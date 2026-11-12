import «ROOT»
import Lean.Util.Sorry
import Lean.Util.NumObjs
import Lean.Util.ShareCommon
import Lean.AutoDecl

/-!
Measurement tool for `scripts/update_stats.py` (not part of any formalization). The script
replaces `ROOT` with the project's root module and runs this file with `lake env lean`.

For every module of the project it reports
* `theorems`: user-written theorems (matching source identifiers, excluding projections
  and Lean auto declarations);
* `sorry_dependent`: those that use `sorryAx`, directly or through other declarations of the
  project (dependencies outside the project, i.e. Mathlib, are assumed sorry-free);
* `direct_sorry`: declarations of any kind whose statement or body contains `sorryAx`,
  reported under their user-facing name (auxiliary `_proof_n` declarations are folded in).
* `max_ratio`: the largest absolute proof-to-vocabulary dependency DAG size ratio among sorry-free
  user-written theorems (including dependencies from Mathlib and Lean).
It also reports, for each name passed in `MAIN`, whether it depends on `sorry`, its axioms, and
the declarations with a direct `sorry` that it reaches (`sorry_leaves`).
-/

open Lean Elab Command

set_option maxHeartbeats 0

/-- Names listed under `[[<Lib>.main]]` in `works.toml`; filled in by the script. -/
def mainNames : List Name := [MAIN]

/-- Fold auxiliary declarations (`foo._proof_1`, `foo.match_2`, …) into `foo`. -/
partial def userName : Name → Name
  | n@(.str p s) =>
    if s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_"
    then userName p else n
  | .num p _ => userName p
  | n => n

partial def dependsOnSorry (env : Environment) (inProject : Name → Bool) :
    Name → StateM (Std.HashMap Name Bool) Bool := fun n => do
  if let some b := (← get)[n]? then return b
  modify (·.insert n false)  -- cycle guard
  let some info := env.find? n | return false
  let b ← (do
    for c in info.getUsedConstantsAsSet do
      if c == ``sorryAx then return true
      if inProject c && (← dependsOnSorry env inProject c) then return true
    return false)
  modify (·.insert n b)
  return b

/-- The project declarations with a direct `sorry` that `n` reaches. -/
partial def sorryLeaves (env : Environment) (inProject : Name → Bool) (n : Name) :
    StateM (Std.HashSet Name × List Name) Unit := do
  if (← get).1.contains n then return
  modify fun (seen, acc) => (seen.insert n, acc)
  let some info := env.find? n | return
  let used := info.getUsedConstantsAsSet
  if used.contains ``sorryAx then modify fun (seen, acc) => (seen, userName n :: acc)
  for c in used do
    if inProject c then sorryLeaves env inProject c

/-- Source ranges alone also admit generated fields and constructor lemmas. Keep private
user theorems, but reject projections and Lean's recognized automatic declarations. -/
def isUserTheorem (env : Environment) (n : Name) : CoreM Bool := do
  let user := privateToUserName n
  if user.isInternalDetail || env.isProjectionFn n then return false
  return !(← isAutoDeclOrPrivate_Internal user)

/-- Attribute-generated theorems can inherit the original theorem's source range. Require
that the identifier selected in the source is a suffix of the actual user-facing name.
Parsing the identifier handles qualified and quoted names without string heuristics. -/
def sourceNameMatches (env : Environment) (n : Name) (text : String) : Bool :=
  match Parser.runParserCategory env `term text with
  | .ok stx => stx.isIdent && stx.getId.isSuffixOf (privateToUserName n)
  | .error _ => false

def selectionMatches (env : Environment) (n : Name) (ranges : DeclarationRanges)
    (lines : Array String) : Bool := Id.run do
  let r := ranges.selectionRange
  if r.pos.line != r.endPos.line then return false
  let some line := lines[r.pos.line - 1]? | return false
  let text := String.ofList ((line.toList.drop r.pos.column).take (r.endPos.column - r.pos.column))
  return sourceNameMatches env n text

structure DagSizes where
  proof : Nat
  statement : Nat
  deriving ToJson

def theoremDagSizes (thm : TheoremVal) : IO DagSizes := do
  return ⟨← (ShareCommon.shareCommon' thm.value).numObjs,
          ← (ShareCommon.shareCommon' thm.type).numObjs⟩

/-- A declaration's contribution to the absolute dependency graph. Sizes are hash-consed
within each expression; distinct declarations are counted separately, once per closure.
Vocabulary expansion includes theorem types but never their proofs. Inductive constructors
and recursor computation rules are included, rather than treating their names as free. -/
structure DependencyNode where
  size : Nat
  deps : Array Name
  types : Nat
  proofs : Nat
  definitions : Nat
  rules : Nat

abbrev DependencyCache := Std.HashMap (Name × Bool) DependencyNode

def dependencyNode (env : Environment) (n : Name) (proof : Bool) :
    StateT DependencyCache IO DependencyNode := do
  if let some node := (← get)[(n, proof)]? then return node
  let some info := env.find? n | throw <| IO.userError s!"Unknown dependency: {n}"
  let typeSize ← (ShareCommon.shareCommon' info.type).numObjs
  let mut proofSize := 0
  let mut definitionSize := 0
  let mut ruleSize := 0
  let mut expressions := #[info.type]
  let includeBody := proof || !(match info with | .thmInfo _ => true | _ => false)
  if includeBody then
    if let some value := info.value? (allowOpaque := true) then
      expressions := expressions.push value
      let bodySize ← (ShareCommon.shareCommon' value).numObjs
      match info with
      | .thmInfo _ => proofSize := bodySize
      | _ => definitionSize := bodySize
  let mut deps := #[]
  match info with
  | .inductInfo v => deps := deps ++ v.ctors.toArray
  | .recInfo v =>
    deps := deps ++ v.all.toArray
    for rule in v.rules do
      expressions := expressions.push rule.rhs
      ruleSize := ruleSize + (← (ShareCommon.shareCommon' rule.rhs).numObjs)
  | _ => pure ()
  for e in expressions do
    deps := deps ++ e.getUsedConstants
  let node := { size := typeSize + proofSize + definitionSize + ruleSize, deps,
                types := typeSize, proofs := proofSize, definitions := definitionSize,
                rules := ruleSize : DependencyNode }
  modify (·.insert (n, proof) node)
  return node

/-- Expand all named dependencies, with no library boundary. Axioms are terminal:
their types count, but they supply no proof bodies. Cycles and shared dependencies
are handled by visiting each declaration once. -/
def absoluteSize (env : Environment) (root : Expr) (proof : Bool) :
    StateT DependencyCache IO Nat := do
  let mut total ← (ShareCommon.shareCommon' root).numObjs
  let mut pending := root.getUsedConstants
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let node ← dependencyNode env n proof
    total := total + node.size
    pending := pending ++ node.deps
  return total

def absoluteTheoremSizes (env : Environment) (thm : TheoremVal) :
    StateT DependencyCache IO DagSizes := do
  return ⟨← absoluteSize env thm.value true, ← absoluteSize env thm.type false⟩

structure Contributor where
  name : String
  module : String
  size : Nat
  deriving ToJson

/-- Disjoint accounting of expression sizes. Top contributors are individual declarations'
own costs, not overlapping transitive subtotals. Other packages are kept separate from Lean. -/
structure Attribution where
  project : Nat := 0
  mathlib : Nat := 0
  lean : Nat := 0
  other : Nat := 0
  types : Nat := 0
  proofs : Nat := 0
  definitions : Nat := 0
  rules : Nat := 0
  top : Array Contributor := #[]
  deriving ToJson

def declarationModule (env : Environment) (n : Name) : Name :=
  ((env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!).getD .anonymous

def addContribution (a : Attribution) (root module : Name) (c : Contributor)
    (types proofs definitions rules : Nat) : Attribution := Id.run do
  let mut a := { a with types := a.types + types, proofs := a.proofs + proofs, definitions := a.definitions + definitions, rules := a.rules + rules }
  if root == module || root.isPrefixOf module then
    a := { a with project := a.project + c.size }
  else if module == `Mathlib || (`Mathlib).isPrefixOf module then
    a := { a with mathlib := a.mathlib + c.size }
  else if [`Init, `Lean, `Std, `Lake].any (fun n => n == module || n.isPrefixOf module) then
    a := { a with lean := a.lean + c.size }
  else
    a := { a with other := a.other + c.size }
  let top := (a.top.push c).qsort fun x y =>
    x.size > y.size || (x.size == y.size && x.name < y.name)
  return { a with top := top.extract 0 3 }

def absoluteAttribution (env : Environment) (project target : Name) (root : Expr)
    (proof : Bool) : StateT DependencyCache IO Attribution := do
  let rootSize ← (ShareCommon.shareCommon' root).numObjs
  let mut a := addContribution {} project project
    ⟨target.toString ++ (if proof then " (proof)" else " (statement)"),
      (declarationModule env target).toString, rootSize⟩
    (if proof then 0 else rootSize) (if proof then rootSize else 0) 0 0
  let mut pending := root.getUsedConstants
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let node ← dependencyNode env n proof
    let module := declarationModule env n
    a := addContribution a project module ⟨n.toString, module.toString, node.size⟩
      node.types node.proofs node.definitions node.rules
    pending := pending ++ node.deps
  return a

structure ModRow where
  theorems : Nat := 0
  dependent : List Name := []
  direct : List Name := []
  maxProof : Nat := 0
  maxProofName : Name := .anonymous
  maxStatement : Nat := 0
  maxStatementName : Name := .anonymous
  maxRatio : DagSizes := ⟨0, 1⟩
  maxRatioName : Name := .anonymous
  maxRatioLine : Nat := 0

run_cmd do
  let env ← getEnv
  let root := `«ROOT»
  let isProjMod : Name → Bool := fun m => m == root || root.isPrefixOf m
  let modOf : Name → Option Name := fun n =>
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let inProject : Name → Bool := fun n => (modOf n).any isProjMod
  let mut sourceLines : Std.HashMap Name (Array String) := {}
  let mut rows : Std.HashMap Name ModRow := {}
  for m in env.header.moduleNames do
    if isProjMod m then
      rows := rows.insert m {}
      let source ← IO.FS.readFile (m.toString.replace "." "/" ++ ".lean")
      sourceLines := sourceLines.insert m (source.splitOn "\n").toArray
  let mut memo : Std.HashMap Name Bool := {}
  let mut dependencyCache : DependencyCache := {}
  for (n, info) in env.constants.toList do
    let some m := modOf n | continue
    let some row := rows[m]? | continue
    let mut row := row
    if info.getUsedConstantsAsSet.contains ``sorryAx then
      row := { row with direct := userName n :: row.direct }
    if let .thmInfo thm := info then
      -- DAG sizes (hash-consed), over all theorem declarations including generated ones.
      let sizes ← theoremDagSizes thm
      let size := sizes.proof
      let stmt := sizes.statement
      if size > row.maxProof || (size == row.maxProof && n.toString < row.maxProofName.toString) then
        row := { row with maxProof := size, maxProofName := n }
      if stmt > row.maxStatement ||
          (stmt == row.maxStatement && n.toString < row.maxStatementName.toString) then
        row := { row with maxStatement := stmt, maxStatementName := n }
      if let (false, some ranges) := (!(← liftCoreM (isUserTheorem env n)), ← findDeclarationRanges? n) then
        if !selectionMatches env n ranges (sourceLines[m]!) then
          rows := rows.insert m row
          continue
        let (b, memo') := (dependsOnSorry env inProject n).run memo
        memo := memo'
        row := { row with theorems := row.theorems + 1,
                          dependent := if b then n :: row.dependent else row.dependent }
        if b then
          rows := rows.insert m row
          continue
        let (absolute, cache') ← (absoluteTheoremSizes env thm).run dependencyCache
        dependencyCache := cache'
        let lhs := absolute.proof * row.maxRatio.statement
        let rhs := row.maxRatio.proof * absolute.statement
        if (lhs > rhs || (lhs == rhs && n.toString < row.maxRatioName.toString)) then
          row := { row with maxRatio := absolute, maxRatioName := n,
                            maxRatioLine := ranges.selectionRange.pos.line }
    rows := rows.insert m row
  let mut mods : Array Json := #[]
  for (m, r) in rows.toList do
    let mut attribution := Json.null
    if let some (.thmInfo thm) := env.find? r.maxRatioName then
      let (proof, cache') ← (absoluteAttribution env root r.maxRatioName thm.value true).run dependencyCache
      let (statement, cache'') ← (absoluteAttribution env root r.maxRatioName thm.type false).run cache'
      dependencyCache := cache''
      attribution := Json.mkObj [("proof", toJson proof), ("statement", toJson statement)]
    mods := mods.push <| Json.mkObj [
    ("module", toJson m.toString),
    ("theorems", toJson r.theorems),
    ("sorry_dependent", toJson (r.dependent.map Name.toString)),
    ("direct_sorry", toJson (r.direct.eraseDups.map Name.toString)),
    ("max_proof_dag", toJson r.maxProof),
    ("max_proof_name", toJson r.maxProofName.toString),
    ("max_statement_dag", toJson r.maxStatement),
    ("max_statement_name", toJson r.maxStatementName.toString),
    ("max_ratio", toJson r.maxRatio),
    ("max_ratio_name", toJson r.maxRatioName.toString),
    ("max_ratio_line", toJson r.maxRatioLine),
    ("max_ratio_attribution", attribution)]
  let mut main : List Json := []
  for n in mainNames do
    if env.contains n then
      let (b, memo') := (dependsOnSorry env inProject n).run memo
      memo := memo'
      let axs ← liftCoreM (collectAxioms (m := CoreM) n)
      let ((), (_, leaves)) := (sorryLeaves env inProject n).run ({}, [])
      main := main ++ [Json.mkObj [("name", toJson n.toString), ("found", toJson true),
        ("sorry", toJson b), ("axioms", toJson (axs.toList.map Name.toString)),
        ("sorry_leaves", toJson (leaves.eraseDups.map Name.toString))]]
    else
      main := main ++ [Json.mkObj [("name", toJson n.toString), ("found", toJson false)]]
  IO.println ("STATS_JSON\t" ++ (Json.mkObj [("metric_version", toJson (3 : Nat)), ("modules", Json.arr mods),
    ("main", Json.arr main.toArray)]).compress)
