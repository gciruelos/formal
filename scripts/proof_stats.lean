import «ROOT»
import Lean.Util.Sorry
import Lean.Util.NumObjs
import Lean.Util.ShareCommon

/-!
Measurement tool for `scripts/update_stats.py` (not part of any formalization). The script
replaces `ROOT` with the project's root module and runs this file with `lake env lean`.

For every module of the project it reports
* `theorems`: user-written theorems (they have a source range; generated lemmas do not);
* `sorry_dependent`: those that use `sorryAx`, directly or through other declarations of the
  project (dependencies outside the project, i.e. Mathlib, are assumed sorry-free);
* `direct_sorry`: declarations of any kind whose statement or body contains `sorryAx`,
  reported under their user-facing name (auxiliary `_proof_n` declarations are folded in).
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

structure ModRow where
  theorems : Nat := 0
  dependent : List Name := []
  direct : List Name := []
  maxProof : Nat := 0
  maxProofName : Name := .anonymous
  maxStatement : Nat := 0
  maxStatementName : Name := .anonymous

run_cmd do
  let env ← getEnv
  let root := `«ROOT»
  let isProjMod : Name → Bool := fun m => m == root || root.isPrefixOf m
  let modOf : Name → Option Name := fun n =>
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let inProject : Name → Bool := fun n => (modOf n).any isProjMod
  let mut rows : Std.HashMap Name ModRow := {}
  for m in env.header.moduleNames do
    if isProjMod m then rows := rows.insert m {}
  let mut memo : Std.HashMap Name Bool := {}
  for (n, info) in env.constants.toList do
    let some m := modOf n | continue
    let some row := rows[m]? | continue
    let mut row := row
    if info.getUsedConstantsAsSet.contains ``sorryAx then
      row := { row with direct := userName n :: row.direct }
    if let .thmInfo thm := info then
      -- DAG sizes (hash-consed), over all theorem declarations including generated ones.
      let size ← (ShareCommon.shareCommon' thm.value).numObjs
      let stmt ← (ShareCommon.shareCommon' thm.type).numObjs
      if size > row.maxProof || (size == row.maxProof && n.toString < row.maxProofName.toString) then
        row := { row with maxProof := size, maxProofName := n }
      if stmt > row.maxStatement ||
          (stmt == row.maxStatement && n.toString < row.maxStatementName.toString) then
        row := { row with maxStatement := stmt, maxStatementName := n }
      if !n.isInternalDetail && (← findDeclarationRanges? n).isSome then
        let (b, memo') := (dependsOnSorry env inProject n).run memo
        memo := memo'
        row := { row with theorems := row.theorems + 1,
                          dependent := if b then n :: row.dependent else row.dependent }
    rows := rows.insert m row
  let mods := rows.toList.map fun (m, r) => Json.mkObj [
    ("module", toJson m.toString),
    ("theorems", toJson r.theorems),
    ("sorry_dependent", toJson (r.dependent.map Name.toString)),
    ("direct_sorry", toJson (r.direct.eraseDups.map Name.toString)),
    ("max_proof_dag", toJson r.maxProof),
    ("max_proof_name", toJson r.maxProofName.toString),
    ("max_statement_dag", toJson r.maxStatement),
    ("max_statement_name", toJson r.maxStatementName.toString)]
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
  IO.println ("STATS_JSON\t" ++ (Json.mkObj [("modules", Json.arr mods.toArray),
    ("main", Json.arr main.toArray)]).compress)
