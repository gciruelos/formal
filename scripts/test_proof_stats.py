#!/usr/bin/env python3
"""Check dependency accounting against small Lean declarations.

Run from the project root: python3 scripts/test_proof_stats.py
"""
import copy
import json
from pathlib import Path
import subprocess
import tempfile

import update_stats as stats

ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = ROOT / "scripts/proof_stats.lean"
CHECKS = r"""
namespace MetricCheck
inductive Vocabulary where
  | first
  | second (n : Nat)
structure Record where
  witness : True
private theorem privateHelper : True := True.intro
theorem «λ lemma» : True := True.intro
def vocabulary : Nat := 37
theorem helper : vocabulary = 37 := rfl
theorem wrapper : vocabulary = 37 := helper
axiom assumption : vocabulary = 37
end MetricCheck
run_cmd do
  let env ← getEnv
  let some (.thmInfo helper) := env.find? ``MetricCheck.helper | throwError "missing helper"
  let some (.thmInfo wrapper) := env.find? ``MetricCheck.wrapper | throwError "missing wrapper"
  unless ← liftCoreM (isUserTheorem env ``MetricCheck.helper) do
    throwError "explicit theorem excluded"
  unless ← liftCoreM (isUserTheorem env ``MetricCheck.privateHelper) do
    throwError "private theorem excluded"
  for n in [``MetricCheck.Record.witness, ``MetricCheck.Vocabulary.second.injEq,
      ``MetricCheck.Vocabulary.noConfusion] do
    if ← liftCoreM (isUserTheorem env n) then
      throwError "generated declaration admitted: {n}"
  unless sourceNameMatches env ``MetricCheck.helper "helper" do
    throwError "source theorem name rejected"
  unless sourceNameMatches env ``MetricCheck.privateHelper "privateHelper" do
    throwError "private source name rejected"
  unless sourceNameMatches env `MetricCheck.«λ lemma» "«λ lemma»" do
    throwError "quoted Unicode name rejected"
  if sourceNameMatches env `MetricCheck.helper_iff "helper" then
    throwError "attribute-generated name admitted"
  let lines := ((← getFileMap).source.splitOn "\n").toArray
  for n in [``MetricCheck.helper, ``MetricCheck.privateHelper, ``MetricCheck.«λ lemma»] do
    let some ranges ← findDeclarationRanges? n | throwError "source range missing"
    unless selectionMatches env n ranges lines do
      throwError "source selection rejected: {n}"
    if selectionMatches env (n ++ `generated_iff) ranges lines then
      throwError "generated theorem inherited a candidate source range"
  let ((), _) ← (do
    let a ← absoluteTheoremSizes env helper
    let b ← absoluteTheoremSizes env wrapper
    unless a.statement == b.statement do throw <| IO.userError "statement mismatch"
    unless b.proof > a.proof do throw <| IO.userError "helper proof not expanded"
    for (root, proof, expected) in [(helper.value, true, a.proof),
        (helper.type, false, a.statement)] do
      let attribution ← absoluteAttribution env `MetricCheck ``MetricCheck.helper root proof
      unless attribution.project + attribution.mathlib + attribution.lean + attribution.other == expected do
        throw <| IO.userError "origin attribution does not sum to size"
      unless attribution.types + attribution.proofs + attribution.definitions + attribution.rules == expected do
        throw <| IO.userError "component attribution does not sum to size"
      IO.println ("ATTRIBUTION_JSON\t" ++ (Json.mkObj [
        ("side", toJson (if proof then "proof" else "statement")),
        ("size", toJson expected), ("attribution", toJson attribution)]).compress)
      unless attribution.top.size == 3 do throw <| IO.userError "top contributors missing"
      if !proof && attribution.proofs != 0 then
        throw <| IO.userError "vocabulary charged for theorem proofs"
    let vocabulary ← dependencyNode env ``MetricCheck.vocabulary false
    unless vocabulary.deps.contains ``OfNat.ofNat do throw <| IO.userError "definition body missing"
    let inductiveNode ← dependencyNode env ``MetricCheck.Vocabulary false
    unless inductiveNode.deps.contains ``MetricCheck.Vocabulary.first &&
        inductiveNode.deps.contains ``MetricCheck.Vocabulary.second do
      throw <| IO.userError "inductive constructors missing"
    let recursorNode ← dependencyNode env ``MetricCheck.Vocabulary.rec false
    let some (.recInfo recursor) := env.find? ``MetricCheck.Vocabulary.rec
      | throw <| IO.userError "missing recursor"
    let recursorTypeSize ← (ShareCommon.shareCommon' recursor.type).numObjs
    unless recursorNode.size > recursorTypeSize do
      throw <| IO.userError "recursor rules missing"
    let ax ← dependencyNode env ``MetricCheck.assumption true
    let axType ← dependencyNode env ``MetricCheck.assumption false
    unless ax.size == axType.size do throw <| IO.userError "axiom acquired a proof"
    let hProof ← dependencyNode env ``MetricCheck.helper true
    let hType ← dependencyNode env ``MetricCheck.helper false
    unless hProof.size > hType.size do throw <| IO.userError "proof/vocabulary distinction lost"
    let root := Lean.mkApp (Lean.mkConst ``MetricCheck.helper) (Lean.mkConst ``MetricCheck.helper)
    let once ← absoluteSize env (Lean.mkConst ``MetricCheck.helper) true
    let twice ← absoluteSize env root true
    let baseOnce ← (ShareCommon.shareCommon' (Lean.mkConst ``MetricCheck.helper)).numObjs
    let baseTwice ← (ShareCommon.shareCommon' root).numObjs
    unless twice - baseTwice == once - baseOnce do
      throw <| IO.userError "shared dependency counted twice"
    IO.println "Absolute metric checks passed"
    ).run ({} : DependencyCache)
"""


def main():
    source = TEMPLATE.read_text().replace("import «ROOT»", "import Lean")
    source = source.replace("«ROOT»", "MetricCheck").replace("[MAIN]", "[]")
    source = source.replace("structure ModRow where", CHECKS + "\nstructure ModRow where")
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", dir=ROOT / ".lake") as f:
        f.write(source)
        f.flush()
        result = subprocess.run(["lake", "env", "lean", f.name], cwd=ROOT,
                                text=True, capture_output=True)
        if result.returncode:
            print(result.stdout + result.stderr)
            result.check_returncode()
    payloads = [json.loads(line.split("\t", 1)[1]) for line in result.stdout.splitlines()
                if line.startswith("ATTRIBUTION_JSON\t")]
    assert len(payloads) == 2
    module = {"module": "MetricCheck.Example", "max_ratio_name": "MetricCheck.helper",
              "max_ratio_line": 1, "max_ratio": {p["side"]: p["size"] for p in payloads},
              "max_ratio_attribution": {p["side"]: p["attribution"] for p in payloads}}
    data = {"metric_version": stats.METRIC_VERSION, "modules": [module]}
    stats.validate_measurement(data)
    invalid = copy.deepcopy(data)
    invalid["modules"][0]["max_ratio_attribution"]["proof"]["project"] += 1
    try:
        stats.validate_measurement(invalid)
    except RuntimeError:
        pass
    else:
        raise AssertionError("inconsistent attribution accepted")
    old = copy.deepcopy(data)
    old["metric_version"] = stats.METRIC_VERSION - 1
    previous_root = stats.LEAN_ROOT
    with tempfile.TemporaryDirectory() as scratch:
        stats.LEAN_ROOT = Path(scratch)
        try:
            (stats.LEAN_ROOT / ".lake").mkdir()
            (stats.LEAN_ROOT / ".lake/stats_MetricCheck.json").write_text(json.dumps(old))
            assert stats.cached_stats(stats.Project("MetricCheck", {})) is None
        finally:
            stats.LEAN_ROOT = previous_root
    project = stats.Project("MetricCheck", {"namespace": "MetricCheck"},
                            [ROOT / "MetricCheck/Example.lean"])
    cell = stats.dependency_ratio_cell(module, "Example.lean", project)
    assert cell == "[<code>helper</code>](Example.lean#L1)"
    print("Absolute metric, candidate selection, attribution and link rendering checks passed")


if __name__ == "__main__":
    main()
