#!/usr/bin/env bash
# Vendors the A∞ / homological-transfer part of TauCeti (https://github.com/TauCetiProject/TauCeti,
# Apache-2.0, same Lean toolchain as this project) into vendor/TauCeti, pinned to one commit with
# a SHA-256 checksum for every file.
#
#   scripts/vendor_tauceti.sh            fetch the pinned files that are missing or modified, and
#                                        verify every checksum (default; same as `fetch`)
#   scripts/vendor_tauceti.sh verify     check the checksums only, no network
#   scripts/vendor_tauceti.sh update [REV]
#                                        resolve REV (default: main) to a commit, download the
#                                        import closure of ROOTS at that commit, and rewrite
#                                        COMMIT and CHECKSUMS below in this file
#
# Nothing under vendor/TauCeti is edited by hand: re-run `fetch` to restore it.
set -euo pipefail

REPO="TauCetiProject/TauCeti"
# Module files whose imports (transitively, within TauCeti.*) are vendored.
ROOTS="TauCeti/Algebra/Homology/AInfinity/Algebra/Transfer/Basic.lean"
# BEGIN COMMIT
COMMIT=d0347706e1153bd2c11e1372849793aa4750d25f
# END COMMIT
# BEGIN CHECKSUMS
CHECKSUMS="
b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1  LICENSE
15861e7f1bec197e306ad287b28b297ba20c38ee23fd7f79921b57a8758a83a6  TauCeti/Algebra/BigOperators/Finset/Range.lean
a83df165de8ebe3b6567453f2b74c59a6448861d903866b70b3687950d943164  TauCeti/Algebra/DirectSum/Internal.lean
f82dd0e70030df1aeb41ebcaf0b9e30ee3813f6290098d39cc1f76d534b8f5e8  TauCeti/Algebra/Homology/AInfinity/Algebra.lean
368a0f4c9672a725b7cdcf60f97bbabb0e76945bf529e60a6ee775acb9cc69b2  TauCeti/Algebra/Homology/AInfinity/Algebra/BarDifferential.lean
e732d4a81f31ef2287fd7775a67d24192391798f56f4056ff085fb88332537e1  TauCeti/Algebra/Homology/AInfinity/Algebra/Cohomology.lean
9f3a87ad176411cbd2711d467ca513e84b9021a00c52d304b4ab4245a6293060  TauCeti/Algebra/Homology/AInfinity/Algebra/DG.lean
594d0f5327f76662af225f5d7c0d445c0a643726e513c6324db074f1d5df0e13  TauCeti/Algebra/Homology/AInfinity/Algebra/Hom/Basic.lean
601c25f8ff2477487b93a7b753ac7baecfeadd2789c647e15d6e36da0eefc202  TauCeti/Algebra/Homology/AInfinity/Algebra/Hom/Cohomology.lean
aee921237a0ad9144b28142c573976372eee0534fc7373a3e83bd7df28edb7cc  TauCeti/Algebra/Homology/AInfinity/Algebra/Hom/Component.lean
bf30b9d18f57e6354a7bb92ce9c4fd152b0ca49a3420a4e76c8ef7b4caec8c4b  TauCeti/Algebra/Homology/AInfinity/Algebra/Hom/Iso.lean
27cb30811145c0a537da68a438f90ff0bdd35479274bf7c0e816ef385a8e9b40  TauCeti/Algebra/Homology/AInfinity/Algebra/Hom/Strict.lean
9f53ae7713316f69b775844abacb0dc332bc47d3193b720af82ebf49549fd659  TauCeti/Algebra/Homology/AInfinity/Algebra/Minimal.lean
3e9ff26886056bdb686a9cb73f39194bbd59c8a00787f59ea42a9cce2c14283f  TauCeti/Algebra/Homology/AInfinity/Algebra/Transfer/Basic.lean
d2e5bfc381378b6bf902706a27eb09b0a686c44246fb06c4bf93ad8f29686be1  TauCeti/Algebra/Homology/AInfinity/Algebra/Transfer/Perturbation.lean
7c149d9e15f23372052c50f5fabb1c774d268706d9a9a0a1859e72f1739b9c0d  TauCeti/Algebra/Homology/AInfinity/Algebra/Unit.lean
e3beec5c53002b310ca71501a23719cd50b167630ad57babc25be97458e51d2e  TauCeti/Algebra/Homology/AInfinity/Coderivation.lean
ddf545e79ed96c998a69710309b6bc23b7777f6860be3eb857d7c531085dc442  TauCeti/Algebra/Homology/AInfinity/Stasheff.lean
572400f268407f228c21adf5244299b5793ef8cf3206ce1c48063c92a4ce58d5  TauCeti/Algebra/Homology/Contraction/Linear/Basic.lean
965075cd280e60e6ebf423f433aaacf9f344d7905f76bbb8dadfdcbcf208af6d  TauCeti/Algebra/Homology/Contraction/Perturbation.lean
f537f970d68af303b8634cfdb77a8c1e8e9a5213a8013ec711fd05d230e6fc55  TauCeti/Algebra/Homology/Contraction/TensorTrick.lean
1426eaa775499bd5dc37ed5020c760dfece1ac4d715a9d912a35c25e9d9db64f  TauCeti/Algebra/Homology/Contraction/TensorTrick/Filtration.lean
0355eaa7085ed1ae4c9f1e4c9864575e3e5576cceada221baeaacbb49ffd4d3a  TauCeti/Algebra/Homology/Contraction/TensorTrick/Perturbation/Basic.lean
134d84d05021c73e0fbf08957086733c1e799bcb352abf164093171b42075a7f  TauCeti/Algebra/Homology/DG/Algebra/Defs.lean
322a01f06db61b7e6084007ffe2cfad95af6dc4b64ca8107b9617b9eac5db318  TauCeti/Algebra/Homology/DG/Algebra/Hom/Basic.lean
10f0b49db55d7ebe0c619f83d191f1e022d6f4d4aa6a3d0b1b9b2711da8a0621  TauCeti/Algebra/Homology/DG/Algebra/Hom/NonUnital.lean
653e3472d9465d8db7ca531e09b77b16a53ce1b56f82510864d498450743833d  TauCeti/Algebra/Homology/HomologicalComplex/Basic.lean
eaa919c3cb5a213e3aeaf725396e589145d58a31fd9366219bb150fae0c5b54b  TauCeti/Algebra/Homology/ModuleCat/Basic.lean
0efc89a8a169069dbb44931047bc3454cd26e66bc0924e91ef847ce2b277b442  TauCeti/Algebra/Homology/SquareZero.lean
9bd4b14ddb7be7a32f44a2a4c7cc1c25e13efe26360f23777f31e33241f4aa83  TauCeti/Algebra/Module/GradedModule/Internal.lean
0a3e7df7b692722a737a45ac8495f0836fdeef5f31935ea06ed5d2488d863a48  TauCeti/Algebra/Module/GradedModule/Multilinear/Basic.lean
9aacca5cc639ce65ae8ee4fa04701a4a97fa18213765058c7596be6f99a1ea13  TauCeti/Algebra/Module/GradedModule/Quotient.lean
71285bb5b11966ce951b7eddc620a0f52b7793747872d5892ffd4a21bebdf9bd  TauCeti/Algebra/Module/GradedModule/Shift.lean
9c4f9b8b86d227d5d3a1e55c644055bc0c6426f6c01798b6c7d8db3d012484d5  TauCeti/Algebra/Module/GradedModule/TensorProduct/Basic.lean
3db229dcadd750ea2e53c6466341adcb24a9df30401b9264e5b314d058c155e8  TauCeti/Algebra/Module/GradedModule/Trivial.lean
5439574395ce3b484f137c4d223283ee938b8e0752fa20d7d90ac18304e2b26c  TauCeti/Algebra/Module/NatInt.lean
9487e0488e93ea94904ab0bb676c0dcc39df9b278013175836ccb57d87ace3f6  TauCeti/Algebra/Module/Submodule/Finite.lean
a8c0b9b031e3340fbf67963f4e72fa2cdff8a5757684899e58f7a3ad1c053ed3  TauCeti/Algebra/Module/Submodule/Ker.lean
b6c7c6ffe5ec61faada1cccb4dd88aab316ed4cc4c836dd560a9cc336d7290d3  TauCeti/Algebra/Ring/NegOnePow.lean
638079ce97781fd5b61e466e02767e80a1c60b48708bd8f18e61c7a2b29ab73f  TauCeti/Algebra/Ring/Units.lean
c3ef2d0e039dcbd105dffb074d6203d9416ef4709723142be6b892c29f5aee54  TauCeti/LinearAlgebra/End/LocallyNilpotent.lean
6c7093f2e3bbad95668cfcf6ff54e12b5bbc88b045dbad0710a107ef1d8361bc  TauCeti/LinearAlgebra/Graded/Insertion.lean
c41e294634274fcf04abf82e3e01c9274a5af1410e700abd6b7ed191ee6ca425  TauCeti/LinearAlgebra/Graded/LinearMap.lean
b83f962f4ac853b9780aac8b23549598849c941f37ee4f1ce54b73c121bc7981  TauCeti/LinearAlgebra/Graded/Multilinear.lean
d4ee726a5c603dafb6ec3c4f54de5bb4c267507efab0355a21b7d958289c155e  TauCeti/LinearAlgebra/Graded/Shift.lean
3346c11b2751377638fa4bd562f1519efb6852067b66188856d1679e9bd05626  TauCeti/LinearAlgebra/PiTensorProduct/Map.lean
5f230229432eeb96fff5e7144eb9a4f7bac5d6912405f2ce30b80f5a2dc60633  TauCeti/LinearAlgebra/Quotient/Prod.lean
db28a20e8b5ae709492a3c8754cb45a702d3469a2ede6413d81d5d3f6889b098  TauCeti/LinearAlgebra/TensorCoalgebra/Basic.lean
cc046136c19c8606f8efeea6d1290af6aaa199effdd036929e29fd533480be07  TauCeti/LinearAlgebra/TensorCoalgebra/Brace.lean
a96878a6b1110bea9ab5ad94ff334c004baa4054923321a1dae656d3c7e50537  TauCeti/LinearAlgebra/TensorCoalgebra/CoalgHom.lean
2d6dfe9151271f02987b51e5b5e7d3828a6136b9ad2370c4b5f2e94eeacb68c7  TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean
b2a467bf3e4b16901a013d329800df9e84ed1502673f68a9fe900699c17c099d  TauCeti/LinearAlgebra/TensorCoalgebra/Filtration.lean
15cb9422ad0def70b0300d3f52b5d03b663d6e2251fcec81ec262062ff1265db  TauCeti/LinearAlgebra/TensorCoalgebra/Filtration/GradedCoderivation.lean
1a97191b55347fb2914a523a2c7facec5ef37b91365d1e627887aedc5f1db28d  TauCeti/LinearAlgebra/TensorCoalgebra/GradedCoalgHom.lean
ed1e2b5d66f9ab1c8273d5e9b9edf01bf8f5724e823206eca068787825719eab  TauCeti/LinearAlgebra/TensorCoalgebra/GradedCoderivation.lean
c99482698e5a44a5be9bbc7d6e815af2f1ff0a214f51ab4b5a9cec98821375cb  TauCeti/LinearAlgebra/TensorCoalgebra/OddSquare.lean
34e5122105f1a90d3d0abdaacc23acba2372db8d60fca3d13a692135601d1a78  TauCeti/LinearAlgebra/TensorCoalgebra/Primitives.lean
a8b4d37625cf150f66f58fd61b791b050549f10599bbed40d29e934ec9655287  TauCeti/LinearAlgebra/TensorCoalgebra/Splice.lean
b0147858539dfbc80c254b03dda11195a8361714bedc282fd60e10cbf64c3f70  TauCeti/LinearAlgebra/TensorCoalgebra/TaylorComponent.lean
f0cc36fc7fc2d861d006660a49b469b08eec4110b0bb970e24bca9dec586d62b  TauCeti/LinearAlgebra/TensorPower/Basic.lean
18208780c195a51515dbfe84ec404d6689c4d2f85c5c60e7034e13c1b408c2f9  TauCeti/LinearAlgebra/TensorProduct/Basic.lean
994acafc3a7cfac1b3a0a3de09055aca9722dd78f919761674053ea1354036b7  TauCeti/LinearAlgebra/TensorProduct/Decomposition.lean
50ffa23a6f4ab3f775ac4f12cb85c9deb1122d374e0ebf26c03ffea637bd908f  TauCeti/LinearAlgebra/TensorProduct/Submodule.lean
3e93b2db178a1ec7405805e8c44586d3f72ea96a56160499f13ada61cde5983f  TauCeti/Order/CompactlyGenerated.lean
d666232904d4380c67c027a778855ba91354e91135c6f20fc00b5722766ecc0b  TauCeti/RingTheory/GradedAlgebra/Trivial.lean
"
# END CHECKSUMS

cd "$(dirname "$0")/.."
DEST="vendor/TauCeti"
RAW="https://raw.githubusercontent.com/$REPO"
SELF="scripts/$(basename "$0")"
mode="${1:-fetch}"

sha() { sha256sum "$1" | cut -d' ' -f1; }

verify() {
  local bad=0 sum path
  while read -r sum path; do
    [ -n "${path:-}" ] || continue
    if [ ! -f "$DEST/$path" ] || [ "$(sha "$DEST/$path")" != "$sum" ]; then
      echo "MISMATCH/MISSING: $path" >&2; bad=1
    fi
  done <<< "$CHECKSUMS"
  return $bad
}

fetch_one() { # fetch_one COMMIT PATH SHA: download and check the checksum
  mkdir -p "$DEST/$(dirname "$2")"
  curl -fsSL "$RAW/$1/$2" -o "$DEST/$2"
  [ "$(sha "$DEST/$2")" = "$3" ] || { echo "checksum mismatch: $2" >&2; return 1; }
}

case "$mode" in
  verify)
    verify && echo "ok: all checksums match ($COMMIT)" ;;
  fetch)
    while read -r sum path; do
      [ -n "${path:-}" ] || continue
      if [ ! -f "$DEST/$path" ] || [ "$(sha "$DEST/$path")" != "$sum" ]; then
        echo "fetching $path"; fetch_one "$COMMIT" "$path" "$sum"
      fi
    done <<< "$CHECKSUMS"
    verify && echo "ok: all checksums match ($COMMIT)" ;;
  update)
    rev="${2:-main}"
    new=$(curl -fsSL "https://api.github.com/repos/$REPO/commits/$rev" |
      python3 -I -c 'import json,sys;print(json.load(sys.stdin)["sha"])')
    echo "resolving import closure at $new"
    ROOTS="$ROOTS" NEW="$new" DEST="$DEST" RAW="$RAW" SELF="$SELF" python3 -I - <<'PY'
import hashlib, os, re, urllib.request
roots, new, dest, raw, self_ = (os.environ[k] for k in ("ROOTS", "NEW", "DEST", "RAW", "SELF"))
imp = re.compile(r"^(?:public |meta )*import\s+(TauCeti(?:\.\w+)*)", re.M)
todo, seen, files = roots.split(), set(), {}
while todo:
    p = todo.pop()
    if p in seen: continue
    seen.add(p)
    data = urllib.request.urlopen(f"{raw}/{new}/{p}").read()
    os.makedirs(os.path.dirname(f"{dest}/{p}"), exist_ok=True)
    open(f"{dest}/{p}", "wb").write(data)
    files[p] = hashlib.sha256(data).hexdigest()
    todo += [m.replace(".", "/") + ".lean" for m in imp.findall(data.decode())]
lic = urllib.request.urlopen(f"{raw}/{new}/LICENSE").read()
open(f"{dest}/LICENSE", "wb").write(lic)
files["LICENSE"] = hashlib.sha256(lic).hexdigest()
block = 'CHECKSUMS="\n' + "".join(f"{h}  {p}\n" for p, h in sorted(files.items())) + '"\n'
s = open(self_).read()
s = re.sub(r"(# BEGIN COMMIT\n).*?(# END COMMIT)", lambda m: f"{m[1]}COMMIT={new}\n{m[2]}", s, flags=re.S)
s = re.sub(r"(# BEGIN CHECKSUMS\n).*?(# END CHECKSUMS)", lambda m: m[1] + block + m[2], s, flags=re.S)
open(self_ + ".tmp", "w").write(s)
os.chmod(self_ + ".tmp", 0o755)
os.replace(self_ + ".tmp", self_)  # new inode: the running bash keeps reading the old file
print(f"vendored {len(files)} files at {new}")
PY
    ;;
  *) echo "usage: $0 [fetch|verify|update [REV]]" >&2; exit 2 ;;
esac
