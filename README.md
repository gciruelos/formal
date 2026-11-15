# Lean formalizations

One Lake project, one library per formalized work (thesis, paper, book chapter). Each work has
a flat directory of `.lean` files plus a README. The conventions are in [`AGENTS.md`](AGENTS.md); file organization and how gaps and changes are recorded are in [`STYLE.md`](STYLE.md).

```bash
lake build MartinPhd     # one work
lake build                # all of them
```

<!-- BEGIN GENERATED: projects -->

| Project | Work | Lines | Sorry-free theorems | `sorry` | Main results proved | Gaps (high / medium / low) | Axioms (except `sorryAx`) |
|:---|:---|---:|---:|---:|---:|---:|:---|
| [MartinPhd](MartinPhd/README.md) | Fernando Daniel Martin, *Aspectos homológicos de la teoría de especies* (PhD thesis, Universidad de Buenos Aires, 2024) | 28,095 | 1252/1326 | 120 | 3/5 | 26 / 8 / 25 (22 open) | `Classical.choice`, `Quot.sound`, `propext` |
| [ScoccolaPhd](ScoccolaPhd/README.md) | Luis N. Scoccola, *Locally Persistent Categories and Metric Properties of Interleaving Distances* (PhD thesis, Western University, 2020) | 21,636 | 829/829 | 0 | 10/10 | 20 / 7 / 9 (0 open) | `Classical.choice`, `Quot.sound`, `propext` |
| [CiruelosLic](CiruelosLic/README.md) | Gonzalo Ciruelos Rodríguez, *Factorizing Derivations via Intersection Types* (Licenciatura thesis, Universidad de Buenos Aires, 2018) | 13,401 | 714/714 | 0 | 5/5 | 6 / 4 / 9 (0 open) | `Classical.choice`, `Quot.sound`, `propext` |
| [TamaroffPhd](TamaroffPhd/README.md) | Pedro Tamaroff, *Homotopical and effective methods for associative algebras* (PhD thesis, Trinity College Dublin, 2021) | 6,039 | 143/217 | 72 | 1/5 | 13 / 2 / 1 (10 open) | `Classical.choice`, `Quot.sound`, `propext` |

<!-- END GENERATED: projects -->

*Sorry-free theorems* counts user-written theorems that do not reach `sorryAx`. *Main results
proved* counts the headline theorems listed for each work in `works.toml` that are
`sorry`-free. *Gaps* counts the places where the source is defective, as high / medium / low severity:
high = a false or underspecified statement or definition (errors, missing hypotheses), medium =
a wrong or missing proof of a true statement (proof gaps, unproved claims), low = an ambiguity
or typo. *Open* means the Lean declaration carrying the note still depends on `sorry`. *Axioms
(except `sorryAx`)* lists every axiom used by the headline results of the work, including
Lean's standard `propext`, `Classical.choice` and `Quot.sound`.

## Layout of a project

```
lakefile.toml               one [[lean_lib]] per work; shared Mathlib in .lake/packages
works.toml                  [<Lib>] metadata and [[<Lib>.main]] headline theorems per work
<Lib>.lean                  root module: imports every file of the work
<Lib>/README.md             see "The README of a work" below
<Lib>/<Module>.lean         flat: no subdirectories, module MartinPhd.Chapter1Section4
<Lib>/<Lib>.pdf             the source being formalized
scripts/                    stats machinery, vendor_tauceti.sh
vendor/TauCeti/             vendored third-party code (see below); not a work
```

## Vendored code

`vendor/TauCeti/` is a pinned, checksummed copy of the A∞ / homological-transfer part of
[TauCeti](https://github.com/TauCetiProject/TauCeti) (Apache-2.0; `vendor/TauCeti/LICENSE`),
built as the Lake library `TauCeti` (not a formalized work, so it has no `works.toml` entry and
the statistics skip it). It is restored and verified with `scripts/vendor_tauceti.sh`
(`fetch` | `verify` | `update <rev>`); never edit it by hand. Its pin must match this project's
Mathlib revision: TauCeti tracks Mathlib `master`, so `update` to a new upstream revision may
need a Mathlib bump first. Works must not import each other, but may import `TauCeti`.

Libraries are named `<Name>Phd`/`Lic`/`Msc` or `<Author><Yyyy>[<Title>]`; see [`STYLE.md`](STYLE.md).

## The README of a work

Every `<Lib>/README.md` has exactly these parts, in this order. *(generated)* parts are
produced by the script between markers; everything else is written by hand.

1. **Title.** `# <Author initial>. <Surname>, *<Title>*`, then one line with the kind,
   institution, year and links to the PDF and the build command.
2. **One sentence** saying what the work is about, for a reader who has never seen it.
3. **`## Main results`.** A numbered list of the 1–5 most important results, one line each
   (source numbering plus a plain-words statement). They are the `[[<Lib>.main]]` entries of
   `works.toml`, in the same order. Below the list, *(generated)* block `main`: a small table
   with, per result, its Lean name, how many declarations with `sorry` it reaches through its
   statement or proof (including its own declaration), and whether it is proved.
4. **`## The results in brief`.** A short explanation of the main results for a mathematician
   who does not know the area: what the objects are, what each result says, and why it
   matters. Sell the results at a high level and keep the details for the Lean docstrings.
5. **`## Per-file statistics`.** *(generated)* block `stats`: one row per file.
6. **`## Gaps found during formalization`.** *(generated)* block `gaps`: one row per
   `**Gap (<kind>).**` docstring note, sorted by severity (high: the printed statement is false
   or needs an unstated assumption; medium: the proof is wrong, incomplete or missing; low:
   an ambiguity or typo), with its status in Lean.
7. **`## Changes to the source`.** *(generated)* block `changes`: one row per `**Change.**`
   docstring note, a departure due only to Lean's ergonomics (not a source defect, not a
   mathematical choice).

Nothing else goes in the README. Proof sketches, representation choices and other
implementation notes belong in module docstrings (`/-! … -/`) of the files concerned.

## Regenerating the tables

```bash
python3 scripts/update_stats.py               # build every project, rewrite all generated blocks
python3 scripts/update_stats.py MartinPhd    # one work; the index uses cached data for the rest
python3 scripts/update_stats.py --check       # exit 1 if any README is stale
```

The script ([`scripts/update_stats.py`](scripts/update_stats.py)) runs `lake build <Lib>` for each
work, then [`scripts/proof_stats.lean`](scripts/proof_stats.lean) against the project's root
module to read off, from the elaborated environment, which theorems depend on `sorry` and which
axioms the headline results use. Source counts (lines, statements, `sorry` tokens) come from
the `.lean` text. Gaps come from `**Gap (<kind>).**` paragraphs in docstrings (see
`AGENTS.md`), and changes from `**Change.**` paragraphs (definitions in `STYLE.md`, section 5). The script only rewrites text between `<!-- BEGIN GENERATED: … -->` and
`<!-- END GENERATED: … -->` markers. It uses only the Python ≥ 3.11 standard library.
