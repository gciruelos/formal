# Lean formalizations

One Lake project, one library per formalized work (thesis, paper, book chapter). Each work has
a flat directory of `.lean` files plus a README. The conventions are in [`AGENTS.md`](AGENTS.md); file organization and how gaps and changes are recorded are in [`STYLE.md`](STYLE.md).

```bash
lake build MartinPhd     # one work
lake build                # all of them
```

<!-- BEGIN GENERATED: projects -->

| Project | Work | Scope | Lines | Sorry-free theorems | `sorry` | Main results proved | Gaps found |
|:---|:---|:---|---:|---:|---:|---:|---:|
| [MartinPhd](MartinPhd/README.md) | Fernando Daniel Martin, *Aspectos homológicos de la teoría de especies* (PhD thesis, Universidad de Buenos Aires, 2024) | Chapters 1–4 (Chapter 1 proved; Chapters 2–4 outline) | 27,521 | 1249/1314 | 113 | 5/5 | 15 (3 open) |
| [ScoccolaPhd](ScoccolaPhd/README.md) | Luis N. Scoccola, *Locally Persistent Categories and Metric Properties of Interleaving Distances* (PhD thesis, Western University, 2020) | Chapters 2–6 | 17,172 | 656/672 | 15 | 10/10 | 21 (8 open) |
| [CiruelosLic](CiruelosLic/README.md) | Gonzalo Ciruelos Rodríguez, *Factorizing Derivations via Intersection Types* (Licenciatura thesis, Universidad de Buenos Aires, 2018) | Whole thesis, plus the cited orthogonality of β-reduction | 13,280 | 714/714 | 0 | 5/5 | 8 (0 open) |
| [TamaroffPhd](TamaroffPhd/README.md) | Pedro Tamaroff, *Homotopical and effective methods for associative algebras* (PhD thesis, Trinity College Dublin, 2021) | Chapters 2–6 (outline: definitions and statements) | 5,474 | 129/205 | 74 | 1/5 | 3 (1 open) |

<!-- END GENERATED: projects -->

*Sorry-free theorems* counts user-written theorems that do not reach `sorryAx`. *Main results
proved* counts the headline theorems listed for each work in `works.toml` that are
`sorry`-free. *Gaps found* counts the places where the formalization had to correct or complete
the source: errors, proof gaps, missing hypotheses, unproved claims, imprecise statements and
typos. *Open* means the Lean declaration carrying the note still depends on `sorry`.

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
`AGENTS.md`), and changes from `**Change (<where>).**` paragraphs. The script only rewrites text between `<!-- BEGIN GENERATED: … -->` and
`<!-- END GENERATED: … -->` markers. It uses only the Python ≥ 3.11 standard library.
