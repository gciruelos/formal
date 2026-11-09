# Style of a formalization

How the Lean files of a work are organized and how departures from the source are recorded.
The three passes and delegation are in [`AGENTS.md`](AGENTS.md).

## 1. Follow the structure of the reference work

* Files, sections and declarations follow the order of the source. A reader holding the PDF
  should be able to find any result by its number.
* Every declaration that formalizes something in the source says so in its docstring, starting
  with the label in bold: `/-- **Theorem 1.3.** … -/`, `/-- **Lemma 1.2.4.** … -/`. Each module
  docstring (`/-! … -/`) names the chapter and sections it covers.
* Helpers that are not in the source get no label. Their docstring says which result they
  serve, for example "used in the proof of Lemma 1.2.4".

## 2. File size: 1k–2k lines

* In a finished work, each file has between 1,000 and 2,000 lines.
* While a work is in progress, splitting files is fine, for example to give parallel agents
  disjoint files. Regroup the pieces into 1k–2k-line files once the campaign is over.
* Files over 2,000 lines are fine only for a dependency that the main work assumes
  (background the source cites or takes as known), not for the work's own results.
* Files under 1,000 lines are fine when a whole chapter of the source is that short. Merge
  adjacent sections before going below the limit for any other reason.

## 3. File names

The directory is flat (no subdirectories). File names encode the position in the source, from
coarse to fine, so that sorting the names alphabetically lists the files in source order:

* `Chapter<N>.lean` or `Chapter<N>Topic.lean`, only when chapter `N` is a single file;
* `Chapter<N>Section<M>Topic.lean`, for example `Chapter1Section2Cauchy.lean`, as soon as a
  chapter has several files;
* `Chapter<N>Section<M>TopicA.lean`, `Chapter<N>Section<M>TopicB.lean`, when section `M` spans
  several files; a `Chapter<N>Section<M>.lean` may group all of them.

Within a chapter, all files use the same level: if there is a `Chapter1Section4…` file, every
other Chapter 1 file names its section too (no `Chapter1Successor.lean` next to
`Chapter1Section4Cohomology.lean`). A file that covers several sections is named after the
section it starts in, or its main one. Use the source's own topic words, in `UpperCamelCase`.
Results the source cites without proving them (background from the literature) go in their own
files named `Preliminaries<Result>.lean`, for example `PreliminariesLambdaOrthogonality.lean` or
`PreliminariesSolomonTits.lean`. They sort after the chapters, and they may import the
chapter files where the key definitions they need live. Name other helpers that are not part of
the source by topic alone, for example `FlagLemmas.lean`.

## 4. Library and namespace names

Each work is one library (`[[lean_lib]]`), named after the surname of its (first) author:

* theses: `<Name>Phd`, `<Name>Lic` or `<Name>Msc`, for example `ScoccolaPhd`, `MartinPhd`;
* papers: `<Author><Yyyy>`, for example `Smith2021`, or `<Author><Yyyy><Title>` when the
  author has several papers that year, for example `Smith2021Interleavings`.

The Lean namespace of the work is the library name: every file of `ScoccolaPhd` lives in
`namespace ScoccolaPhd`. The `namespace` field of `works.toml` matches it.


## 5. Gaps and changes

Wherever the Lean text departs from the source, the docstring of the declaration where the
departure lives says so, in a paragraph of its own. The paragraph runs to the next blank line.
`scripts/update_stats.py` collects these paragraphs into the README.

**Gaps** are defects of the source. Tag them `**Gap (<kind>).**`, or
`**Gap (<kind>, <where>).**` when the defect is not in the result the docstring labels.

| Kind | Meaning |
|---|---|
| `error` | the statement is false as printed; Lean states the corrected version |
| `missing hypothesis` | the source uses an assumption it never states |
| `proof gap` | the statement is right but the argument skips or botches a step |
| `unproved` | the source states a claim without proof |
| `imprecise` | the statement admits several readings; say which one Lean takes and why |
| `typo` | notation or index slips that do not affect the mathematics |

**Changes** are deliberate departures where the source is not wrong: a simpler proof, a
different route, a restructured definition, a stronger statement. Tag them
`**Change (<where>).**`, or `**Change.**` for the docstring's own label.

```lean
/-- **Lemma 1.21.** `∑_{P ⊇ B} ± [n choose P]_ħ = ħ^{C(n,2)}`.

**Gap (error).** The thesis prints the sign as `(-1)^{|P|}`; that is off by `(-1)ⁿ` (check
`n = 1`). We formalize the corrected identity.

**Change.** We prove it by induction on `n` instead of the thesis's bijective argument, which
needs the whole of Section 1.4. -/
```

The README's `gaps` block sorts gaps by severity, which follows from the kind (high: `error`,
`missing hypothesis`; medium: `proof gap`, `unproved`; low: `imprecise`, `typo`), and marks
each *formalized* when its declaration is `sorry`-free, *open* otherwise. The `changes` block
lists the changes.

A note says what the source has, what Lean does instead, and why. It is concrete enough to
check: give a counterexample, the missing step or the reading chosen. Use a gap only for a
real defect; a different proof is a change. Delete notes that turn out to be wrong. If an
explanation needs more than a paragraph, write `<Lib>/<where>-<slug>.md` and link it.
