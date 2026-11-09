# Autoformalization

## Installing and running Lean

Install [`elan`](https://github.com/leanprover/elan), the Lean toolchain manager. It reads
`lean-toolchain` and fetches the pinned Lean version on first use:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
```

Then, from the project root:

```bash
lake exe cache get          # download prebuilt Mathlib (otherwise Mathlib builds from source, hours)
lake build                  # every work
lake build ScoccolaPhd      # one work
lake build ScoccolaPhd.Chapter5Section2Flows   # one module (and what it imports)
lake env lean ScoccolaPhd/Chapter5Section2Flows.lean   # check a file without building its dependents
```

The first build fetches Mathlib into `.lake/packages`. Rebuilding a module after an edit only
recompiles it and the modules that import it. The statistics script
(`python3 scripts/update_stats.py`, Python ≥ 3.11) also builds before measuring.

## One library per work

This repository is a single Lake project. Each formalized work (thesis, paper, book chapter)
is one `[[lean_lib]]` in `lakefile.toml`, named as in [`STYLE.md`](STYLE.md) (`ScoccolaPhd`,
`Smith2021`), and builds on its own with `lake build <Lib>`. A work has:

* `<Lib>/`: a **flat** directory holding the `.lean` files, the `README.md` and the source
  PDF (file naming and sizes: [`STYLE.md`](STYLE.md)).
* `<Lib>.lean`: the root module, importing every file of the work.
* `<Lib>/<Lib>.pdf`: the source.
* a `[<Lib>]` table in `works.toml`: `title`, `author`, `kind`, `year`, `source`, `scope`,
  `namespace`, and one `[[<Lib>.main]]` entry (`label`, fully qualified `name`) per headline
  result.

The README follows the fixed structure in [`README.md`](README.md#the-readme-of-a-work):
title, one sentence, main results (1–5, with a generated status table), the results in brief,
per-file statistics, gaps, and changes. Generated blocks sit between
`<!-- BEGIN GENERATED: <block> -->` and `<!-- END GENERATED: <block> -->`. Implementation
notes go in module docstrings, not in the README. Run
`python3 scripts/update_stats.py` (or `… <Lib>`) whenever counts change and before finishing a
session; it also refreshes the index in `README.md`. Do not edit generated blocks by hand.
Works must not import each other.

## Work from the source text

The source must be in the repository before formalizing starts: `<Lib>/<Lib>.pdf`, the
thesis, paper or chapter itself. If it is missing, get it (from the author's page, arXiv or
the publisher) or ask the user for it; do not formalize from memory or from a summary. Read it
with `pdftotext -layout <Lib>/<Lib>.pdf -` and rely on it heavily:

* read the relevant section before stating or proving anything, and take statements,
  hypotheses, definitions and numbering from it;
* follow its proofs; when a proof does not go through, check the text again before deciding
  it is a gap;
* quote or paraphrase it in docstrings where that helps a reader compare.

Results the source cites from other works (its references) are not in the PDF. Look them up
online (arXiv, the author's page, the cited book) to get the exact statement and hypotheses,
or ask the user for the reference text. Do not guess a cited statement; it goes in a
`Preliminaries<Result>.lean` file ([`STYLE.md`](STYLE.md)) and its docstring names where it
was taken from.

## Three passes

Formalize a source in **three passes, in this order**. Finish a pass for the whole target
(chapter/section) before starting the next.

1. **Outline.** Definitions and theorem statements only, with the source's numbering
   (e.g. `lemma_1_21`). Proofs are `sorry`. Make it build (`lake build`) and record any
   errors found in the source as gaps (see `STYLE.md`).
2. **Proofs that are not widely known.** The source's own results and arguments: the new
   lemmas, the key constructions, anything a reader could not look up elsewhere.
3. **Proofs that are widely cited.** Standard facts (textbook theorems, folklore, routine
   category-theory coherence, results Mathlib nearly has). Do these last, or import them
   from Mathlib when available.

## Gaps, changes and style

How files are organized and named, how declarations reference the source, and how gaps
(`**Gap (<kind>).**`) and changes (`**Change.**`) are documented are all in
[`STYLE.md`](STYLE.md). Read it before editing a work; it is the single source for those rules.

## Delegating to other coding agents

Rank the open `sorry`s by difficulty and pick a model from the table. Hard tasks are new
constructions, the source's key arguments, or anything that changes a definition. Medium tasks
are everything else: a clear proof in the source, Mathlib plumbing, routine unfolding and
short calculations. Most tasks are medium: default to a medium model, and use hard models
sparingly, only for the few tasks that need them.

| | claude (`--model`, `--effort low`) | codex (`-m`, `model_reasoning_effort=low`) | agy (`--model`) |
|---|---|---|---|
| hard | `claude-opus-5-5` | `gpt-6.1-sol` | `gemini-4-argon-low` |
| medium | `claude-sonnet-5-5` | `gpt-6.1-terra` | `gemini-3.8-flash-low` |

Model names are as the CLIs list them: `agy models`, `codex debug models`; `claude` takes a full
model name or an alias (`opus`, `sonnet`).

**How to call them.** Write the task to a prompt file in a scratch directory (not the repo),
then run the agent from the project root in the background, with stdout going to a file and
stdin closed (claude reads the prompt from stdin instead). Nothing is printed until the agent finishes.

```bash
# claude: --model claude-opus-5-5 or claude-sonnet-5-5
claude -p --model claude-sonnet-5-5 --effort low --permission-mode acceptEdits \
  --allowedTools "Bash(lake:*)" < prompt.md > out.txt
# codex: -m gpt-6.1-sol or gpt-6.1-terra
codex exec -m gpt-6.1-terra -c model_reasoning_effort=low -s workspace-write \
  "$(cat prompt.md)" </dev/null > out.txt
# agy: --model gemini-4-argon-low or gemini-3.8-flash-low (agy-host.sh takes the same arguments as agy)
scripts/agy-host.sh --model gemini-3.8-flash-low -p "$(cat prompt.md)" </dev/null > out.txt
```

* `scripts/agy-host.sh` runs `agy` headless. The agent reuses the installed toolchain and
  the built `.lake/`, edits are accepted automatically, and only Lean/Lake and read-only shell
  commands are allowed (add more with `AGY_EXTRA_ALLOW`). Plain `agy -p` auto-denies its first
  shell command. `agy models` lists the available models.
* `claude -p` cannot ask for permissions: `--permission-mode acceptEdits` lets it edit files,
  and `--allowedTools "Bash(lake:*)"` lets it run `lake`.
* `codex exec -s workspace-write` can edit the repo and run the local `lake`, with no network.

**The prompt file must say:**
* the task (which `sorry`s or declarations) and the files it may edit;
* the files not to touch;
* the source PDF and the section numbers to read, and that the agent must read them
  (`pdftotext -layout`) and follow the text, not its memory of the result;
* "never leave the build broken";
* "no `git commit/push/stash/checkout/reset`";
* "report what is closed, what remains, and any gaps".

Agents edit the repository files in place; do not hand them scratch copies. To keep that
safe, delineate the work: each agent running at the same time gets its own task and its own
disjoint set of files, named in its prompt, and no two agents edit the same file.

All agents share the working tree and `.lake/`, so a concurrent `lake build` may wait on a
lock. Tell agents to build single modules (`lake build ScoccolaPhd.Chapter2Section1Metric`).
Afterwards, read `git diff` and run a full `lake build <Lib>` yourself before trusting any
report.

## Commits

Do not commit unless asked.
