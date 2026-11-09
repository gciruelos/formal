#!/usr/bin/env python3
"""Regenerate the generated sections of the project READMEs and of the index README.

A project is a `lean_lib` of `lakefile.toml` (directory `<Lib>/`, root file
`<Lib>.lean`, metadata in the `[<Lib>]` table of `works.toml`). For each project this script
builds it (`lake build <Lib>`), runs `scripts/proof_stats.lean` against its root module,
and rewrites the README blocks between

    <!-- BEGIN GENERATED: <block> -->  ...  <!-- END GENERATED: <block> -->

for the blocks `main` (headline results and their axioms), `gaps` (source gaps, read from
`**Gap (<kind>).**` paragraphs in docstrings) and `stats` (per-file statistics). The index, the top-level
`README.md`, gets one row per project in its `projects` block. Text outside the
markers is never touched.

Usage (from anywhere):
    python3 scripts/update_stats.py                  # all projects + index
    python3 scripts/update_stats.py MartinPhd       # one project (+ index, from cache)
    python3 scripts/update_stats.py --check          # fail if anything is stale
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass, field
import html
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

LEAN_ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = LEAN_ROOT / "scripts" / "proof_stats.lean"
# Gap kinds, most serious first, with the severity shown in the README.
GAP_SEVERITY = {"error": "high", "missing hypothesis": "high", "proof gap": "medium",
                "unproved": "medium", "imprecise": "low", "typo": "low"}
GAP_KINDS = tuple(GAP_SEVERITY)


# ---------------------------------------------------------------- source parsing

def code_only(source: str) -> str:
    """Blank out comments, strings and «quoted» identifiers, keeping line breaks."""
    out, i, depth = [], 0, 0
    while i < len(source):
        start = i
        if depth:
            if source.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif source.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                i += 1
        elif source.startswith("/-", i):
            depth, i = 1, i + 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            i += 1
        elif source[i] == "«":
            end = source.find("»", i + 1)
            i = len(source) if end < 0 else end + 1
        else:
            out.append(source[i])
            i += 1
            continue
        out.append(" " + "\n" * source[start:i].count("\n"))
    return "".join(out)


SORRY = re.compile(r"(?<![\w'.])sorry(?![\w'])")
DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|opaque|inductive|structure|class|instance)\b",
    re.MULTILINE)


def source_counts(source: str) -> Counter:
    code = code_only(source)
    c = Counter(lines=len(source.splitlines()), sorry=len(SORRY.findall(code)))
    matches = list(DECL.finditer(code))
    for m, nxt in zip(matches, matches[1:] + [None]):
        kind = m[1]
        chunk = code[m.end():nxt.start() if nxt else len(code)]
        if kind in ("theorem", "lemma", "instance"):
            c["statements"] += 1
            c["open"] += bool(SORRY.search(chunk))
        elif kind in ("def", "abbrev", "opaque"):
            c["defs"] += 1
        else:
            c["types"] += 1
    return c


@dataclass
class Gap:
    path: Path
    line: int
    decl: str
    where: str
    kind: str
    note: str


GAP_TAG = re.compile(r"\*\*Gap \(([^)]*)\)\.\*\*")
CHANGE_TAG = re.compile(r"\*\*Change(?: \(([^)]*)\))?\.\*\*")
DOC = re.compile(r"/--(.*?)-/", re.DOTALL)
NAME_AFTER = re.compile(
    r"\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|inductive|structure|class|instance)\s+([^\s:({\[]+)")
WHERE = re.compile(
    r"^\W*((?:Lemma|Theorem|Proposition|Prop\.|Corollary|Cor\.|Definition|Def\.|Example|"
    r"Remark|Construction)\s+\d[\d.]*\d|\(\d+\.\d+\))")


def find_gaps(path: Path, source: str) -> list[Gap]:
    gaps = []
    for doc in DOC.finditer(source):
        body = doc[1]
        decl = NAME_AFTER.match(source, doc.end())
        where = WHERE.search(body.strip())
        for tag in GAP_TAG.finditer(body):
            kind, _, loc = (x.strip() for x in tag[1].partition(","))
            if kind not in GAP_KINDS:
                raise RuntimeError(f"{path}: unknown gap kind {kind!r}; use one of {GAP_KINDS}")
            rest = body[tag.end():]
            para = re.split(r"\n\s*\n|\*\*Gap \(", rest)[0]
            gaps.append(Gap(path, source.count("\n", 0, doc.start()) + 1,
                            decl[1] if decl else "—", loc or (where[1] if where else "—"), kind,
                            " ".join(para.split())))
    return gaps


# ---------------------------------------------------------------- projects

@dataclass
class Project:
    lib: str
    meta: dict
    files: list[Path] = field(default_factory=list)
    lean: dict | None = None

    @property
    def name(self) -> str:
        return self.lib

    @property
    def dir(self) -> Path:
        return LEAN_ROOT / self.lib

    def module(self, path: Path) -> str:
        return self.lib if path.parent == LEAN_ROOT else f"{self.lib}.{path.stem}"

    def link(self, path: Path) -> str:
        """Path of `path` relative to the project's README."""
        return f"../{path.name}" if path.parent == LEAN_ROOT else path.name


def natural_key(path: Path):
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", path.as_posix())]


def load_projects() -> list[Project]:
    """One project per `lean_lib` of the shared lakefile; metadata from `works.toml`."""
    lake = tomllib.loads((LEAN_ROOT / "lakefile.toml").read_text())
    works = tomllib.loads((LEAN_ROOT / "works.toml").read_text())
    projects = []
    for lib in (l["name"] for l in lake["lean_lib"]):
        if lib not in works:
            raise RuntimeError(f"lean_lib {lib} has no [{lib}] table in works.toml")
        files = [LEAN_ROOT / f"{lib}.lean", *sorted((LEAN_ROOT / lib).glob("*.lean"), key=natural_key)]
        projects.append(Project(lib, works[lib], [f for f in files if f.exists()]))
    return projects


def run(cmd: list[str], cwd: Path) -> str:
    r = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True)
    if r.returncode:
        sys.stderr.write(r.stdout[-4000:] + r.stderr[-4000:])
        raise RuntimeError(f"{' '.join(cmd)} failed in {cwd}")
    return r.stdout


def lean_stats(p: Project) -> dict:
    print(f"[{p.name}] lake build {p.lib}", file=sys.stderr)
    run(["lake", "build", p.lib], LEAN_ROOT)
    mains = ", ".join(f"`{m['name']}" for m in p.meta.get("main", []))
    script = TEMPLATE.read_text().replace("«ROOT»", p.lib).replace("[MAIN]", f"[{mains}]")
    tmp = LEAN_ROOT / ".lake" / f"proof_stats_{p.lib}.lean"
    tmp.write_text(script)
    print(f"[{p.name}] measuring", file=sys.stderr)
    out = run(["lake", "env", "lean", str(tmp.relative_to(LEAN_ROOT))], LEAN_ROOT)
    payload = [l.split("\t", 1)[1] for l in out.splitlines() if l.startswith("STATS_JSON\t")]
    if len(payload) != 1:
        raise RuntimeError(f"unexpected output from proof_stats.lean:\n{out}")
    data = json.loads(payload[0])
    (LEAN_ROOT / ".lake" / f"stats_{p.lib}.json").write_text(json.dumps(data))
    return data


def cached_stats(p: Project) -> dict | None:
    f = LEAN_ROOT / ".lake" / f"stats_{p.lib}.json"
    return json.loads(f.read_text()) if f.exists() else None


def short(name: str, p: Project) -> str:
    name = re.sub(r"^_private\..*?\.\d+\.", "", name)
    ns = p.meta.get("namespace")
    return name[len(ns) + 1:] if ns and name.startswith(ns + ".") else name


def code(s: str) -> str:
    return f"`{s}`"


# ---------------------------------------------------------------- tables

def sorry_names(p: Project) -> tuple[set[str], set[str]]:
    mods = p.lean["modules"] if p.lean else []
    dep = {short(n, p) for m in mods for n in m["sorry_dependent"]}
    direct = {short(n, p) for m in mods for n in m["direct_sorry"]}
    return dep, direct


def find_changes(path: Path, source: str) -> list[Gap]:
    """`**Change.**` / `**Change (<where>).**` paragraphs: deliberate deviations from the source."""
    out = []
    for doc in DOC.finditer(source):
        body = doc[1]
        decl = NAME_AFTER.match(source, doc.end())
        where = WHERE.search(body.strip())
        for tag in CHANGE_TAG.finditer(body):
            para = re.split(r"\n\s*\n|\*\*(?:Gap|Change)\b", body[tag.end():])[0]
            out.append(Gap(path, source.count("\n", 0, doc.start()) + 1,
                           decl[1] if decl else "—", (tag[1] or "").strip() or (where[1] if where else "—"),
                           "change", " ".join(para.split())))
    return out


def changes_block(p: Project) -> str:
    ch = [c for f in p.files for c in find_changes(f, f.read_text(encoding="utf-8"))]
    if not ch:
        return "_No changes recorded yet._"
    rows = ["| Where | Lean | Change |", "|:---|:---|:---|"]
    for c in ch:
        rows.append(f"| {c.where} | [{code(c.decl)}]({p.link(c.path)}#L{c.line}) | "
                    f"{c.note.replace('|', '&#124;')} |")
    return "\n".join(rows)


def all_gaps(p: Project) -> list[Gap]:
    return [g for f in p.files for g in find_gaps(f, f.read_text(encoding="utf-8"))]


def gap_status(g: Gap, p: Project) -> str:
    dep, direct = sorry_names(p)
    hit = lambda s: any(n == g.decl or n.endswith("." + g.decl) for n in s)
    if hit(direct) or hit(dep):
        return "open (`sorry`)"
    return "formalized"


def gaps_block(p: Project) -> str:
    gaps = sorted(all_gaps(p), key=lambda g: GAP_KINDS.index(g.kind))
    if not gaps:
        return "_No gaps recorded yet._"
    rows = ["| Severity | Where | Kind | Lean | Status | Note |", "|:---|:---|:---|:---|:---|:---|"]
    for g in gaps:
        rel = p.link(g.path)
        rows.append(f"| {GAP_SEVERITY[g.kind]} | {g.where} | {g.kind} | "
                    f"[{code(g.decl)}]({rel}#L{g.line}) | {gap_status(g, p)} | "
                    f"{g.note.replace('|', '&#124;')} |")
    return "\n".join(rows) + GAP_LEGEND


GAP_LEGEND = """

*Severity*: **high** means the printed statement is false or needs an unstated assumption;
**medium** means the statement is right but its proof is wrong, incomplete or missing;
**low** means an ambiguity or typo that a careful reader resolves. *Status* is *formalized*
when the declaration carrying the note is `sorry`-free."""


def main_block(p: Project) -> str:
    mains = p.meta.get("main", [])
    if not mains:
        return "_No headline results configured in `works.toml`._"
    info = {m["name"]: m for m in (p.lean or {}).get("main", [])}
    rows = ["| Result | Lean | `sorry`s it depends on | Status |", "|:---|:---|---:|:---|"]
    for m in mains:
        i = info.get(m["name"], {})
        if not i.get("found"):
            n, status = "—", "not found"
        else:
            leaves = {short(x, p) for x in i.get("sorry_leaves", [])}
            own = short(m["name"], p) in leaves
            n = len(leaves - {short(m["name"], p)})
            status = ("statement only (its proof is `sorry`)" if own
                      else "open" if i["sorry"] else "**proved**")
            extra = set(i["axioms"]) - {"propext", "Classical.choice", "Quot.sound", "sorryAx"}
            if extra:
                status += " (axioms: " + ", ".join(code(x) for x in sorted(extra)) + ")"
        rows.append(f"| {m.get('label', '')} | {code(short(m['name'], p))} | {n} | {status} |")
    return "\n".join(rows) + MAIN_LEGEND


MAIN_LEGEND = """

*`sorry`s it depends on* counts the other declarations of this project with an explicit
`sorry` that the result reaches through its statement and proof. For a result whose own proof
is still `sorry` this only covers its statement. A **proved** result uses only `propext`,
`Classical.choice` and `Quot.sound`, unless other axioms are listed."""


def file_parts(f: Path) -> tuple[str, str]:
    """Split a file name into a shared prefix (chapter/section) and the rest."""
    m = re.match(r"(Chapter\d+(?:Section\d+)?)(.*)\.lean$", f.name)
    return (m[1], m[2] + ".lean") if m else (f.stem, ".lean")


def dag_cell(m: dict | None, kind: str, p: Project) -> str:
    if m is None or not m[f"max_{kind}_dag"]:
        return "—"
    return f"{m[f'max_{kind}_dag']:,} (<code>{html.escape(short(m[f'max_{kind}_name'], p))}</code>)"


def stats_block(p: Project) -> str:
    lean = {m["module"]: m for m in (p.lean or {}).get("modules", [])}
    rows = ["| Prefix | File | Lines | Statements | Defs | Types | `sorry`s | "
            "Max statement DAG (statement) | Max proof DAG (proof) | Theorems with `sorry` |",
            "|:---|:---|---:|---:|---:|---:|---:|:---|:---|:---|"]
    tot = Counter()
    best = {"statement": (0, None), "proof": (0, None)}
    prev = None
    for f in [*p.files[1:], *p.files[:1]]:  # root module last
        rel = p.link(f)
        c = source_counts(f.read_text(encoding="utf-8"))
        tot.update(c)
        m = lean.get(p.module(f))
        for k in best:
            if m and m[f"max_{k}_dag"] > best[k][0]:
                best[k] = (m[f"max_{k}_dag"], m)
        if m is None:
            names = "_not imported by the root module_"
        else:
            ds = sorted({short(x, p) for x in m["direct_sorry"]})
            names = ", ".join(f"<code>{html.escape(x)}</code>" for x in ds) or "—"
        prefix, suffix = file_parts(f)
        cell = f"**{prefix}**" if prefix != prev else ""
        prev = prefix
        vals = [c[k] for k in ("lines", "statements", "defs", "types", "sorry")]
        rows.append(f"| {cell} | [{suffix}]({rel}) | " + " | ".join(f"{v:,}" for v in vals)
                    + f" | {dag_cell(m, 'statement', p)} | {dag_cell(m, 'proof', p)} | {names} |")
    vals = [tot[k] for k in ("lines", "statements", "defs", "types", "sorry")]
    mx = [f"**{best[k][0]:,}** (<code>{html.escape(short(best[k][1][f'max_{k}_name'], p))}</code>)"
          if best[k][1] else "—" for k in ("statement", "proof")]
    rows.append("| **Total / maximum** | | " + " | ".join(f"**{v:,}**" for v in vals)
                + f" | {mx[0]} | {mx[1]} | |")
    return "\n".join(rows) + STATS_LEGEND


STATS_LEGEND = """

The shared **Prefix** is the chapter/section; append **File** to recover the filename. The root
module appears last.

- **Lines** includes blank lines and comments.
- **Statements** counts `theorem`, `lemma` and `instance` commands, including private ones.
- **Defs** counts `def`, `abbrev` and `opaque`; **Types** counts `inductive`, `structure` and
  `class`. Generated declarations, constructors and fields are not counted.
- **`sorry`s** counts explicit tokens outside comments, strings and quoted identifiers.
- **Max statement DAG (statement)** is the size of the largest elaborated theorem type;
  **Max proof DAG (proof)** the largest theorem body (hash-consed expression DAG), each with
  the declaration's name. Both include compiler-generated theorems.
- **Theorems with `sorry`** lists declarations (of any kind) whose own term contains `sorryAx`.

Generated by [`scripts/update_stats.py`](../scripts/update_stats.py)."""


def index_row(p: Project) -> str:
    c = Counter()
    for f in p.files:
        c.update(source_counts(f.read_text(encoding="utf-8")))
    m = p.meta
    work = f"{m.get('author', '')}, *{m.get('title', '')}* ({m.get('kind', '')}, {m.get('year', '')})"
    info = {x["name"]: x for x in (p.lean or {}).get("main", [])}
    mains = m.get("main", [])
    proved = sum(1 for x in mains if info.get(x["name"], {}).get("found")
                 and not info[x["name"]]["sorry"])
    gaps = all_gaps(p)
    open_gaps = sum(1 for g in gaps if gap_status(g, p).startswith("open"))
    tot = sum(x["theorems"] for x in (p.lean or {}).get("modules", []))
    free = tot - sum(len(x["sorry_dependent"]) for x in (p.lean or {}).get("modules", []))
    return (f"| [{p.name}]({p.name}/README.md) | {work} | {m.get('scope', '')} | {c['lines']:,} | "
            f"{free}/{tot} | {c['sorry']} | {proved}/{len(mains)} | {len(gaps)} ({open_gaps} open) |")


def index_block(projects: list[Project]) -> str:
    rows = ["| Project | Work | Scope | Lines | Sorry-free theorems | `sorry` | Main results proved "
            "| Gaps found |", "|:---|:---|:---|---:|---:|---:|---:|---:|"]
    rows += [index_row(p) for p in projects]
    return "\n".join(rows)


# ---------------------------------------------------------------- README rewriting

def replace_blocks(text: str, blocks: dict[str, str], where: Path) -> str:
    for name, body in blocks.items():
        begin, end = f"<!-- BEGIN GENERATED: {name} -->", f"<!-- END GENERATED: {name} -->"
        if text.count(begin) != 1 or text.count(end) != 1:
            raise RuntimeError(f"{where} needs exactly one '{begin}' / '{end}' pair")
        a = text.index(begin) + len(begin)
        b = text.index(end, a)
        text = text[:a] + "\n\n" + body + "\n\n" + text[b:]
    return text


def write(path: Path, new: str, check: bool) -> bool:
    old = path.read_text(encoding="utf-8")
    if old == new:
        return True
    if check:
        print(f"stale: {path.relative_to(LEAN_ROOT)}", file=sys.stderr)
        return False
    path.write_text(new, encoding="utf-8")
    print(f"updated: {path.relative_to(LEAN_ROOT)}", file=sys.stderr)
    return True


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("projects", nargs="*", help="project directories (default: all)")
    ap.add_argument("--check", action="store_true", help="fail if any README is stale; write nothing")
    args = ap.parse_args()
    projects = load_projects()
    selected = {Path(x).name.removesuffix(".lean") for x in args.projects} or {p.name for p in projects}
    unknown = selected - {p.name for p in projects}
    if unknown:
        raise RuntimeError(f"not a lean_lib in lakefile.toml: {', '.join(sorted(unknown))}")
    ok = True
    for p in projects:
        if p.name in selected:
            try:
                p.lean = lean_stats(p)
            except RuntimeError as e:
                p.lean = cached_stats(p)
                if p.lean is None:
                    raise
                print(f"warning: {e}; using the last successful measurement", file=sys.stderr)
                ok = False
            readme = p.dir / "README.md"
            new = replace_blocks(readme.read_text(encoding="utf-8"), {
                "main": main_block(p), "gaps": gaps_block(p), "changes": changes_block(p), "stats": stats_block(p)}, readme)
            ok &= write(readme, new, args.check)
        else:
            p.lean = cached_stats(p)
    index = LEAN_ROOT / "README.md"
    ok &= write(index, replace_blocks(index.read_text(encoding="utf-8"),
                                      {"projects": index_block(projects)}, index), args.check)
    return 0 if ok else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, KeyError) as e:
        print(f"error: {e}", file=sys.stderr)
        raise SystemExit(1)
