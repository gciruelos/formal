#!/bin/bash
# Run agy headless on the host (no Docker), reusing the installed Lean toolchain and the
# built .lake/. Permissions are an allow-list of command prefixes instead of
# --dangerously-skip-permissions: Lean/Lake and read-only utilities, cd/cp/mkdir, read-only git (no rm, git write ops, curl,
# python). File edits are auto-accepted (--mode accept-edits). Usage, from the project root:
#   scripts/agy-host.sh --model gemini-3.8-flash-high --effort high -p "$(cat prompt.md)" </dev/null
# Extra rules: AGY_EXTRA_ALLOW='"command(python3)","command(make)"'.
SETTINGS=$(mktemp --suffix=.json)
trap 'rm -f "$SETTINGS"' EXIT
cat > "$SETTINGS" <<EOF
{"permissions":{"allow":[
"command(lake env lean)","command(lake build)","command(lake)","command(lean)",
"command(ls)","command(cat)","command(grep)","command(sed)","command(head)","command(tail)",
"command(wc)","command(find)","command(pdftotext)","command(diff)",
"command(cd)","command(echo)","command(pwd)","command(cp)","command(mkdir)","command(touch)","command(awk)",
"command(sort)","command(uniq)","command(tr)","command(cut)","command(test)","command(true)","command(python3 scripts/update_stats.py)",
"command(git diff)","command(git status)","command(git log)","command(git show)"${AGY_EXTRA_ALLOW:+,$AGY_EXTRA_ALLOW}
]}}
EOF
exec agy --mode accept-edits --settings "$SETTINGS" "$@"
