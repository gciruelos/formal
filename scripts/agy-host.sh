#!/bin/bash
# Run agy headless on the host (no Docker), reusing the installed Lean toolchain and the
# built .lake/. Permissions are an allow-list of command prefixes instead of
# --dangerously-skip-permissions: Lean/Lake and read-only utilities, cd/cp/mkdir, read-only git (no rm, git write ops, curl,
# python). File edits are auto-accepted (--mode accept-edits). Usage, from the project root:
#   scripts/agy-host.sh --model gemini-3.8-flash-high --effort high -p "$(cat prompt.md)" </dev/null
# Headless mode auto-denies any command outside the allow-list and then stops with empty output
# (python3 -c, rm, curl, git write ops...). Set AGY_LOG=file to record the stream-json event log
# and list the denied commands at the end; the prompt should tell the agent to use grep/sed/awk.
# Compound commands (||, &&, ;, $(...), pipes into denied tools) and python3 -c are denied: the prompt
# should say to run single plain commands (e.g. `pdftotext -layout X.pdf out.txt` once, then grep/sed).
# Extra rules: AGY_EXTRA_ALLOW='"command(python3)","command(make)"'.
SETTINGS=$(mktemp --suffix=.json)
trap 'rm -f "$SETTINGS"' EXIT
cat > "$SETTINGS" <<EOF
{"permissions":{"allow":[
"command(lake env lean)","command(lake build)","command(lake)","command(lean)",
"command(ls)","command(cat)","command(grep)","command(sed)","command(head)","command(tail)",
"command(wc)","command(find)","command(pdftotext)","command(diff)",
"command(cd)","command(echo)","command(pwd)","command(cp)","command(mkdir)","command(touch)","command(awk)",
"command(sort)","command(uniq)","command(tr)","command(cut)","command(test)","command(true)",
"command(rg)","command(nl)","command(less)","command(printf)","command(tee)","command(time)","command(timeout)","command(basename)","command(dirname)","command(realpath)","command(xargs)","command(python3 scripts/update_stats.py)","command(pdftotext)","command(wc)","command(find)","command(diff)","command(echo)","command(pwd)",
"command(git diff)","command(git status)","command(git log)","command(git show)","command(git grep)","command(git blame)"${AGY_EXTRA_ALLOW:+,$AGY_EXTRA_ALLOW}
]}}
EOF
if [ -n "$AGY_LOG" ]; then
  agy --mode accept-edits --settings "$SETTINGS" --output-format stream-json "$@" > "$AGY_LOG"
  rc=$?
  if grep -q '"denied_actions":\[{' "$AGY_LOG"; then
    echo "agy-host: STUCK on a denied command (the run stopped there):" >&2
    grep '"state":"DONE","step_type":"tool","tool_name":"run_command"' "$AGY_LOG" | grep -v '"output"' | tail -1 \
      | grep -o '"CommandLine":"[^}]*' >&2
    echo "agy-host: allow it with AGY_EXTRA_ALLOW='\"command(<prefix>)\"' or tell the prompt not to use it (rm, python3 are denied by default)." >&2
  fi
  grep -o '"denied_actions":\[[^]]*\]' "$AGY_LOG" | tail -1 >&2
  grep -o '"response":"[^"]*"' "$AGY_LOG" | tail -1 | sed 's/^"response":"//; s/"$//; s/\\n/\n/g'
  exit $rc
fi
exec agy --mode accept-edits --settings "$SETTINGS" "$@"
