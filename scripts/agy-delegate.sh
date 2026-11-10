#!/usr/bin/env bash
# Launch an agy worker in the background from a prompt file.
# Usage: scripts/agy-delegate.sh MODEL PROMPT_FILE OUT_FILE
# Reads the prompt itself (no shell quoting to get wrong), closes stdin, detaches, and writes
# the worker PID to OUT_FILE.pid. Stop a worker with `kill $(cat OUT_FILE.pid)`; never use
# `pkill -f agy...` (it matches the calling shell's own command line).
set -euo pipefail
[ $# -eq 3 ] || { echo "usage: $0 MODEL PROMPT_FILE OUT_FILE" >&2; exit 2; }
model=$1 prompt=$(realpath "$2") out=$(realpath -m "$3")
[ -s "$prompt" ] || { echo "empty or missing prompt file: $prompt" >&2; exit 2; }
cd "$(dirname "$0")/.."
export AGY_LOG=${AGY_LOG:-$out.log.json}   # so denied commands are reported in OUT_FILE
# Every worker is told how the sandbox restricts the shell.
prompt_text="$(cat "$prompt")

Shell rules: python3, rm and compound commands (||, &&, ;, \$(...)) are denied in this sandbox. Run single plain commands only, e.g. \`pdftotext -layout Work/Work.pdf /tmp/work.txt\` once, then grep/sed/head on that text file."
setsid nohup scripts/agy-host.sh --model "$model" -p "$prompt_text" </dev/null >"$out" 2>&1 &
echo $! >"$out.pid"
sleep 15
# fail fast on quota/auth errors, which agy prints immediately
if grep -q "AGY_ERROR\|^error:\|STUCK" "$out" 2>/dev/null; then
  echo "worker failed to start:" >&2; head -c 400 "$out" >&2; exit 1
fi
echo "started $model pid $(cat "$out.pid") -> $out"
