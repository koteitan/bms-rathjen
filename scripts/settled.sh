#!/usr/bin/env bash
# scripts/settled.sh — wait until a worker's file has stopped changing.
#
# WHY THIS IS A FILE AND NOT A SHELL LOOP I RETYPE.  The throwaway version was
# wrong twice, in the same night, in the same direction:
#
#   1. it treated 60s of silence as "finished" — these workers pause longer than
#      that while thinking, so it reported a file settled that was still growing,
#      and the verdict measured against it went stale within minutes;
#   2. after that was fixed, it reported "settled" for a file that DID NOT EXIST,
#      because `sha256sum missing | cut` returns the exit status of `cut`, which
#      succeeds, so the `|| echo absent` fallback never ran and two empty strings
#      compared equal.
#
# Both read as "done".  Retyping a probe reproduces its holes (constitution C8);
# freezing it with a self-test is the fix.  Run `scripts/settled.sh --self-test`.
#
# Usage:  scripts/settled.sh FILE [QUIET_ROUNDS] [INTERVAL_SEC] [MAX_ROUNDS]
# Exits:  0 settled   3 no file within the deadline   4 still moving
# Prints exactly one line, and the line names which of the three happened.

set -uo pipefail

# Defaults are NAMED so the self-test can assert them.  The historical bug was a
# threshold of one quiet round; a behavioural test that passes its own threshold
# never exercises the default and cannot see that regression.
DEFAULT_QUIET=3
DEFAULT_INTERVAL=60
DEFAULT_MAX=60

hash_of() {
  # An absent file gets a DISTINCT marker, never the empty string, and never the
  # same marker as any real hash.  "absent" and "unchanged" must not collide.
  if [ -f "$1" ]; then sha256sum "$1" | cut -c1-16; else printf '__ABSENT__'; fi
}

settled() {
  local file="$1" need="${2:-$DEFAULT_QUIET}" interval="${3:-$DEFAULT_INTERVAL}" max="${4:-$DEFAULT_MAX}"
  local prev="__INIT__" cur quiet=0 i
  for ((i = 0; i < max; i++)); do
    cur="$(hash_of "$file")"
    if [ "$cur" = "$prev" ] && [ "$cur" != "__ABSENT__" ]; then
      quiet=$((quiet + 1))
    else
      quiet=0
    fi
    if [ "$quiet" -ge "$need" ]; then
      echo "SETTLED $file after ${quiet} quiet rounds"
      return 0
    fi
    prev="$cur"
    sleep "$interval"
  done
  if [ ! -f "$file" ]; then
    echo "NOFILE $file never appeared in $((max * interval))s"
    return 3
  fi
  echo "MOVING $file still changing after $((max * interval))s"
  return 4
}

# --- self-test (constitution C0: fire the instrument at what it must catch) ---
# Each case is a behaviour the two historical bugs would get WRONG.  A run that
# only checks the happy path cannot tell this from a script that always says
# SETTLED, so the pausing case is here precisely because the first version failed it.
self_test() {
  local d out rc fails=0
  d="$(mktemp -d)"; trap 'rm -rf "$d"' RETURN

  # 1. absent file must NOT be reported settled  (the second historical bug)
  out="$(settled "$d/nope" 2 1 3)"; rc=$?
  [[ $rc -eq 3 && "$out" == NOFILE* ]] || { echo "FAIL absent: rc=$rc $out"; fails=1; }

  # 2. a file that stops changing must be reported settled
  printf 'x' > "$d/still"
  out="$(settled "$d/still" 2 1 6)"; rc=$?
  [[ $rc -eq 0 && "$out" == SETTLED* ]] || { echo "FAIL still: rc=$rc $out"; fails=1; }

  # 3. a file written slowly, with a gap LONGER than one interval, must NOT be
  #    called settled while it is still being written  (the first historical bug)
  printf 'a' > "$d/slow"
  ( for k in 1 2 3 4; do sleep 2; printf 'more%s' "$k" >> "$d/slow"; done ) &
  local writer=$!
  out="$(settled "$d/slow" 2 1 6)"; rc=$?
  wait "$writer" 2>/dev/null
  [[ "$out" == SETTLED* ]] && { echo "FAIL slow: called settled while still writing — $out"; fails=1; }

  # 4. a file created late must be picked up, not reported NOFILE
  ( sleep 2; printf 'late' > "$d/late" ) &
  writer=$!
  out="$(settled "$d/late" 2 1 8)"; rc=$?
  wait "$writer" 2>/dev/null
  [[ $rc -eq 0 && "$out" == SETTLED* ]] || { echo "FAIL late: rc=$rc $out"; fails=1; }

  # 5. THE DEFAULT THRESHOLD ITSELF.  Cases 1-4 all pass an explicit `need`, so
  #    none of them touches the default — and the default is exactly what was
  #    wrong historically (one quiet round, so a thinking worker read as done).
  #    Verified by mutation: lowering DEFAULT_QUIET to 1 left cases 1-4 passing.
  [ "$DEFAULT_QUIET" -ge 3 ] || { echo "FAIL default: DEFAULT_QUIET=$DEFAULT_QUIET, must be >= 3"; fails=1; }
  [ "$DEFAULT_INTERVAL" -ge 30 ] || { echo "FAIL default: DEFAULT_INTERVAL=$DEFAULT_INTERVAL, must be >= 30"; fails=1; }

  if [ "$fails" -eq 0 ]; then echo "settled.sh self-test: 5/5 (absent, still, slow-writer, late-create, default-threshold)"; return 0; fi
  echo "settled.sh self-test: FAILURES above"; return 1
}

if [ "${1:-}" = "--self-test" ]; then self_test; exit $?; fi
[ $# -ge 1 ] || { echo "usage: $0 FILE [QUIET_ROUNDS] [INTERVAL_SEC] [MAX_ROUNDS]" >&2; exit 2; }
settled "$@"
