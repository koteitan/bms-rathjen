#!/usr/bin/env bash
# bp2pss-check.sh — cross-check §85's `bInv85` against naruyoko's `TransRev`.
#
#   scripts/bp2pss-check.sh
#   PSS2BP=/path/to/dir/holding/common.js scripts/bp2pss-check.sh
#
# WHY THIS EXISTS.  `bOnto85` is a THEOREM with no unproved hypothesis, so this
# cannot remove a gate.  What it can catch is a DEFINITIONAL mismatch: `bValA71`
# meaning something other than naruyoko's `Trans`, which would make the theorem
# true about the wrong object.  Until now `bInv85` was only ever checked against
# this repository's own forward map (§85.7's `pool85.all fun b => bValA71 (bInv85
# b) == b`) — the same instrument twice.  `TransRev` is an INDEPENDENT inverse.
#
# It is standalone rather than part of scripts/crosscheck.sh: that script is gated
# on $YABMS and compares the BMS side against yaBMS's C implementation, and has no
# business acquiring a node / $PSS2BP dependency.  Run both.
#
# Exit: 0 no value mismatch and every control behaved as declared, 1 otherwise,
#       2 could not run.
set -u
cd "$(dirname "$0")/.."

CLI="lean/.lake/build/bin/bp2psscli"
REF="scripts/bp2pss-ref.js"
refdir=${PSS2BP:-$HOME/proofs/pss2bp}

if [ ! -x "$CLI" ]; then
  echo "error: $CLI not found (cd lean && lake build bp2psscli)" >&2
  exit 2
fi
if [ ! -f "$refdir/common.js" ]; then
  echo "error: no common.js under $refdir; set PSS2BP to the directory holding it" >&2
  exit 2
fi
if ! command -v node >/dev/null 2>&1; then
  echo "error: node not found" >&2
  exit 2
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# ---------------------------------------------------------------------------
# THE CORPUS.  Shape, not volume.  Deep AND wide, and every family is here for a
# reason:
#   A  a chain of psi_1 under a psi_0, seven deep          -- depth
#   B  a SUM under a psi_0, two to four wide               -- the shape an earlier
#                                                             population missed
#   C  a sum under a psi_1, then under a psi_0             -- depth AND width
#   D  psi_0 nested inside psi_1, alternating              -- level alternation
#   E  level-0 and level-1 components side by side
#   F  top-level sums, descending, repeated, finite tail
#   G  the natural numbers -- where §71.2 documents bValA71 and Trans differing
# Candidates are then FILTERED by our own domain predicate, so what is compared is
# exactly the terms `bOnto85` speaks about.
# ---------------------------------------------------------------------------
python3 - > "$tmp/cand" <<'PY'
def s(*p): return "(" + ",".join(p) + ")" if len(p) > 1 else p[0]

O  = "D_1 0"                        # Omega
E0 = "D_0 D_1 0"                    # eps_0
Z0 = "D_0 D_1 D_1 0"                # zeta_0
out = []

# A  depth
chain = "0"
for _ in range(8):
    out.append("D_0 " + chain); chain = "D_1 " + chain

# B  a sum nested under a psi_0
w1 = [O, "D_1 D_1 0", "D_1 D_1 D_1 0", "D_1 D_1 D_1 D_1 0",
      "D_1 " + s(O, O), "D_1 D_0 D_1 0", "D_1 D_1 " + s(O, O)]
for n in (2, 3, 4, 5):
    out.append("D_0 " + s(*([O] * n)))
for a in w1:
    for b in w1:
        out.append("D_0 " + s(a, b))
out.append("D_0 " + s(w1[2], w1[1], w1[0]))
out.append("D_0 " + s(w1[3], w1[2], w1[1], w1[0]))
out.append("D_0 " + s(w1[6], w1[4], w1[1], w1[0], w1[0]))

# C  a sum under a psi_1
for a in w1:
    out.append("D_0 D_1 " + s(a, O))
    out.append("D_0 D_1 D_1 " + s(a, O))
out.append("D_0 D_1 " + s(E0, E0))
out.append("D_0 D_1 " + s(E0, E0, E0))
out.append("D_0 D_1 " + s(Z0, E0))
out.append("D_0 " + s("D_1 " + s(E0, E0), O))

# D  level alternation
out += ["D_0 D_1 " + E0, "D_0 D_1 D_1 " + E0, "D_0 D_1 " + Z0,
        "D_0 D_1 D_0 D_1 D_0 D_1 0", "D_0 D_1 D_1 D_0 D_1 0",
        "D_0 D_1 D_0 D_1 D_1 D_0 D_1 0"]

# E  mixed levels side by side
for a in (O, "D_1 D_1 0", "D_1 D_0 D_1 0"):
    for b in (E0, Z0, "D_0 0"):
        out.append("D_0 " + s(a, b))
out.append("D_0 " + s(O, E0, "D_0 0"))
out.append("D_0 " + s("D_1 D_1 0", O, E0, "D_0 0"))

# F  top-level sums
tops = ["D_0 " + x for x in ("D_1 D_1 D_1 0", "D_1 " + s(O, O), "D_1 D_1 0",
                             "D_1 D_0 D_1 0", O, "0")]
for i in range(len(tops)):
    for j in range(i, len(tops)):
        out.append(s(tops[i], tops[j]))
out.append(s(tops[0], tops[2], tops[4]))
out.append(s(tops[2], tops[4], tops[5], tops[5]))
out.append(s("D_0 D_1 " + s(E0, E0), tops[4]))

# G  the naturals
out += ["0", "1", "2", "3", "5"]

seen = set()
for t in out:
    if t not in seen:
        seen.add(t); print(t)
PY

"$CLI" --batch < "$tmp/cand" > "$tmp/cand-ours"
paste -d'\t' "$tmp/cand" "$tmp/cand-ours" | grep -P '\t= ' | cut -f1 > "$tmp/corpus"
ncand=$(wc -l < "$tmp/cand")
ncase=$(wc -l < "$tmp/corpus")

"$CLI" --batch < "$tmp/corpus" > "$tmp/ours"
node "$REF" --batch < "$tmp/corpus" > "$tmp/theirs"

echo "corpus: $ncase terms in bOnto85's domain (out of $ncand candidates)"
echo

# ---------------------------------------------------------------------------
# THE COMPARISON.  Not blind equality: §71.2 says `bValA71` is `bVal` without the
# leading-(0,0) exception -- "the Buchholz-side reading of vOf's 1 +" -- and the
# two differ on exactly the all-(0,0) matrices, i.e. the natural numbers.  So
#     theirs = ours              when the term is not a natural number
#     theirs = "(0,0)" ++ ours   when it is (ours is then all-(0,0))
# and a deviation from THAT is a mismatch.  Checking the offset is part of the
# check, not an excuse for it.
# ---------------------------------------------------------------------------
paste -d'\t' "$tmp/corpus" "$tmp/ours" "$tmp/theirs" | awk -F'\t' '
{ t=$1; o=$2; h=$3; raw=$3; sub(/^= /,"",o); sub(/^= /,"",h);
  if (raw ~ /^!/) { guard++; print t > "'"$tmp"'/guard"; next }
  allz=o; gsub(/\(0,0\)/,"",allz);
  if (allz=="") { want="(0,0)" o; kind="the documented 1 + on the naturals"; nat++ }
  else          { want=o;        kind="equality" }
  if (h==want) { ok++ }
  else { bad++;
         printf "MISMATCH  %s\n  ours  : [%s]\n  theirs: [%s]\n  wanted: [%s]  (%s)\n", t,o,h,want,kind }
}
END { printf "%d cases, %d mismatches\n", ok+bad+guard, bad;
      printf "  %d agreed (%d of them by the documented 1 + on the naturals)\n", ok, nat;
      printf "  %d the reference refused (see below)\n", guard+0 }' > "$tmp/report"
touch "$tmp/guard"
cat "$tmp/report"
mismatches=$(grep -c '^MISMATCH' "$tmp/report" || true)
nguard=$(wc -l < "$tmp/guard")

# ---------------------------------------------------------------------------
# The reference's refusals inside our domain, and WHY.
# ---------------------------------------------------------------------------
if [ "$nguard" -gt 0 ]; then
  echo
  echo "the reference refused these $nguard terms, which are inside bOnto85's domain:"
  while IFS= read -r t; do
    echo "  $t"
    echo "      TransRev's guard: $(node "$REF" --why "$t")"
  done < "$tmp/guard"
  echo
  echo "  Every one of these is the STANDARDNESS clause, not t < Omega.  There are two"
  echo "  possible causes and the probe below tells them apart -- it asks whether the"
  echo "  reference's G actually uses its level argument:"
  echo "      (D_0 D_1 0,D_0 D_1 0)  ->  $(node "$REF" --gindep "(D_0 D_1 0,D_0 D_1 0)")"
  echo "  A level-sensitive G would answer [] at level 5 and [D_1 0,0] at level 0."
  if node "$REF" --gindep "(D_0 D_1 0,D_0 D_1 0)" | grep -q "same=true"; then
    echo
    echo "  same=true, so \$PSS2BP/common.js PREDATES the upstream commit"
    echo "  'Fix G(a,u) for isStandardBuchholz'.  There G on a formal sum was written"
    echo "  a.flatMap(G), and Array.prototype.flatMap passes (element, INDEX, array),"
    echo "  so the level argument was replaced by the component's index.  That makes"
    echo "  isStandardBuchholz over-reject psi_1(eps_0*2) and -- when the offending"
    echo "  component is not the FIRST one -- under-reject psi_0(Omega+zeta_0), which"
    echo "  TransRev then accepts and dies on.  THIS IS NOT A FINDING: update"
    echo "  \$PSS2BP/common.js and re-run."
  else
    echo
    echo "  same=false, so the reference's G is the fixed one and the stale-copy"
    echo "  explanation does NOT apply.  This is a real disagreement between bInv85's"
    echo "  domain and TransRev's, and it is worth investigating on its own terms."
    echo "  Do not adjust the corpus to make it go away."
  fi
  echo "  Our GB (Trans/Dict.lean) passes the level down correctly, which is what"
  echo "  Buchholz's G_u(a_1+...+a_n) = union of G_u(a_i) says.  G is used ONLY by"
  echo "  isStandardBuchholz, which is used ONLY by TransRev, so Trans itself and"
  echo "  the acceptance record in Trans/Recal.lean are not touched by it."
fi

# ---------------------------------------------------------------------------
# NEGATIVE CONTROLS.  A check that cannot fail is not a check: each control
# declares what BOTH sides must do, and the script fails if they do something else.
# "ours"/"theirs" is `answers` or `refuses`.
# ---------------------------------------------------------------------------
ctl_bad=0
control() {           # <term> <ours: answers|refuses> <theirs: answers|refuses> <why>
  t=$1; wo=$2; wt=$3; why=$4
  if "$CLI" "$t" >/dev/null 2>&1; then go=answers; else go=refuses; fi
  if node "$REF" "$t" >/dev/null 2>&1; then gt=answers; else gt=refuses; fi
  if [ "$go" = "$wo" ] && [ "$gt" = "$wt" ]; then
    printf '  ok    %-26s ours %-7s theirs %-7s  %s\n' "$t" "$go" "$gt" "$why"
  else
    printf '  FAIL  %-26s ours %-7s theirs %-7s  (wanted ours %s, theirs %s)  %s\n' \
           "$t" "$go" "$gt" "$wo" "$wt" "$why"
    ctl_bad=$((ctl_bad + 1))
  fi
}

echo
echo "controls:"
control "D_0 D_1 0"            answers answers "positive control -- a check that only ever refuses is not a check"
control "D_1 0"                refuses refuses "Omega itself: standard, level 1, and the value of NO index (not_bValA71_om85)"
control "D_2 0"                refuses refuses "Omega_2: above Omega and above our level bound"
control "D_0 D_2 0"            refuses answers "standard and below Omega but carries a LEVEL-2 node -- outside ours, inside theirs"
control "D_0 D_1 D_2 0"        refuses refuses "sbadB85 = psi_0(psi_1(Omega_2)): not standard (§85.6)"
control "(D_0 0,D_0 D_1 0)"    refuses refuses "1 + eps_0: below Omega but an ASCENDING sum, so not standard"
control "D_0 (D_1 0,D_1 D_1 0)" refuses refuses "an ascending sum under a psi_0"
control "D_1 D_1 0"            refuses refuses "psi_1(Omega): head is D_1, so not below Omega"
control "D_0 (D_1 0,D_0 D_1 D_1 0)" refuses refuses "psi_0(Omega+zeta_0): both call it non-standard -- and this is the term the pre-fix G let through the guard, so it doubles as a check that \$PSS2BP is not stale"
echo
echo "The level-2 control is the domain difference in one line: ours is the"
echo "level-<=1 sub-region, theirs is everything standard below Omega, and ours is"
echo "a PROPER subset.  The head condition and t < Omega, however, are the same"
echo "condition on standard terms."

status=0
[ "$mismatches" -eq 0 ] || status=1
[ "$ctl_bad" -eq 0 ] || status=1
echo
if [ "$status" -eq 0 ]; then
  echo "bp2pss-check: OK — $ncase cases, $mismatches value mismatches, all controls as declared"
else
  echo "bp2pss-check: FAILED — $mismatches value mismatches, $ctl_bad controls off"
fi
exit "$status"
