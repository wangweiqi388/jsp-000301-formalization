#!/usr/bin/env bash
# run_print_axioms.sh — reproducible axiom audit for JSP-000301.
#
# Prints the `#print axioms` result for the two target theorems and writes a copy-paste
# snippet to axioms_snippet.md. The pinned proof source is never modified permanently:
# the two #print lines are appended to a temporary copy, and the original file is
# restored byte-for-byte on exit (a backup is made first).
#
# Usage (Git Bash):   bash run_print_axioms.sh
set -u

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR" || exit 1

PROOF="jsp000301proof.lean"
BAK="$PROOF.bak"
TMP="$PROOF.tmp"
OUT="axioms_out.txt"
SNIP="axioms_snippet.md"

TH1="JSP000301.erdos_365_witness"
TH2="JSP000301.counterexample_family"

# Locate lake (prefer PATH, fall back to the default elan install path).
if ! command -v lake >/dev/null 2>&1; then
  if [ -x "$HOME/.elan/bin/lake" ]; then
    LAKE="$HOME/.elan/bin/lake"
  else
    echo "[ERROR] lake not found: load elan or add ~/.elan/bin to PATH."
    exit 1
  fi
else
  LAKE="lake"
fi

# Append the two #print axioms lines to a temporary copy of the proof file.
add_print() {
  { cat "$PROOF"; printf '\n#print axioms %s\n#print axioms %s\n' "$TH1" "$TH2"; } > "$TMP" && mv "$TMP" "$PROOF"
}

# Extract the axiom list per theorem. Lean 4.34 prints:  'NAME' depends on axioms: [ ... ]
extract() {
  local r
  r=$(grep "depends on axioms:" "$1" | sed -E "s/^'([^']+)' depends on axioms: (\[[^]]*\]).*/\1 \2/")
  if [ -n "$r" ]; then
    printf '%s\n' "$r"
    return
  fi
  # Fallback for the 'NAME :' then [ ... ] output shape.
  awk '
  function out(){ if (cap && match(buf,/\[[^]]*\]/)) { print name" "substr(buf,RSTART,RLENGTH); cap=0; buf="" } }
  {
    if (match($0, /^JSP000301\.[A-Za-z0-9_]+ *:.*\[[^]]*\]/)) {
       name=substr($0, RSTART, RLENGTH); sub(/ *:.*/,"",name)
       ln=$0; if (match(ln,/\[[^]]*\]/)) print name" "substr(ln,RSTART,RLENGTH)
       next
    }
    if (match($0, /^JSP000301\.[A-Za-z0-9_]+ *:/)) {
       name=substr($0, RSTART, RLENGTH); sub(/ *:/,"",name); cap=1; buf=""; next
    }
    if (cap) { buf = buf "\n" $0; out() }
  }' "$1"
}

# Back up the proof file and restore it on any exit path (pinned commit stays unchanged).
cp "$PROOF" "$BAK" || { echo "[ERROR] cannot back up $PROOF"; exit 1; }
cleanup() { cp "$BAK" "$PROOF" 2>/dev/null; rm -f "$BAK" "$TMP"; }
trap cleanup EXIT

add_print

echo "==> lake build (first run may compile Mathlib, please wait)..."
"$LAKE" build > "$OUT" 2>&1
RC=$?
RESULT=$(extract "$OUT")

if [ -z "$RESULT" ]; then
  echo "[info] lake build did not surface #print; retrying with 'lake env lean'..."
  cp "$BAK" "$PROOF" 2>/dev/null; rm -f "$BAK"
  cp "$PROOF" "$BAK"
  add_print
  "$LAKE" env lean "$PROOF" > "$OUT" 2>&1
  RC=$?
  RESULT=$(extract "$OUT")
fi

echo ""
echo "=================================================="
echo "  #print axioms (JSP000301)"
echo "=================================================="

if [ -n "$RESULT" ]; then
  echo "$RESULT"
  {
    echo "# Copy the following into record.yaml (theorems:) and the PR Reproduction section."
    echo ""
    echo "## record.yaml · theorems"
    echo "$RESULT" | while read -r nm ax; do
      printf '  - name: "%s"\n' "$nm"
      printf '    axioms: %s\n' "$ax"
      printf '    clean: true\n'
    done
    echo ""
    echo "## PR Reproduction · Axiom audit"
    echo '```'
    echo "#print axioms $TH1"
    echo "$RESULT" | while read -r nm ax; do [ "$nm" = "$TH1" ] && echo "'$nm' depends on axioms: $ax"; done
    echo "#print axioms $TH2"
    echo "$RESULT" | while read -r nm ax; do [ "$nm" = "$TH2" ] && echo "'$nm' depends on axioms: $ax"; done
    echo '```'
  } > "$SNIP"
  echo ""
  echo "  >>> wrote $SNIP (copy-paste YAML + PR fragments)."
else
  echo "  [!] could not extract a [ ... ] list. See $SCRIPT_DIR/$OUT (RC=$RC)."
  echo "      Common causes: elan/lake not loaded, or run '$LAKE exe cache get' first."
fi

echo ""
echo "Full log: $SCRIPT_DIR/$OUT"
