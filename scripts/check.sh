#!/usr/bin/env bash
# Enforce discipline: every row of residuals.csv must agree with the code.
#   COMPILE  verified by `lake build`
#   OPEN     the theorem carries a `sorry -- ID` marker
#   PROVEN   no marker, and `#print axioms` does not mention sorryAx
# Every `sorry -- ID` marker in the code must also have a row. See residuals.csv.
set -euo pipefail

cd "$(dirname "$0")/.."

echo "=== Building ==="
lake build

# search our own .lean files, not the packages under .lake
grep_code() { grep -rE --include='*.lean' --exclude-dir=.lake "$@" .; }

echo "=== Checking residuals ==="
failures=0
ids=()

# only the first four columns matter here, so commas in the description are harmless
while IFS=',' read -r id status file theorem _; do
  [[ "$id" == "id" || -z "$id" ]] && continue
  ids+=("$id")
  # boundary so that R-1 does not match R-10
  marker="sorry -- ${id}([^A-Za-z0-9-]|\$)"

  case "$status" in
    COMPILE)
      # verified by lake build above
      ;;
    OPEN)
      if ! grep_code -q "$marker"; then
        echo "FAIL: $id OPEN but no 'sorry -- $id' in code"
        failures=$((failures + 1))
      fi
      ;;
    PROVEN)
      if grep_code -q "$marker"; then
        echo "FAIL: $id PROVEN but 'sorry -- $id' still in code"
        failures=$((failures + 1))
        continue
      fi
      mod="${file%.lean}"
      opens="open Semioverse"
      [[ "$mod" == "Alignment" ]] && opens="open Semioverse Semioverse.Alignment"
      result=$(printf 'import %s\n%s\n#print axioms %s\n' "$mod" "$opens" "$theorem" \
               | lake env lean --stdin 2>&1 || true)
      if echo "$result" | grep -q "sorryAx"; then
        echo "FAIL: $id PROVEN but $theorem uses sorryAx"
        failures=$((failures + 1))
      elif ! echo "$result" | grep -qE "depends on axioms|does not depend on any axioms"; then
        echo "FAIL: $id could not check axioms of $theorem:"
        echo "$result" | head -5
        failures=$((failures + 1))
      fi
      ;;
    *)
      echo "FAIL: $id has unknown status '$status'"
      failures=$((failures + 1))
      ;;
  esac
done < residuals.csv

# markers in the code with no row in the ledger
for m in $(grep_code -ohE 'sorry -- R-[A-Za-z0-9-]+' | sed 's/^sorry -- //' | sort -u || true); do
  found=0
  for i in "${ids[@]}"; do [[ "$i" == "$m" ]] && found=1; done
  if [[ $found -eq 0 ]]; then
    echo "FAIL: 'sorry -- $m' in code but no row in residuals.csv"
    failures=$((failures + 1))
  fi
done

if [ "$failures" -gt 0 ]; then
  echo "=== $failures failures ==="
  exit 1
fi

echo "=== All residuals consistent ==="
