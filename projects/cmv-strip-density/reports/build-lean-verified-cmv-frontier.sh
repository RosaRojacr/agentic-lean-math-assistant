#!/usr/bin/env bash
set -euo pipefail

here="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$here"
source="$here/lean-verified-cmv-frontier.md"
style="$here/lean-verified-cmv-cutoff.css"
html="$here/lean-verified-cmv-frontier.html"
pdf="$here/lean-verified-cmv-frontier.pdf"

pandoc "$source" \
  --from=markdown+fenced_divs \
  --standalone \
  --embed-resources \
  --citeproc \
  --mathml \
  --css="$style" \
  --metadata title-prefix="Lean-verified CMV frontier" \
  --output="$html"

chromium="${CHROMIUM:-}"
if [[ -z "$chromium" ]]; then
  for candidate in chromium-browser chromium google-chrome google-chrome-stable; do
    if command -v "$candidate" >/dev/null 2>&1; then
      chromium="$candidate"
      break
    fi
  done
fi

if [[ -z "$chromium" ]]; then
  printf 'No Chromium executable found; HTML was generated at %s\n' "$html" >&2
  exit 1
fi

"$chromium" \
  --headless \
  --disable-gpu \
  --no-sandbox \
  --no-pdf-header-footer \
  --print-to-pdf="$pdf" \
  "file://$html"

printf 'Generated %s and %s\n' "$html" "$pdf"
