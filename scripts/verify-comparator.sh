#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

for command in bwrap lake lean python3; do
  command -v "$command" >/dev/null || {
    echo "error: $command is required for Linux Comparator verification" >&2
    exit 1
  }
done

prefix=$(lean --print-prefix)
config=$(mktemp)
trap 'rm -f "$config"' EXIT

# Match Palomar's independent-kernel check without adding unaccepted fields
# to the submitted comparator.json. The toolchain supplies both checkers.
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
from pathlib import Path
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(Path(source).read_text(encoding="utf-8"))
config["external_kernels"] = {
    "nanoda": [str(Path(prefix) / "bin" / "nanoda_bin")],
    "con-ron": [str(Path(prefix) / "bin" / "con-ron")],
}
Path(destination).write_text(json.dumps(config) + "\n", encoding="utf-8")
PY

lake comparator --config "$config"
