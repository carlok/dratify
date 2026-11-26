#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
#
# Run the whole suite with the Rust checker present, and fail if any test that
# needs it skipped.
#
# Every native test class skips with "no native checker installed" when
# cdclkit_native cannot be imported. CI used to run only the two differential
# modules with the checker present, so the native halves of the 0.1.11 fix
# tests skipped on every run and nothing noticed. This runs everything, and
# only that skip reason fails it: a missing python-sat or an old setuptools is
# another job's business.
#
# Needs cdclkit_native in the current Python: `make native` builds it against
# this checkout's rust/.
set -euo pipefail

py=${PYTHON:-python3}
here=$(cd "$(dirname "$0")/.." && pwd)
log=$(mktemp)
trap 'rm -f "$log"' EXIT

if ! "$py" -c "import cdclkit_native" 2>/dev/null; then
  echo "error: cdclkit_native is not importable from $py; run make native" >&2
  exit 1
fi

cd "$here"
status=0
PYTHONPATH=src "$py" -m unittest discover -s tests -v 2>&1 | tee "$log" || status=$?

if [ "$status" -ne 0 ] || ! grep -q "^OK" "$log"; then
  echo "error: the suite failed" >&2
  exit 1
fi

skipped=$(grep -c "skipped 'no native checker" "$log" || true)
if [ "$skipped" -ne 0 ]; then
  echo "::error::$skipped native tests skipped -- the Rust checker was not compared" >&2
  exit 1
fi
echo "native suite: OK, no native test skipped"
