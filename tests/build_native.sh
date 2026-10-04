#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
#
# Build cdclkit-native against THIS checkout's Rust crate, and install it.
#
# This package has no Python binding of its own; the Rust checker reaches
# Python through cdclkit-native, which embeds the crate. CI used to
# `pip install cdclkit-native` from PyPI, which embeds whatever crate version
# was last *released* -- so a change to rust/ was never compared against the
# Python checker until after it shipped. Building with a [patch] pointing at
# rust/ compares the two implementations as they are in this commit.
#
# Needs: git, a Rust toolchain, network access. Installs into the current
# Python environment.
set -euo pipefail

here=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

git clone --quiet --depth 1 https://github.com/carlok/cdclkit.git "$work/cdclkit"
cat >> "$work/cdclkit/native/Cargo.toml" <<TOML

[patch.crates-io]
dratify = { path = "$here/rust" }
TOML

# Cargo.lock pins the registry's dratify, and a [patch] whose version differs
# from the locked one is silently *unused* -- Cargo only warns. Re-resolve.
(cd "$work/cdclkit/native" && cargo update --quiet -p dratify)

# Prove the crate that will be built is this one, not the registry's. Without
# this check the first version of this script built against crates.io and
# reported success.
pkgid=$(cd "$work/cdclkit/native" && cargo pkgid dratify)
case "$pkgid" in
  path+file://"$here"/rust*) ;;
  *) echo "error: dratify resolves to $pkgid, not $here/rust" >&2; exit 1 ;;
esac

python -m pip install --quiet maturin
(cd "$work/cdclkit/native" && maturin build --release --out "$work/dist" >/dev/null)
python -m pip install --quiet --force-reinstall --no-deps "$work"/dist/cdclkit_native-*.whl
python -c "import cdclkit_native; print('cdclkit_native built against $pkgid')"
