# SPDX-License-Identifier: Apache-2.0
"""Availability of the optional Rust checker."""

from __future__ import annotations

BUILD_HINT = (
    "engine='native' was requested but the Rust checker is not installed. "
    "The Rust accelerator is not yet published as a Python wheel; use "
    "engine='python' or engine='auto' "
    "(the pure-Python checker is complete and is never going away -- it is "
    "the independent implementation that makes agreement meaningful)."
)


def available() -> bool:
    """True when the Rust checker can be imported."""
    try:
        import sable_native
    except ImportError:
        return False
    return hasattr(sable_native, "check_proof")
