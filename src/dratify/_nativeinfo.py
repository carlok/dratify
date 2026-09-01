# SPDX-License-Identifier: Apache-2.0
"""Availability of the optional Rust checker."""

from __future__ import annotations

#: Raised on engine="native" with nothing registered. This is the one message a
#: user sees when the fast path is missing, so it names the route that actually
#: works -- it used to say only "not yet published as a Python wheel", which
#: pointed away from the fix.
BUILD_HINT = (
    "engine='native' was requested but no native checker is available. "
    "This package ships no compiled extension of its own; install one that "
    "registers itself:\n"
    "    pip install \"cdclkit[native]\"\n"
    "or hand your own to dratify.register_native(module). "
    "Otherwise use engine='python' or engine='auto' -- the pure-Python "
    "checker is complete, and it is the independent implementation that "
    "makes agreement meaningful."
)


def available() -> bool:
    """True when a native checker is importable or has been registered."""
    from .proof import _native_module
    return _native_module() is not None
