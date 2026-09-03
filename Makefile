# dratify -- a DRAT/DRUP proof checker with no dependencies.
#
# The package lives under src/, so it has to be on the path to be imported
# without installing. Every target below does that for you; running
# `python -m unittest discover -s tests` on its own will fail with import
# errors, which is why this file exists.
PYTHON ?= python3
export PYTHONPATH := src

.PHONY: help test test-verbose test-native coverage fuzz native lint gate clean

help:
	@echo "make test      -- run the full suite, no Rust and no install needed"
	@echo "make test-native-- same, with a native checker installed (see below)"
	@echo "make coverage  -- statement coverage via the stdlib trace module"
	@echo "make fuzz      -- randomised differential run; SEED=n to reproduce"
	@echo "make native    -- install cdclkit-native, which supplies the Rust checker"
	@echo "make lint      -- cargo clippy and cargo test on the crate"
	@echo "make gate      -- everything that must pass before a commit"

test:
	$(PYTHON) -m unittest discover -s tests

test-verbose:
	$(PYTHON) -m unittest discover -s tests -v

# The Rust checker is not published under this name: cdclkit-native embeds this
# crate and registers itself, so a proof checker never needs a toolchain.
native:
	$(PYTHON) -m pip install cdclkit-native

# Fails loudly if the comparison skipped. A differential test that silently
# disables itself is how the agreement claim went untested for three releases.
test-native:
	@$(PYTHON) -c "import dratify; assert dratify.native_available(), \
	 'no native checker; run make native'"
	$(PYTHON) -m unittest discover -s tests -v

coverage:
	$(PYTHON) tests/coverage_report.py

fuzz:
	$(PYTHON) tests/fuzz.py $(if $(SEED),--seed $(SEED),)

lint:
	cd rust && cargo test --release
	cd rust && cargo clippy --all-targets -- -D warnings

gate: test coverage lint

clean:
	rm -rf build dist src/*.egg-info .coverage
	find . -name __pycache__ -type d -prune -exec rm -rf {} +
