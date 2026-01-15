.PHONY: all build check cache docs pdf clean

# Default target
all: check

# Get Mathlib cache. 
# This is useful when dependencies (lake-manifest.json) change.
cache:
	lake exe cache get

# Build the project
build:
	lake build

# Check axioms
# Depends on build implicitly via lake, but we can make it explicit if we want make to handle it.
# However, lake handles its own dependencies well.
check:
	lake exe check_axioms

# A target that ensures cache is fetched if lake-manifest.json is newer than a marker file
# This attempts to satisfy "getting cache on change of files"
.cache_marker: lake-manifest.json lean-toolchain
	lake exe cache get
	touch .cache_marker

# Use this target if you want automatic caching based on file changes
auto-build: .cache_marker
	lake build
	lake exe check_axioms

# Generate LaTeX documentation for all Lean files
docs:
	cd scripts && poetry run python3 generate_text_docs.py
	cd scripts && poetry run python3 graph_gen.py

# Compile proof.tex to PDF
# Runs xelatex twice to resolve cross-references and bookmarks
pdf:
	cd docs && xelatex proof.tex

# Clean build artifacts
clean:
	rm -f docs/proof.aux docs/proof.log docs/proof.out docs/proof.pdf .cache_marker
	rm -rf docs/*.tex
