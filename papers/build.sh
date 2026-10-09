#!/bin/sh
# Build the three papers and their arXiv tarballs.
#
#   papers/build.sh
#
# Needs pdflatex (TeX Live 2023 or later). Writes each PDF next to its source,
# one arXiv tarball per paper (the .tex plus mathfin-paper.sty) to papers/dist/
# (ignored by git), and regenerates arxiv-submission-notes.md.
set -eu
cd "$(dirname "$0")"
mkdir -p dist
for p in ftap ito library; do
    (
        cd "$p"
        for _ in 1 2 3; do
            TEXINPUTS=../common: pdflatex -interaction=nonstopmode -halt-on-error "$p.tex" >/dev/null \
                || { tail -20 "$p.log"; exit 1; }
        done
    )
    rm -rf "dist/$p-src"
    mkdir -p "dist/$p-src"
    cp "$p/$p.tex" common/mathfin-paper.sty "dist/$p-src/"
    tar -czf "dist/$p-arxiv.tar.gz" -C "dist/$p-src" .
    echo "$p: dist/$p-arxiv.tar.gz"
done
python3 make_notes.py
