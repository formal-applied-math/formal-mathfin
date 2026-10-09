# arXiv papers

Sources for the three papers that describe this library at release `v1.5.0` (`main` at
`c0180c8`). They live on this branch rather than on `main`, which holds only the library.

| Paper | arXiv | This revision | Source | PDF |
|---|---|---|---|---|
| The Fundamental Theorem of Asset Pricing, Formalized in Lean 4 | 2606.28990 | v2 | [`ftap/ftap.tex`](ftap/ftap.tex) | [`ftap/ftap.pdf`](ftap/ftap.pdf) |
| A Machine-Checked Itô Calculus for Brownian Motion | 2606.15089 | v3 | [`ito/ito.tex`](ito/ito.tex) | [`ito/ito.pdf`](ito/ito.pdf) |
| A Formally Verified Library of Mathematical Finance in Lean 4 | 2606.01356 | v4 | [`library/library.tex`](library/library.tex) | [`library/library.pdf`](library/library.pdf) |

## Building

```sh
papers/build.sh
```

The script needs pdflatex (TeX Live 2023 or later). It writes each PDF next to its source and
one arXiv tarball per paper to `papers/dist/` (ignored by git). Each tarball holds the `.tex`
and the shared style `common/mathfin-paper.sty`. The script also regenerates
[`arxiv-submission-notes.md`](arxiv-submission-notes.md): each abstract as arXiv-ready text,
checked against the 1,920-character limit, and a Comments field.

## How the papers were checked

- Every claim was read against the Lean statement it cites, not against the docstring or the
  textbook theorem.
- Every `\lean{…}` name was checked to resolve to a declaration.
- The library paper's area tables were audited claim by claim.
- The papers describe only what is in `main` at the release: no pull requests, branches or
  unmerged work.

What this exercise showed about the repository is recorded on the fix branch as
`docs/paper-revision-review-2026-10-09.md`.

## Style

`common/mathfin-paper.sty` is shared by all three papers. It provides:
- Palatino text and math;
- a `listings` language for Lean with Unicode mappings, and a `leancode` environment that keeps
  listings unbroken;
- `\lean{}` and `\file{}` for identifiers that break at `_`, `.` and `/`;
- `\bench{}` for benchmark ids, which break at hyphens.

The bibliographies are inline `thebibliography` blocks, so no `.bbl` file is needed.
