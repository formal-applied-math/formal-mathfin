# What the literature adds: the atlas first

Status: proposed 2026-11-25.

## The two maps

The library keeps a map of what it has proved: 37 taxonomy cells (`docs/taxonomy.toml`), 180
proved blueprint nodes, 115 frontier nodes, 906 corpus entries, 210 bibliography entries. Since
November 2026 there is also a map of what the field knows: a local corpus of 24,147 papers.
11,872 are the q-fin arXiv papers; 12,275 are open-access papers from journals, repositories and
theses, found through OpenAlex. The corpus has full text for 758,723 pages, kept on one machine
by the private `mathfin-corpus` repo and never committed: arXiv and most publishers allow keeping
papers for research, not redistributing them.

Joining the two maps is the point. Every use below lands in an object the library already has:
cells in `taxonomy.toml`, nodes in the blueprint, sources in `references.bib`, tasks in issues,
problems in `docs/research-problems/`, rows in the Hugging Face export. Nothing becomes a second
map beside the first (CLAUDE.md: no parallel objects).

## The uses, in order

| Use | Lands in | Needs formula OCR? |
|---|---|---|
| 1. **Atlas**: how much the field says in each cell, and how much the library covers | a layer of the program tree; the roadmap | no |
| 2. **Literature trails**: for each proved node, where it was first proved, who generalised it, who cites it | the docs site's node pages; `references.bib` | no |
| 3. **Blueprint candidates**: the named theorems and definitions of a cell's founding papers | frontier nodes | yes |
| 4. **Issues and plans**: a candidate with its statement quoted, its page, its `Blueprint:` line | issues; a plan per cell | yes |
| 5. **Open problems**: the catalogue's Scout over full text | `docs/research-problems/` | partly |
| 6. **Teaching**: a reading path per cell (survey, classic, recent) beside the library's proofs | the beginners' manual; the docs site | no |
| 7. **Data for AI**: informal statement (paper, page, LaTeX) paired with its Lean statement; retrieval for the cátedra's chairs; tasks for the prover benchmark | the Hugging Face export; the cátedra | yes |

The atlas comes first because it orders the rest. It says which cells the field is dense in and
the library thin in, so that is where trails, candidates and issues pay most. It needs no formula
OCR (Marker is waiting for the GPU), only metadata, abstracts and the citation graph.

## The atlas

### What it measures

For each cell:

- **Field weight:** how many papers the cell holds, weighted by citations within the corpus, and
  how fast the count grows by year.
- **Founding works:** the papers most cited by the corpus's own papers in that cell. That is
  in-corpus citation count, not global citation count. These are what the field rests on.
- **Library coverage:** proved blueprint nodes, corpus entries and modules in the cell, all read
  from what the build already records (`blueprint_nodes.json`, the corpus entries' `cell`, the
  layers).
- **Gap:** field weight against library coverage. A dense, thinly covered cell is a roadmap
  candidate. It is not a verdict: some cells are dense for empirical work the library does not
  formalise, and the per-cell reading says which.

### How a paper gets a cell

1. **Metadata.**
   - The OpenAlex corpus already has each work's topics.
   - For the arXiv papers, OpenAlex indexes them under their arXiv DOIs (`10.48550/arXiv.<id>`).
     So one batched listing gives the same record for both corpora: abstract, topics, keywords,
     `referenced_works`, `cited_by_count`.
   - Batches of 100 DOIs cost about one cent for all 11,872. OpenAlex data is CC0.
   - OpenAlex often maps an arXiv DOI to the published version, with that version's citations,
     but not always: in a three-paper test, one arXiv record stood alone with zero citations. An
     unmatched arXiv record is therefore matched to its journal version by title and authors
     before citations are counted. Otherwise a founding paper could count as uncited.
2. **A cell profile from the library's own words.** Each cell is described by:
   - its blurb;
   - the docstrings of the modules in it, read from the declaration index;
   - the descriptions of its corpus entries;
   - its JEL and MSC codes from `docs/subjects.toml`.

   The library describes its cells better than any outside vocabulary does, so the profile comes
   from the library itself.
3. **Classification.** A paper's title and abstract are scored against every cell profile by
   TF-IDF similarity, and its OpenAlex topics break ties. The best cell is kept, with a second
   when its score is close. This is deterministic, runs on the CPU and is cheap. If it fails the
   validation in step 4, the next step is local sentence embeddings, once the GPU is free.
4. **Validation.** A sample of 300 papers, stratified by cell, is labelled by agents that see
   only the cell list and the abstract. The maintainer checks a third of those labels. The atlas
   reports the classifier's agreement with the labels, per cell. A cell with agreement under 70%
   is shown with that warning, not hidden.

Papers no cell fits are counted and listed, not forced into one. A cluster of them in one area is
the case for a new cell, which the taxonomy's own rules then judge.

### The index, cleaned for counting

Searches in the current index are crowded by reference lists. For one query, all four top hits
were bibliography entries citing the same paper. The index marks each page as body or
bibliography: the page carrying the `References` heading, and every page after it, are
bibliography. Search and every count then use body pages only, unless asked. This is a
`mathfin-corpus` change, made before the atlas counts anything.

### What is published, and where

- **Private, in `mathfin-corpus`:** the per-paper table (id, cells, scores, in-corpus citations).
  Titles and identifiers are metadata, but they stay with the corpus that produced them.
- **Public, in this repo:** `docs/atlas.json`, holding per-cell numbers (field weight, growth,
  coverage, gap) and the ten founding works of each cell, by DOI and title. Its generator
  records the corpus snapshot it read.
- **On the docs site:** a **Literature** layer on the program tree, beside Gaps, Future work,
  Open problems and Leaves. It shades each cell by field weight and outlines it by gap. A cell's
  card lists its founding works and says how much of each is formalised.

No paper text is published. The founding-work lists are bibliographic metadata.

## Milestones

1. **The corpus, ready for counting.**
   - The retry pass is done.
   - Body and bibliography pages are split.
   - OpenAlex metadata is fetched for the arXiv papers.
   - Exit: every one of the 24,147 papers has a metadata record or is listed as missing one.
2. **The classifier.** Cell profiles, TF-IDF scoring and the validated sample.
   - Exit: agreement is reported per cell, and is at least 70% over the corpus.
3. **The atlas.** `docs/atlas.json`, the Literature layer, and a dated note in `docs/roadmap.md`
   naming the three cells with the largest gap.
   - Exit: the layer renders on the docs site, and the roadmap note is written.
4. **Literature trails** on the 180 proved nodes. For each: the source the node's docstring cites,
   matched to its OpenAlex record, the papers in the corpus that cite it, and its generalisations.
   A generalisation is a citing paper whose abstract restates the result under weaker hypotheses;
   an agent judges this, and the maintainer checks a sample.
   - Exit: every proved node shows its trail, or "no source in the corpus".
5. **Candidates, issues, teaching and data.** These come after Marker has converted the papers of
   the cells the atlas ranks first, and get a spec of their own.

## Honesty rules

- A classification is an estimate. Every per-cell number carries the agreement measured for that
  cell.
- A founding work is founding *within this corpus*. The corpus misses closed papers and most of
  SSRN, and the atlas says so on its page.
- A generalisation claim in a trail is an agent's reading of an abstract, marked as such, until
  someone checks the paper.
- The prose rule applies: a cell card says what the library proves there, read from the
  statements, not from the titles of the papers it sits beside.

## Decisions for the maintainer

1. **Publishing:** the public `docs/atlas.json` and the Literature layer. Both are metadata only,
   but they are outward-facing.
2. **Validation:** whether 300 agent labels with a third checked by hand is enough, or whether the
   maintainer checks all of them.
3. **Order after the atlas:** literature trails (milestone 4) before or after the cátedra's
   Phase 1 (MF-OP-017).
