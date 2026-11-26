# What the literature adds: the atlas first

Status: adopted 2026-11-25 (decisions at the end).

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
   - For the arXiv papers, OpenAlex indexes them under their arXiv DOIs (`10.48550/arXiv.<id>`),
     so both corpora get the same record: abstract, topics, keywords, `referenced_works`,
     `cited_by_count`. An arXiv paper is looked up on its own, which is free. A batched lookup
     cannot map the answer back to the paper when OpenAlex returns the published version under
     another DOI. The OpenAlex corpus is fetched in batches of 100, about a cent in all.
     OpenAlex data is CC0.
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
3. **Classification.** First tried as written here: a paper's title and abstract scored against
   every cell profile by TF-IDF similarity. It placed 34% of the validation papers where the
   labellers did; local sentence embeddings matched to the library's pieces placed 22–29%. The
   profiles describe what the library has formalised, not the region of the field: `risk/insurance`
   is thin in the library and large in the corpus. So the cells are learned instead
   (`mathfin_corpus.place`, 2026-11-26):
   - **Training labels:** 2,000 papers, each labelled once by an agent that read the title and the
     full abstract against the cell list. `NONE` (outside every cell) is a class like the others.
   - **Features:** the paper's sentence embedding, its similarity to an agent-written description
     of each cell's field, and TF-IDF over its title and abstract.
   - **Model:** balanced logistic regression, its two settings chosen by cross-validation on the
     training labels alone. The best cell is kept, with the runner-up when its probability is at
     least half the best.
4. **Validation, with no hand labelling.**
   - **Ground truth from the library's own citations.** Every `references.bib` entry is cited by a
     module, and every module sits in a cell. When a cited paper is in the corpus, its cell is
     known without anyone judging it. Only 14 cited sources turned out to be corpus papers, too
     few to score against, so these labels check the classifier but do not carry the bar.
   - **Two independent agent labellers** labelled a held-out sample of 297 papers. They got
     different instructions, and neither saw the other's answer or the classifier's. A third agent
     settled the 34 papers they did not share. They chose the same first cell for 80% of the
     papers, which is the ceiling any classifier can be measured to.
   - The classifier must reach 70% against these held-out labels: its first cell is one of the
     paper's gold cells. The training labels never include a held-out paper. The atlas reports
     agreement per cell, measured by cross-validation on the training labels, and shows a cell
     under 70% with that warning, not hidden.
   - **Measured (2026-11-26).** Three embeddings were tried: `bge-small`, `bge-base`, and both
     together. Cross-validation on the training labels prefers `bge-base` and both together
     equally (1,353 and 1,352 of 2,000 right) over `bge-small` (1,330). On the held-out sample,
     the first cell is a gold cell for 68% (`bge-base`) and 71% (both) of the papers, and one of
     the first two for 86%. With 297 papers that difference is noise (one standard error is 2.7
     points). The classifier sits at the bar, under the labellers' own 80%. The atlas uses both
     embeddings.
   - **What the atlas publishes is a count, and counts are steadier than placements.** Under
     cross-validation, 7% of the training papers would move between cell totals. The errors are
     not even, though: small cells are undercounted (`valuation/trees` 7 predicted against 20
     labelled, `probability/discrete` 3 against 13). 20 of the 33 cells, almost all small ones,
     have recall under 70%. The atlas marks them.

   This is enough because an atlas error misorders a roadmap and asserts no theorem.

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
   - Body and bibliography pages are split (done 2026-11-25; on a sample of 600 papers about 10%
     show no reference list: short notes, chapters, scans without text).
   - OpenAlex metadata is fetched for every paper (`mathfin_corpus.metadata`).
   - Exit: every one of the 24,147 papers has a metadata record or is listed as missing one.
2. **The classifier.** Cell profiles, the labels, the trained classifier and the held-out sample.
   - Exit: agreement is reported per cell, and is at least 70% on the held-out sample.
3. **The atlas.** `docs/atlas.json`, the Literature layer, and a dated note in `docs/roadmap.md`
   naming the three cells with the largest gap.
   - Exit: the layer renders on the docs site, and the roadmap note is written.
4. **Literature trails** on the 180 proved nodes. For each: the source the node's docstring cites,
   matched to its OpenAlex record, the papers in the corpus that cite it, and its generalisations.
   A generalisation is a citing paper whose abstract restates the result under weaker hypotheses.
   An agent judges this, and the trail marks it as that agent's reading.
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

## Decisions (2026-11-25)

1. **Publishing: yes, at milestone 3, once validation passes.** `docs/atlas.json` and the
   Literature layer are bibliographic metadata, and OpenAlex's data is CC0. Each cell card shows its
   measured agreement, and the page states the corpus's blind spots. Nothing is published before
   the classifier is checked.
2. **Validation: no hand labelling.** Citation-derived labels are the ground truth, and two
   independent agent labellers with a third to settle cover the rest (above).
3. **Order: the atlas (milestones 1–3) first, then the cátedra's Phase 0 and MF-OP-017, then the
   literature trails.** The atlas is short and needs only the CPU. MF-OP-017 is the strongest
   result on the table and needs neither the GPU nor the corpus. The trails improve the docs site,
   nothing waits on them, and their generalisation claims read better from Marker's LaTeX.
