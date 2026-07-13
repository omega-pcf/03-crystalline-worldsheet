# TODO — Limitations, Future Work & Open Questions

This document records what the build does **not** verify, the cosmetic
blemishes visible in the current `build/document-v0.1.0.pdf`, and the
concrete next steps. It is the hand-off note for the next editorial round.

---

## How the bibliography pipeline works now

The single source of truth is **`citation.csl.json`** (76 hand-curated CSL
entries). `pnpm run build` runs `scripts/build.ts`, which calls
`scripts/tasks/citation.ts`:

1. `citation.csl.json` → `src/bibliography.bib`   (via `@citation-js/plugin-bibtex`)
2. `citation.csl.json` → `CITATION.cff` references (via `@citation-js/plugin-cff`)
3. `CITATION.cff`      → `.zenodo.json`            (native mapping in `citation.ts`)
4. docker `pdflatex` × 3 + `biber` → `build/document-v<version>.pdf`

Two non-obvious `citation.ts` settings make this work:

- `plugins.config.get('@bibtex').format.useIdAsLabel = true`
  Without it, citation-js generates `AuthorYearWord` keys *and* emits an
  invalid trailing comma after the entry-opening brace
  (`@article{Key},`), which biber rejects. With it, the CSL `id`
  becomes the BibTeX key and the opener is valid
  (`@article{Strominger01,`). This is the documented option — not a heuristic.
- CSL `type: "article"` for the companion-paper stubs (`F1`, `HP`, `Corr`).
  citation-js maps CSL `preprint` / `misc` / `report` to CFF types that the
  CFF 1.2.0 schema rejects (missing `type` field). `article` maps cleanly.

**Rule:** to change the bibliography, edit `citation.csl.json` and re-run
`pnpm run build`. Do not hand-edit `src/bibliography.bib`, `CITATION.cff`,
or `.zenodo.json` — they are regenerated every build.

---

## 1. NOT verified by this build

These are out of scope of the shell-wiring pass and are the natural starting
point for a separate editorial task:

- **Each citekey resolves to the correct publication.** The CSL `id`s match
  the `\bibitem{key}` keys in the source `src/chapters/references.tex`, so
  every `\cite{key}` in the chapter files resolves. But *which paper* each
  key points to (e.g. that `Maldacena98` really is Adv. Theor. Math. Phys.
  **2** (1998) 231, not a different Maldacena 1998 paper) has not been
  cross-checked against doi.org / arXiv.
- **Each DOI / arXiv ID is real and points to the right paper.** The URLs
  are syntactically valid; none have been HEAD-checked.
- **Each volume / page / article-number is exact.** Hand-transcribed from
  the source `\bibitem{}` blocks; transcription errors are possible.
- **Factual accuracy of the prose** (the physics, the mathematics, the
  attributions to M-theory / F₁ / AdS-CFT literature). Pure editorial
  review.
- **The Schiller translation** in Appendix `app:epigraph-en` is *a* standard
  English rendering; confirm it against the translator you want to credit.

---

## 2. Cosmetic blemishes in the current PDF (all in the bibliography)

None block compilation. All are fixable by editing `citation.csl.json`.

| # | Entry | Symptom | Fix (in `citation.csl.json`) |
|---|-------|---------|------------------------------|
| 1 | `Cooper2026`, `Elvang2026` | `In: ()` — empty year slot | These are arXiv-only preprints whose year lives inside the arXiv id (`2602.12265` → 2026, `2601.11705` → 2026). citation-js does not derive a year from the arXiv id. Add `"issued": {"date-parts": [[2026]]}` explicitly. |
| 2 | `Schreiber13cohesive` | Title renders as `Differential cohomology in a cohesive -topos` — the `∞` (U+221E) was silently dropped by citation-js's `asciiOnly` conversion. | Replace the `∞` in the title with `{\textinfinity}` won't help (citation-js strips it). Either accept the loss or rephrase the title in the CSL to avoid the symbol. The original paper's title does contain ∞, so the loss is a known citation-js limitation. |
| 3 | `Kiely26` | Title is the placeholder `(title to be confirmed against the publication)`. The source `\bibitem{}` had no `\emph{...}` title. | Look up the actual paper title (Phys. Rev. A **113** (2026) 022403) and replace the placeholder string. |
| 4 | ~13 arXiv-only entries | `In: (YEAR).` with no volume — correct for preprints, but visually sparse. | Cosmetic only; preprints genuinely have no volume. No action needed unless a journal style requires it. |
| 5 | `Santos2020` | DOI renders the underscore as `\_28\_4`. | Acceptable (the hyperlink target is correct). If undesired, the DOI field can be moved into a `URL` field instead. |

Everything else renders correctly: 0 literal tildes, Greek letters
(`α`, `χ`) render in math mode, the Schiller epigraph and its English
translation are present, all 76 `\cite{}` calls resolve.

---

## 3. Pipeline / shell notes for future rounds

- **`src/chapters/references.tex`** is the verbatim copy of the original
  hardcoded `\begin{thebibliography}` block. It is no longer compiled
  (`\printbibliography` from the generated `src/bibliography.bib` is the
  active path). Keep it as the human-readable provenance of the cite keys;
  if commit size matters it can move under `docs/archive/`.
- **`.env`** is gitignored and not committed. `.env.example` documents the
  one secret the release step needs (`GITHUB_TOKEN`). The build itself does
  not need it — only `pnpm run release` does.
- **`build/document-v<version>.pdf`** is committed as a release artifact.
  Intermediate LaTeX aux files (`build/*.aux`, `*.bbl`, `*.log`, …) are
  gitignored.
- **Optional automation:** a `validate:bib` script that HEAD-checks each
  `URL` / `DOI` field against arxiv.org / doi.org would turn the "factual
  accuracy" item in §1 from manual review into CI. Not implemented.

---

## 4. Status snapshot

| Item | Status |
|------|--------|
| Project shell cloned from `01-hilbert-polya` / `02-odd-zeta` | done |
| 8 chapter `.tex` files + acknowledgments + disclosure + appendix translation | done |
| `lean/CW3_Backing.lean` — `lake build` | done |
| `tests/CW3_backing_verify.py` — 41/41 PASS | done |
| 6 publication figures in `images/` | done |
| `citation.csl.json` — 76 hand-curated entries (single source of truth) | done |
| `pnpm run build` end-to-end (citation sync + docker pdflatex + biber) | done |
| Schiller epigraph + English translation appendix | done |
| Citekey ↔ real-publication cross-check | **not done** |
| DOI / arXiv reality (HEAD) checks | **not done** |
| Volume / page exactness audit | **not done** |
| `Kiely26` real title | **not done** |
