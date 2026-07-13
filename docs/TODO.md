# TODO — Limitations, Future Work & Open Questions

This document collects every item the build **does not** currently verify, every
known blemish visible in `build/main.pdf`, and concrete recommendations for
later rounds of editorial / engineering work.

> **Operational note:** The shell is set up so that `pnpm run build` and
> `pnpm run verify` (Lean + Python) succeed on a clean checkout. The items
> below are *further* checks; they require human review, external data, or
> additional engineering before they can become automated.

---

## 1. NOT verified by this build

The project explicitly did **not** verify the following. They are out of scope
of the completeness-and-correctness pass that wired the deliverables into the
shell, and they are the natural starting point for a separate editorial task.

- **Each citekey points to a real publication** in the cited journal/proceedings
  (e.g. that `Maldacena98` is actually the Adv.\ Theor.\ Math.\ Phys.\ 2
  (1998) 231 article; that `Kiely26` Phys.\ Rev.\ A 113 022403 corresponds
  to the same paper; that `SusskindWitten98` matches hep-th/9805114, etc.).
- **Each DOI resolves** to the correct paper on doi.org.
- **Each arXiv ID is a real preprint** (the new-style `YYMM.NNNNN` and the
  old-style `hep-th/YYMMNNN` forms both parsed cleanly, but no URL was
  HEAD-checked).
- **Each page / volume / issue number matches** the original publication. The
  `\textbf{}`-wrapped volume markers and bare page numerals in the source
  `\bibitem{}` blocks are dropped during parsing (see §3.1 below), so
  quantities like `JHEP 02 () 082` or `Phys.\ Lett.\ B 379 () 283` retain the
  year and the first page number but lose the volume.
- **The English translation** of the Schiller epigraph in Appendix
  §`app:epigraph-en` is a standard rendering — verify it against the
  translator you intend to credit.
- **The bibliography order** in the rendered PDF is alphabetical by label
  (biblatex `style=numeric, sorting=none` does NOT reorder; the printed order
  follows first-cite order). If the journal expects alphabetical-by-author
  ordering, that has to be switched.
- **Factual accuracy of the prose** (the mathematics, the physics attributions,
  the claims about M-theory, F₁, etc.) — pure editorial review.

---

## 2. Cosmetic blemishes visible in the current `build/main.pdf`

These are *known* format quirks in the bibliography / body. None block
compilation, but they are visible.

- **2 entries with `In: ()` empty year.** `Pacioli1509` ("Venice (1509)") and
  `Hurwitz1891` ("Math.Ann.39 (1891) 279"). The year appears in the raw
  bibitem but the current `parse_raw` year regex
  `r'\b((?:19|20)\d{2})\b'` is too narrow to catch `1509` / `1891`. Fix:
  widen to `r'\b1[0-9]{3}|20\d{2}\b'` or any four-digit year.
- **~62 entries** show `In: (YEAR). JournalShort.Y () Page`, with the volume
  field empty (`()`). The `\textbf{<vol>}` markers used in the source were
  stripped. To recover volumes, preserve `\textbf{...}` blocks and emit them
  as a separate `volume = {...}` field in the bib (then biber routes them).
- **`Kiely26` title is the author list** in the rendered output, because the
  source `\bibitem{}` has no `\emph{...}` or `\textbf{...}` title. The fallback
  heuristic picked the wrong segment. Either manually title the entry or
  improve the fallback (look for `Phys. Rev. ...` patterns before the page
  number).
- **`Santos2020` DOI** renders the underscore as `\_28\_4` (escaped form that
  biblatex prints as `_28_4`). Acceptable but cosmetically wider than a real
  underscore; check whether DOI URLs may need `url = {...}` instead.
- **`arXiv` URLs for new-style IDs** contain `https : / / arxiv . org` (with
  spaces from `pdfTeX` URL breaking). This is a side effect of the
  `arxiv.org/abs/NNNN.NNNNN` URL being passed through TeX's url-breaking
  algorithm; the actual hyperlink target is correct. To silence it, set
  `url = {...}` (which uses `\url{}` rather than `\href{}`) or pass `nolinkurl`.
- **Companion-paper stubs `F1`, `HP`, `Corr`** show
  `J.A. Gonzalez Garcia et al.` in the author position with the actual title
  in the next field — fine, but the bibliography treats them as `@misc`
  (correctly), and their "year" source from the original paper's
  preprint/draft is not always recoverable (here they do get year=2026).

---

## 3. Recommendations for future rounds

### 3.1 Parser improvements (`/tmp/gen_bib.py` → `scripts/build_bib.py`)

- **Year regex**: widen from `r'\b((?:19|20)\d{2})\b'` to
  `r'\b1[0-9]{3}|20\d{2}\b'`. Captures `Pacioli1509` (1509),
  `Hurwitz1891` (1891), `Aristotle_*` (350 BCE wouldn't match but
  historical mechanics references do).
- **Volume / number capture**: instead of stripping `\textbf{...}` entirely,
  look for the pattern `\textbf{<vol>}\ (<num>)\ (<page>)` and emit
  `volume = {vol}`, `number = {num}` (or `issue`), `pages = {page}` fields
  with biblatex-compatible names.
- **`\footnote{}` stripping** in `strip_tex`: some original `\bibitem{}`
  arguments carry footnote markers that should not propagate into the bib.
- **Escape unification**: `clean_field` currently escapes `%` and `#`
  individually; centralise the LaTeX special-char escape into one helper and
  apply it consistently across all field cleanups.
- **Wrap-Greek fix**: `wrap_greek_in_math` is correct, but `\alpha^X` for
  superscripts needs to attach to the surrounding math mode automatically
  (the LaportaRemiddi96 `$\alpha^3$` patch was a manual in-place fix).
  Implement a `wrap_math(super_pattern=r'\^[a-zA-Z0-9]{1,3}')` sweep.

### 3.2 Pipeline integration

- **Replace `pnpm run build`'s citation sync** (which overwrites our
  carefully-preserved cite keys because `@citation-js/core`'s
  `format('bibtex')` regenerates them) with the Python generator now living
  at `/tmp/gen_bib.py`. Either:
  - commit `/tmp/gen_bib.py` as `scripts/build_bib.py` (versioned) and
    call it from `scripts/build.ts` via the `before:build` hook, **or**
  - patch `scripts/tasks/citation.ts` to use the CSL entry `id` as the
    BibTeX key by setting a `citationKey = id` option (citation-js
    supports `--citationKey-from-id`).
- **Round-trip regeneration**: write a separate `scripts/retex_bib.py` that
  consumes `src/bibliography.bib` and emits a `\bibitem{...}` block
  faithful to the original `src/chapters/references.tex`. Run
  `diff` between the two to surface parser regressions.

### 3.3 Reference archival

- `src/chapters/references.tex` is preserved as a verbatim copy of the
  original hardcoded `\begin{thebibliography}` block. It is no longer
  compiled in the main flow (`\printbibliography` from `src/bibliography.bib`
  is the active path). It should stay in the repo as a historical
  reference. If commit size is a concern, it can be moved under
  `docs/archive/references_original.tex` instead.

### 3.4 Shell hygiene

- Remove `src/paper_integrado_original_s4.tex.pre-split` (a stale copy of
  the integrated preprint before split; the chapter files are now the
  canonical manuscript sources).
- Confirm `.env` is **not** committed (it should remain gitignored per
  the project `.gitignore`); add a tracked `.env.example` documenting
  the only secret the build needs (`GITHUB_TOKEN`).
- Decide whether the PDF artifacts under `build/` belong in version
  control. Today they are not (only `build/*.pdf` is implicitly exempted
  by the existing `.gitignore`'s `!build/*.pdf` line — actually the PDF
  IS currently excluded since the `build/*.aux`, etc. exclusions override
  the keep-PDF rule, *unless* you literally want the PDF in the repo).

### 3.5 Validation expansion

- Add a `validate:bib` script that, for each entry in `bibliography.bib`,
  HEAD-checks the URL field against `arxiv.org` and `doi.org` and
  reports non-200 / redirect / mismatch. This is the automation layer
  that would let the "factual accuracy" task move from manual editorial
  review to CI.

---

## 4. Status of "what is in / out of scope today"

| Item                                                  | Status today       |
|--------------------------------------------------------|--------------------|
| File-layout clone of `01-hilbert-polya` / `02-odd-zeta` | done               |
| 8 chapter `.tex` files (cleanly split)                  | done               |
| `lean/CW3_Backing.lean`                                | done, `lake build` |
| `tests/CW3_backing_verify.py` (41/41 PASS)              | done               |
| 6 publication figures in `images/`                       | done               |
| `src/bibliography.bib` generated from CSL JSON           | done (Python gen)  |
| `citation.csl.json` (76 entries)                         | done               |
| Citation sync (\cite → bib → bbl → PDF)                  | done               |
| Schiller epigraph (`\emph`-free quote env)              | done               |
| Funding / COI / Acknowledgments / Appendix translation   | done               |
| Citekey factual verification                            | **not done**       |
| DOI / arXiv reality checks                              | **not done**       |
| Volume / issue / page exactness                        | **not done (cosmetic)** |
| Round-trip bibitem fidelity check                      | **not done**       |
| `pnpm run build` → `citation.ts` sync uses `id` as key   | **not done**       |
