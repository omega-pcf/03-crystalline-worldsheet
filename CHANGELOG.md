# Changelog

## 0.2.0 (2026-07-13)

### Features

* **bib:** hand-curate citation.csl.json as single source of truth ([47adfde](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/47adfded366e356a7cb2c4902010693676b7cff0))
* bootstrap crystalline-worldsheet from CW3 author deliverables ([57d1867](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/57d1867d16cf9f733aa690a0495359143073d1d8))

### Bug Fixes

* **lean:** add missing spaces around operators in dS_einstein_Lambda ([4cdbc8f](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/4cdbc8fe072aff107f3b3df49c7d0ffba9b46ad4))
* **tex:** Profesor → Professor in acknowledgments ([706b928](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/706b9288f8db2cbc13bdde043b7ca5725ccac6cf))

All notable changes to the **The Crystalline Worldsheet** manuscript and
verification suite are recorded here.

The format follows [Conventional Commits](https://www.conventionalcommits.org/);
release-it generates the per-version section headers automatically from the
commit messages, so only the *Unreleased* section is hand-curated.

## [Unreleased]

### Added

- Initial manuscript sources (`src/chapters/`) split from the integrated
  preprint `CW3_paper_integrado_nuevo_s4.tex` (single-section monolithic
  predecessor).
- Lean 4 / Mathlib backing `lean/CW3_Backing.lean` (113 `\Lean{...}` tags).
- Numerical backing `tests/CW3_backing_verify.py` (one `[OK]/[FAIL]` line
  per cited equation label).
- Figure generator `scripts/figures/CW3_all_figures.py` (six publication
  figures).

### Notes

- This release preserves the deliverables from the author for placement
  into the project shell; no editorial or scientific content has been added
  or removed.
