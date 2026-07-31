# Changelog

## [0.4.3](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v0.4.2...v0.4.3) (2026-07-31)

### Bug Fixes

* **build:** use biblatex format, clean stale artifacts, surface latex errors ([1733271](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/17332718f06405664320bb339599c0d64c22e0e5))

### Chores

* regenerate metadata and PDF after biblatex format fix ([656a587](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/656a5876e3e98d2bb08c7983d99768287d4c8abd))
* update .gitignore, remove .env.example ([c7326ab](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/c7326abd74bb367c83ee2b0da0e9f3d0cde27e31))

## [0.4.2](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v0.4.1...v0.4.2) (2026-07-30)

### Documentation

* acknowledge MiniMax, Z.ai, and Xiaomi Research in formal verification ([10d3920](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/10d39207565aa9932e3062302926ddbab83432a9))

## [0.4.1](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v0.4.0...v0.4.1) (2026-07-30)

### Bug Fixes

* **build:** use latexmk instead of manual pdflatex/biber ([8bfd9e9](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/8bfd9e977ed652ff99c330fdd0902a7b6868a77b))

### Documentation

* standardize generic build pipeline docs ([7c9b0ea](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/7c9b0eac106866d14de0d8e8d7a39331b5c27888))

## [0.4.0](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v0.3.5...v0.4.0) (2026-07-29)

### Features

* **ci:** add Zenodo upload workflow via REST API ([f2cce11](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/f2cce1108e76104a32c7cf42107666dc906d6f11))

### Bug Fixes

* **citation:** add doi to package.json, propagate via pipeline ([3e64dbb](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/3e64dbb9ad5654017c33a78e213a0f5c4cad523f))
* **citation:** replace invalid resource_type 'publication-technicalreport' with 'publication' ([b01da2d](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/b01da2d0ca5b7254573dcaccb979c1f3161ad747))
* **citation:** set Zenodo upload_type to publication/preprint, add Corr DOI ([498313e](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/498313e8afd321022c80cefd85aa0d992cb388c1))

## [0.3.5](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v0.3.4...v0.3.5) (2026-07-29)

### Bug Fixes

* **citation:** remove invalid publication_type from .zenodo.json ([1d9f052](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/1d9f05272001fe5cbff6a3af013b33c08140bdc0))

### Chores

* remove docs/archive directory ([69a6df2](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/69a6df286d4d8674aa89941d909a54c07d50ff42))

## [0.3.4](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v0.3.3...v0.3.4) (2026-07-29)

### Bug Fixes

* **citation:** set upload_type to software for Zenodo ([93e7a14](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/93e7a1460ea9b267f78cfba0548db2e4b31867b2))

## [0.3.3](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v0.3.2...v0.3.3) (2026-07-29)

### Bug Fixes

* **build:** clean stale LaTeX artifacts and tolerate pdflatex non-zero exit ([c387f55](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/c387f55e06be7e845c01af6d1bab58e32cf7b406))
* **citation:** normalize institution.country to ISO codes ([1da6a39](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/1da6a39a6320fe5dd9b00d32b37fa65bae80a879))
* **citation:** repair CSL→Zenodo pipeline bugs ([1144441](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/1144441c58d56214c0931f6c7631ebde260e4d76))
* **citations:** add confirmed DOIs via Hound MCP ([ebe25f0](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/ebe25f07352b869747e6f402a7d7795f61749c64))
* **citations:** correct metadata for 6 references ([246f691](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/246f691084ee01545c9fb1018e245663f1448c1c))

### Styles

* add missing \subjclass to match 01/02 target state ([5746edf](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/5746edf4558e2288e90813a8b4a431678ce7b503))
* use muted red for linkcolor across all repos ([23512a3](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/23512a3865b4106e8314bedb1a9af10e7a8dad3b))

## [0.3.2](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v0.3.1...v0.3.2) (2026-07-13)

### Bug Fixes

* **tex:** restore urlcolor=blue in hypersetup ([82e3e1c](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/82e3e1caa2ac8838feb8fc6022e5e4904f332ebe))

## [0.3.1](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v0.3.0...v0.3.1) (2026-07-13)

### Bug Fixes

* **readme:** remove premature trilogy/companion table ([98efd80](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/98efd8023e378fb121a9b559653d41ab834cac8f))
* **tex:** red cross-refs, blue citations (no green) ([72b7cbe](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/72b7cbe9d31f5bd4c485b82ec27e955a36ccbd80))
* **tex:** remove explicit hypersetup, amsart handles blue links natively ([7c1414c](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/7c1414c309b6296533bc789dae92f90c63c6fc0a))
* **tex:** restore colored hyperlinks for refs and cites ([beb4c01](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/beb4c0155ba4a9f36d73fd9d3c6530ad8316a93d))

## [0.3.0](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v0.2.0...v0.3.0) (2026-07-13)

### Features

* **doi:** add Zenodo DOI 10.5281/zenodo.21343602 ([ef49111](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/ef491115bd357fa84707eb7ff0661f3838eef62f))

### Bug Fixes

* **tex:** add 'The Crystalline Worldsheet' to first-page title ([ff5cd19](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/ff5cd195880074332a7f4e5bcdd9a245de42cacb))
* **tex:** correct received date to July 13 2026 (Zenodo publication date) ([51fc1b8](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/51fc1b85d585aff4aa1cf7e21e34e1755da19ab5))
* **tex:** shorten running header to avoid page-number overlap ([816b2a3](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/816b2a3875151614ec1d3f677b692facf2dd0406))
* **tex:** switch to amsart class, fix author block, figures to PDF ([6964e4d](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/6964e4db7cceec1209368fabb950ea1a3f9dfd7a))

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
