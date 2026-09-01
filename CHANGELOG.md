# Changelog

## [1.2.1](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v1.2.0...v1.2.1) (2026-09-01)

### Bug Fixes

* **tex:** add univalence and Lawvere paragraphs with verified CSL entries ([80cee0b](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/80cee0bb08bb8d687c56f5461a5b77f59e0b8674))

## [1.2.0](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v1.0.9...v1.2.0) (2026-08-27)

### Features

* **fig:** add rug plot of measured spacings to sine kernel figure ([d86f320](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/d86f3201e949f5cb4adbfad5f7710e8a30abd86b))
* **lean:** rebuild ledger JSON v3.0 (flat, lean+tex+numerical), move propgraph to lean/, simplify compilation note ([7c067c2](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/7c067c29fd50622b9c3e3afbb9c45f61361d2a36))
* **tests:** migrate verification to pytest suite ([af588cb](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/af588cb210e71183bfb64d2e13fd433473a32fcc))
* **tex:** add \Pytest/\PytestInline macros for test references ([a39ea72](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/a39ea72bdb5275c6b7704178a150347e89f4def6))
* **tex:** replace \Pytest with \Numerical, cite eq labels not file paths ([8b076f2](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/8b076f24f2b150f11df170b62d434283fd57b88e))
* **tex:** replace tier system with P/N/Hyp verification tags ([18a37a1](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/18a37a1d772cd877899278fbfa57cc5e9dd5c4c4))

### Bug Fixes

* **lean,tex:** rename ALL camelCase declarations to snake_case ([9e208de](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/9e208de0a31d518b5427ca0a2e86c4d180db3031))
* **lean,tex:** rename all camelCase decls to snake_case across lean, ledger, and tex witnesses ([45e74ec](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/45e74ecc924c8a6658292fd2a885766fa71e1559))
* **lean,tex:** rename M-prefixed migration artifacts to descriptive names ([d7c7a35](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/d7c7a35a6c814f5ab1cf4fbd3be9de012056b9d8))
* **lean:** rename camelCase declarations to snake_case ([95aeabe](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/95aeabe887a9a1bfe114ba45aa0f9613db21b527))
* **lean:** rename Nmodes_six_ne_fib to snake_case ([7d13cd2](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/7d13cd2de972a849f190919cb8f55e8916ce7a97))
* **tex,fig:** academic figure reference, panel (a) to bottom-right, D3 sentence fix ([14eb1bf](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/14eb1bf48bbed2028db2388f2a516cd8ed382089))
* **tex,lean:** orphaned ProofWitness→Block, broken sentences, rebuild ledger JSON ([664ae43](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/664ae43b62191c3961622c1a79a2a11f54ab330e))
* **tex:** add citations to all HypWitness, add missing bib entries ([cf05b8d](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/cf05b8d696e5cc3eefe57fb7a0120fbfe5257017))
* **tex:** add N[] tags to key numerically verified equations ([baed703](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/baed70339d734649319f90cbd67092b95bb48e0a))
* **tex:** add N[] tags where text explicitly claims numerical verification ([99d62b5](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/99d62b5e58e1cd20d95f0e431c6cbf5d9f64c55c))
* **tex:** audit and fix all H[] witness tags ([879f822](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/879f822707f646aca7395f042cfb3bca65a0b199))
* **tex:** convert end-of-line \ProofWitness to \ProofWitnessBlock across all chapters ([10ef5df](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/10ef5df0ab83a52dc829db33e7c0f2c866d87583))
* **tex:** correct figure generation reference — no pytest for figures, just main.py ([17c9220](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/17c922016215c7abcdef55b9f3b3c37c9d941c3a))
* **tex:** merge consecutive P[] blocks, fix orphaned inline ([1e1a840](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/1e1a8409637fd083c00a79cd5688e4fdfb653387))
* **tex:** merge consecutive ProofBlock, fix stray brace, add colors ([01bfb4c](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/01bfb4cfae8d0ea6717aa0f6cc3f94b039498e65))
* **tex:** orphaned cites, merged blocks, inline/block corrections ([b114968](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/b1149689891ec86d84132708d3c5c6090e5d2f91))
* **tex:** P[]+N[] inline pairing, standalone P→block ([efcca69](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/efcca69f33bda41db2829d7ea10bec7bdd63b708))
* **tex:** prose fixes from pdftotext audit — missing period, orphaned semicolon, tag typo, capitalization, subject-verb, parallelism ([935ec03](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/935ec0382480be9b54df859fa73fc33f5c6391f8))
* **tex:** remove \Conj from verification legend — tag unused, description was unclear ([7bb9d93](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/7bb9d935e2b4dbe875b6490c0a98c4811a8c74bc))
* **tex:** remove \HypWitness{\cite{...}} — renders as H[[65,66]] ([37f4538](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/37f4538cfbb0ddb4a8e6b7e322b26ddec91bf474)), closes [#1](https://github.com/omega-pcf/03-crystalline-worldsheet/issues/1)
* **tex:** remove duplicate P[oplus_formula] ([f3a0d63](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/f3a0d63b75c55ee1e0bb3d3266fb277acfe80a48))
* **tex:** remove inline title from fig:spine5, keep legend labels only ([4cfff5e](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/4cfff5ec5a4c13b82053b1caef2b83f92a8435ef))
* **tex:** remove orphaned \Conj tags, replace CW6 shorthands with 'framework', fix stale py filenames ([ca13a48](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/ca13a480e4d972c7c18082189c2f3fd68a399484))
* **tex:** remove orphaned \Open, deduplicate HypWitness cites ([7dfe1cc](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/7dfe1ccf74e84630c6109a2f68d0d2659b8dd90c))
* **tex:** remove orphaned HypWitnessBlock{class_number_formula} ([122ed20](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/122ed2058e37ddbbbd4a8a351ad8b9ca885b3ba1))
* **tex:** remove orphaned Minkowski citation, integrate into text ([c613b39](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/c613b390138cd104dbb19555a76526fc4b10f982))
* **tex:** remove orphaned Proof:, dots, and parentheses around ProofWitnessBlocks ([01f8e35](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/01f8e3523d5fc941b7375985f881133e54a8aaa9))
* **tex:** remove stale HypWitness{dedekind_factorisation} ([cc051cb](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/cc051cb3d668fed1636f70994acd9d753c89e152))
* **tex:** remove stale HypWitness{poisson_summation} ([13c87db](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/13c87dbc995754f0eb43a509b77bb61568c74460))
* **tex:** rename verification macros to avoid LaTeX conflicts ([467b744](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/467b744ec866e5ba4d6c50810db979cf5f813a2c))
* **tex:** resolve undefined control sequence in figure lines ([8fb0ffd](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/8fb0ffd879accd6d29c49b80bc2e550c88410d5f))
* **tex:** resolve undefined ref and macro formatting issues ([8eb4328](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/8eb4328322285c5dc0974c66c3b3a5e253fb5607))
* **tex:** restore orphaned 'dimension count' as proper sentence before Block ([0daeda4](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/0daeda4b574965ca696628b716631de76ac02515))
* **tex:** revert inline→block for all end-of-theorem witnesses ([5b47ccf](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/5b47ccfed80c7bdae475b4d97dfabb7d23888987))
* **tex:** standardize all witness names to snake_case ([7664ec8](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/7664ec86272bc0cc3ee7ce5297f71db94d6e4eba))
* **tex:** update Nmodes\_six\_ne\_fib witness to snake_case in ProofWitnessBlock ([c1d8808](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/c1d8808964ea953c27b58d6600a7acd5ab5d4e28))
* **tex:** verification tags — escape underscores, fix bracket syntax ([8822544](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/8822544560ce9762ba03fd5527519fa6f131c99d))
* **tex:** wrap inline macros in \mbox{} to fix \Small in math mode ([24a91aa](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/24a91aa451f8d5a18a262b708c3986aa1263385a))

### Refinements

* **tex:** inline→block conversion for end-of-environment witnesses ([f736595](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/f7365954162a1768a5adf31bce9b9b6aa2f867e4))
* **tex:** rename verification tags to descriptive witness names ([d09672d](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/d09672d9429dca53f2e24432f40551d82223c331))

### Chores

* **lean:** remove unused lean_lib entries (CW3_Backing, CW6_complete_v1, CW6_complete_v1_clean) ([c0218c0](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/c0218c0395e2517e202cae12b737f6eaaaf7060d))
* remove fig3_N_modes.pdf from scripts/figures (lives in images/) ([364bcf8](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/364bcf8bcd0d324315215cec81ad5ed8700997c9))
* remove stale CW6_ledger_run.txt ([0d1c71b](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/0d1c71b101ee1cb6fd9ef10c9ddc3e634b44cfd7))

## [1.0.9](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v1.0.8...v1.0.9) (2026-08-26)

### Bug Fixes

* correct GUE measurement, add level-repulsion figures, remove unjustified 0.35% ([2ca7511](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/2ca75113511afcc4a3f4640671188e89ed966e52))

### Styles

* **figures:** improve layout, remove overflow, fix labels ([79231e5](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/79231e5f886706848731cd014e0660f749e40b38))

## [1.0.8](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v1.0.7...v1.0.8) (2026-08-25)

### Bug Fixes

* align author ordering in CITATION.cff and .zenodo.json with main.tex ([73bca0e](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/73bca0ea140c19b54250175c9d4af7503a23bef2))
* **tex:** connect eq:bridge-fixed to its Lean proof and update counts ([3354175](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/335417550d05e85019ba8d64ee468ccde64a0e9c))
* **tex:** correct compilation note and verification table in 02-methods.tex ([bb067ac](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/bb067ac651672fb049732552d746b66e7d4df77e))

## [1.0.7](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v1.0.6...v1.0.7) (2026-08-25)

### Bug Fixes

* **lean:** restore -- comments after colour_ratio theorem ([27f89f0](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/27f89f0752f5355ebde51a2c1f9e11caff6b0c62))

## [1.0.6](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v1.0.5...v1.0.6) (2026-08-25)

### Bug Fixes

* correct project page badge link to crystalline-worldsheet slug ([534879f](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/534879f8ad959d11f4634a3cd8904b0eebbd654e))

### Chores

* **lean:** remove CW3_Backing.lean ([afdd7f4](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/afdd7f4fb09605a988109e1ecbde9d10952955b1))
* **lean:** remove development process artifacts from CW6_complete_v2.lean ([6177f09](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/6177f09705796e456de036f903ce862c6d41ab61))
* **lean:** translate all Spanish comments/docstrings to English ([60e3a5c](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/60e3a5c7d6ccbbba9ab6d770efbfda7b53e37e52))
* **tests:** remove orphaned CW3_backing_verify.py ([e794244](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/e7942443b138cbd8400bda77097a15f81b4b806e))

## [1.0.5](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v1.0.4...v1.0.5) (2026-08-24)

### Bug Fixes

* move period before \Lean tag in KK numerator passage ([1fafe60](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/1fafe6046c89475b60ec8dbbc708adf5cc21d1f9))
* move period before \Lean tag in S-duality/certainty passage ([fa38972](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/fa38972ee074f40e81fdcedcc1b589e74aa5667f))
* orphaned punctuation after Lean tags in W3/W5/spectral sections ([8491b34](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/8491b343d209bd4c62f2a9a1cf99dc59ffffe1ce))
* orphaned punctuation in bullet list and D3 proposition ([7459132](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/745913256980b99a1f1ece24df9d5c868b3f5921))
* orphaned punctuation in spectral angle/uniqueness section ([9f5331a](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/9f5331a9582645a6eed3daddc7891de81cd28216))
* orphaned punctuation, broken \Lean\, W9/W11/W12 formatting ([deb87cc](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/deb87cc52dbd910beb4a37410aa32c889e0768da))
* **typography:** \Lean uses \nolinkurl for word-break at any character ([8f54bf2](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/8f54bf2b701e192666f70313f37f070418f25d8c))
* **typography:** \Lean uses \parbox for word-wrap, prevents right-margin overflow ([6fe3db7](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/6fe3db718ce34a94bf287db368466498ff04ccfd))

## [1.0.4](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v1.0.3...v1.0.4) (2026-08-24)

### Bug Fixes

* **acknowledgments:** correct native_decide count from two to one ([f809df9](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/f809df91b4ddbc6c5cb1f97978f59c7cfe7d8d6d))
* add line breaks between Lean tags and following text in Section 3.3 ([a16534f](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/a16534f09e6774c0f88f061df800c745fbed6ff3))
* **bib:** cite Wertz translation of Schiller's An die Freude ([d667d3d](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/d667d3de75cbce8915e91791c7fd3a650b55b720))
* convert last \LeanFor in Section 3.3 to \LeanWrap for proper line break ([f7cfd03](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/f7cfd03c105ab362f59621e9318142955e89a537))
* Funding line breaks, bullet list orphaned punctuation ([d1b15ca](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/d1b15ca8f041fab9d70aeade245c8620d3066c3e))
* orphaned citations, broken sqrt, restore \LeanInline ([7ff573c](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/7ff573c2094f2dc19847449ff60d7cd59f560133))
* reset paragraph settings after Schiller minipages, prevent format leak to Funding ([229ec89](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/229ec897afcb035aaa145fedd0be62f97472bbad))
* **typography:** \Lean tags now start their own right-aligned paragraph ([4716e02](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/4716e0206d538352ca7610f3e0dfe63d64007e7b))
* **typography:** \Lean uses \raggedleft for word-wrap, preventing right-margin overflow ([c3be14e](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/c3be14e2f7a5bffc6f5933b40390d44daf0cafbc))
* **typography:** add newlines between \Lean tags and following text ([49a8073](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/49a8073852b9c17192f68cfbdd23fc234ae8d374))
* **typography:** clean up inline Lean tags in Sections 3.4, 4.2, 4.4 ([7e0ebb6](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/7e0ebb66e6994ab277d1f49a2c7387688c64d241))
* **typography:** clean up Section 3.3 Lean tags — remove % suppressors, convert inline to \LeanWrap ([fbe8a2c](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/fbe8a2c5143c7ede9c7d48f8ef22303cef31eaa4))
* **typography:** convert 15 Lean tags with suppressed newlines to \LeanWrap ([05fbd5f](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/05fbd5ff8fe57cbb6b03445fd02fc163ec8a0a80))
* **typography:** convert 27 inline Lean tags to \LeanWrap across all chapters ([8538be3](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/8538be362ae0c418ab22ce379bd41e61a89894a3))
* **typography:** convert 7 inline Lean tags to \LeanWrap in appendix ([ada2214](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/ada22149f4303d7761cc16f380713ed134fb457c))
* **typography:** revert \Lean to inline \unskip\hfill, fix right-alignment leak ([c85bde9](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/c85bde9fb48bb1e4b6ab4d2a68ec65b4602f365e))

### Styles

* add \medskip before Chebyshev proof for visual separation ([127ac29](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/127ac29ebf48986fcef6f0fc14d1c3ceb5e22388))
* add \medskip between Lemma 2.7 (Gaussian) and Theorem 2.8 (half-factorial) ([1f38bb4](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/1f38bb4993ec5d91a09317d986e86059880e4a45))
* polish Schiller side-by-side — epigraph leftskip, rule separator, 1em spacing ([810dfcb](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/810dfcb921091ddcae3a388f4e02037fc9d61ab6))
* tighten Schiller side-by-side layout — compact spacing, smaller attributions ([32aef65](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/32aef6502e4210c3dfa9bf9ba5d65608710309d6))

### Refinements

* move Schiller translation to acknowledgements side-by-side layout ([3187b01](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/3187b0176cfdc8b37eb9b8323d1730f028a99b8b))
* unify \Lean and \LeanWrap into single \Lean command ([e3c9ef1](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/e3c9ef1beefa8f9a32c63f25d871fa7c4c653d40))

## [1.0.3](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v1.0.2...v1.0.3) (2026-08-24)

### Bug Fixes

* **metadata:** update Corr DOI to all-versions (10.5281/zenodo.21731878) ([5200294](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/5200294924da08279598829268336a09e09d7b16))

## [1.0.2](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v1.0.1...v1.0.2) (2026-08-24)

### Bug Fixes

* **metadata:** sync title from package.json and correct CITATION.cff/zenodo ([bd74777](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/bd747775e505a3d642487ed47ca7da864a3dc504))

## [1.0.1](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v1.0.0...v1.0.1) (2026-08-24)

### Bug Fixes

* **metadata:** update abstract and zenodo_description to match CW6 v4 paper ([4775752](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/477575210cffba2aec18a2524bf5c6994ef65535))
* **metadata:** update package.json description to match CW6 v4 title ([a6fe801](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/a6fe801059d926b17237a9f570d2786c229ba196))

### Documentation

* update README for CW6 v4 — title, abstract, file references, and verification commands ([dec4e1d](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/dec4e1d81776902fa99c620306fb1d45d8120421))

## [1.0.0](https://github.com/omega-pcf/03-crystalline-worldsheet/compare/v0.4.3...v1.0.0) (2026-08-24)

### ⚠ BREAKING CHANGES

* Paper content updated to CW6 v4 (monolithic split into
chapters). Lean backing replaced: CW3_Backing.lean (1870 lines) →
CW6_complete_v2.lean (6600+ lines, 0 sorry, 0 axioms, 0 warnings).
Numerical verify replaced: CW3_backing_verify.py (148 checks) →
CW6_complete_verify_v2.py (344/344 checks OK).

- Split CW6_paper_v4.tex (5855 lines) into chapter files by line delimiter
- Updated main.tex preamble with v4 packages, commands, and theorem envs
- Added 31 missing entries to citation.csl.json (76 → 107 total)
- Verified all 107 entries against DOI/publication sources (17 corrected)
- Regenerated bibliography.bib, CITATION.cff, .zenodo.json via pipeline
- Added biber support to .latexmkrc
- Updated lakefile.toml: CW6_complete_v2 as default target
- Updated package.json: verify scripts point to new files
- Added sympy dependency to pyproject.toml
- Added alignment ledger, propgraph, and stats artifacts
- Fixed duplicate TOC entries in acknowledgements/funding

### Features

* CW6 v4 — paper, lean backing, numerical verify, and bibliography ([a9eea8f](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/a9eea8f3d2523f776b5035fff0644503587e384c))

### Bug Fixes

* use blackboard F_1 symbol for field-with-one-element reference ([9ef8451](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/9ef8451bedec155b778526d48a30919272baaedc))

### Styles

* improve title layout and section pagination ([1ceba6f](https://github.com/omega-pcf/03-crystalline-worldsheet/commit/1ceba6fcecefc54f17369cdb42c5736a23fcc305))

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
