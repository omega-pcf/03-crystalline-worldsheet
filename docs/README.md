# Project Documentation

This directory contains technical documentation for the manuscript, its build and release pipeline,
and the family style guide as it applies here.

## Structure

```
docs/
├── README.md              # This file
├── architecture.md        # Release system architecture
├── citations.md           # CSL single-source citation pipeline + witness (tier) contract (§1–§8)
├── figures.md             # Deterministic figure pipeline
├── installation.md        # Prerequisites and setup
├── style-guide.md         # Family style guide v2.2 (port of `05-kkgt/docs/style-guide.md`)
├── style/
│   └── grammar.md         # Grammar and usage rules of human language (ES/EN/FR/IT examples)
├── usage.md               # Build and release commands
├── witness-contract.md    # Why the marks exist (portable rationale of the witness device, EN)
├── witness-compliance.md  # Applied §8.5 inventory: every witness site with its quantities
├── witness-decisions.md   # Witness decision gates for the author (§0 and §4 applied; §1–§3, §5–§7 open)
└── reports/               # Specific, repository-tied reports (dated, id'd)
    └── README.md          # Reports convention (template) + index of this repository's reports
```

## Contents

- **architecture.md**: Tech stack, execution flow, reproducibility measures, scripts structure.
- **citations.md**: How `citation.csl.json` drives the bibliography, CITATION.cff and .zenodo.json
  (§1–§7); §8 is the family witness (tier) contract — grammar, writing rules, alphabet and the
  quantified inline / own-line criterion — propagated here on 2026-11-17. Its applied inventory for
  this manuscript is [`witness-compliance.md`](witness-compliance.md); the open decisions stay in
  [`witness-decisions.md`](witness-decisions.md) and are untouched by the propagation.
- **figures.md**: What `pnpm run generate:figures` guarantees and why (byte-stable, text-extractable PDFs).
- **installation.md**: Prerequisites and setup instructions.
- **style-guide.md**: The family style guide (v2.2), a port of `05-kkgt/docs/style-guide.md`:
  editorial rules (§1–§12), including the rigorous IMRAD structure of §7; the software-quality
  doctrine D1–D7 (§13); the TeX/proofreading pipeline with its cited sources (§14). Generic across
  the family: this repository's own conventions are linked, never copied — the family documents it
  links (`citations.md` §8, `witness-contract.md`, `style/grammar.md`, `reports/`) are propagated
  here, so every link is local.
- **style/grammar.md**: The grammar and usage rules extracted from `style-guide.md` §1.5 —
  language-neutral, worked in Spanish, English, French and Italian, with the RAE-checked Spanish
  `se` verbs and their sources.
- **usage.md**: Daily workflow, conventional commits, build and release commands.
- **witness-contract.md**: The rationale of the witness marks — why they exist, the inline /
  own-line shape rule, the compactness method, the colour and accessibility rules, and what the
  marks do not assert. Portable across the family; the applied state of a repository lives in its
  `docs/reports/`.
- **reports/**: Specific reports — per-site inventories, decision logs, verdict tables and
  incidents. The convention (naming, ISO header, index format) and the index of this repository's
  reports are in `reports/README.md`; this repository has no report yet.
- **witness-compliance.md**: The applied inventory of `05-kkgt` `citations.md` §8.5 for this
  manuscript — every one of the 223 witness sites with `k`, `L`, `r`, `i`, `d`, `u`, `p` and the
  rule that decides its shape — plus the compliance audit of the rules of §8.2 (one claim one tag,
  no compound, no cite inside a tag, no tag in a caption) and the literal gate output.
- **witness-decisions.md**: One row per open decision on the verification-tag system, each with a
  recommendation and a ready-made replacement text; written for the main author. §0 (mechanical
  pass) and §4 (the `H` class) are applied; the rest stays open.

## Conventions

All commits follow [Conventional Commits](https://www.conventionalcommits.org/):

```
<type>(<scope>): <description>
```

**Common types:** `feat`, `fix`, `docs`, `refactor`, `chore`.
