# Witness inventory — 03-crystalline-worldsheet

Generated 2026-11-25 from the working tree at `9319adf` (`git rev-parse --short HEAD`), over `main.tex` and `src/**/*.tex` — 11 files. Every number below is read from those files at run time; nothing here is copied from an older document. The form taxonomy comes from FTI-001 §2, F8-001 §1, WIT-RECON-001 and INV-WIT-001 §A, which this file supersedes (`superseded-by: docs/witness-inventory.md`).

## Marks

| form | count |
|---|--:|
| `\tier[ids]{P}` | 81 |
| `\tier[ids]{N}` | 19 |
| `\tier{P}` (bare) | 0 |
| `\tier{N}` (bare) | 0 |
| own-line `\witness{P}{…}` | 122 |
| own-line `\witness{N}{…}` | 1 |
| `\tier[\testref{…}]{N}` marks | 0 |

Ids carried by `N` tags: **0 citations over 0 distinct ids**.

## Decoration and accounting macros

| macro | occurrences in the manuscript |
|---|--:|
| `\LeanInline` | 0 |
| `\LeanStar` | 0 |
| `\LeanTally` | 0 |
| `\LeanCW` | 0 |
| `\leanline` | 0 |
| `\code` | 0 |
| `\testref` | 0 |
| `\witness` | 124 |

## Gates measured here

| gate | result |
|---|---|
| citation-key lint (no key, no `\cite` inside a tag) | **0 failures** |
| stars (`\LeanStar` body uses) | **0** |
| `Tier` column in a table | **0** |
| `pending(D7)` markers | **0** |
| `\tier[…]` id parts that are neither a `\testref`, a snake_case id nor a qualified declaration | **18** |
| open sites (`(open;`) | **0** |

`\tier[…]` ids that are neither a `\testref`, a snake_case id nor a namespace-qualified declaration (18 occurrences, 11 distinct):

- `...` ×6
- `R\_scalar\_pcf` ×2
- `M\_eq\_Mpcf` ×2
- `projection\_PCF` ×1
- `E\_iff\_no\_shared\_ordinate` ×1
- `G\_AB\_pcf` ×1
- `BF\_value` ×1
- `R\_AB\_einstein` ×1
- `eps0\_Mpcf\_pi` ×1
- `dS\_covers\_half\_hyperboloid` ×1
- `entropy\_ratio\_S3\_S6` ×1

## Per-file marks

| file | `\tier[…]` + `\tier{…}` marks |
|---|--:|
| `src/chapters/01-introduction.tex` | 3 |
| `src/chapters/02-methods.tex` | 31 |
| `src/chapters/03-derivations.tex` | 11 |
| `src/chapters/04-implications.tex` | 46 |
| `src/chapters/05-discussion.tex` | 1 |
| `src/chapters/06-conclusions.tex` | 2 |
| `src/chapters/appendix.tex` | 6 |

Re-generate with the measurement of the wave that owns this file; a hand-edited figure is a defect.
