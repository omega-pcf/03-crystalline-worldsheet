# Witness inventory — 03-crystalline-worldsheet

> **GENERATED** — `pnpm run witness:inventory` (`scripts/tasks/witness-inventory.ts`) rewrites
> this file from the working tree; `pnpm run inventory:check` (inside `validate`) fails with
> a diff when it drifts. Do not edit by hand.

Measured over the tracked manuscript sources (`main.tex` and `src/**/*.tex`) — 11 files. TeX comments (a line whose first non-space character is `%`) and the lines that *define* a counted macro are excluded; nothing here is copied from an older document. The form taxonomy is the one of `docs/witness-contract.md` §6.1.

## Marks

| form | count |
|---|--:|
| own-line `\witness[ids]{P}` | 132 |
| own-line `\witness[ids]{N}` | 3 |
| own-line `\witness{P}` (bare) | 0 |
| own-line `\witness{N}` (bare) | 0 |
| inline `\witness[ids]{P}` | 70 |
| inline `\witness[ids]{N}` | 17 |
| inline `\witness{P}` (bare) | 0 |
| inline `\witness{N}` (bare) | 0 |
| `\witness[\testref{…}]{N}` marks | 0 |

Ids carried by `N` marks: **21 ids over 19 distinct**.

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
| `\witness` | 224 |

## Gates measured here

| gate | result |
|---|---|
| citation-key lint (no key, no `\cite` inside a tag) | **0 failures** |
| stars (`\LeanStar` body uses) | **0** |
| `Tier` column in a table | **0** |
| `pending(D7)` markers | **0** |
| `\witness[…]` id parts that are neither a `\testref`, a snake_case id nor a qualified declaration | **74** |
| open sites (`(open;`) | **0** |

`\witness[…]` ids that are neither a `\testref`, a snake_case id nor a namespace-qualified declaration (74 occurrences, 47 distinct):

- `...` ×6
- `R\_scalar\_pcf` ×5
- `BF\_value` ×4
- `G\_AB\_pcf` ×4
- `eps0\_Mpcf\_pi` ×4
- `M\_eq\_Mpcf` ×3
- `R\_AB\_einstein` ×3
- `S\_tower` ×2
- `euler\_from\_ideals\_K` ×2
- `local\_dedekind\_inert\_K` ×2
- `local\_dedekind\_ramified\_K` ×2
- `local\_dedekind\_split\_K` ×2
- `C\_fixed\_PF\_rotate` ×1
- `E\_iff\_no\_shared\_ordinate` ×1
- `G\_Lambda\_duality` ×1
- `H\_half\_one\_bit` ×1
- `KK\_BF\_bound` ×1
- `KK\_numerator` ×1
- `L1\_eq\_period\_over\_pi\_sqrt5` ×1
- `L1\_from\_class\_number\_formula` ×1
- `LL\_spatial\_ne\_zero` ×1
- `M\_PCF\_eq\_pi\_div\_eps0` ×1
- `S\_is\_operator\_spectrum` ×1
- `S\_tower\_eq\_exp\_regulator` ×1
- `S\_tower\_recurrence` ×1
- `class\_number\_one\_K` ×1
- `clifford\_S3\_condition` ×1
- `colour\_scale\_from\_M` ×1
- `cpt\_fixes\_C` ×1
- `cpt\_swaps\_P\_to\_F` ×1
- `dS\_covers\_half\_hyperboloid` ×1
- `degree\_formula\_K` ×1
- `energy\_is\_inv\_H` ×1
- `entropy\_ratio\_S3\_S6` ×1
- `even\_L\_rationality` ×1
- `ideal\_norm\_values\_K` ×1
- `kk\_above\_BF` ×1
- `kk\_continuous\_below\_BF` ×1
- `modular\_generator\_is\_LL\_over\_T` ×1
- `projection\_PCF` ×1
- `regulator\_K\_pos` ×1
- `sigma\_EM\_val` ×1
- `sigma\_G\_val` ×1
- `sigma\_Lambda\_val` ×1
- `sigma\_geom\_from\_S3` ×1
- `sqrt5\_half\_L1\_eq\_regulator` ×1
- `theta\_preserves\_modulus\_C` ×1

## Per-file marks

| file | `\witness` marks |
|---|--:|
| `src/chapters/01-introduction.tex` | 4 |
| `src/chapters/02-methods.tex` | 76 |
| `src/chapters/03-derivations.tex` | 25 |
| `src/chapters/04-implications.tex` | 101 |
| `src/chapters/05-discussion.tex` | 1 |
| `src/chapters/06-conclusions.tex` | 2 |
| `src/chapters/appendix.tex` | 13 |

Re-generate with `pnpm run witness:inventory`; a hand-edited figure is a defect.
