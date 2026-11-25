# Witness compliance — 03-crystalline-worldsheet

| Field | Value |
|---|---|
| **id** | `WIT-001` |
| **title** | Witness compliance of 03-crystalline-worldsheet: every witness site with its criterion quantities |
| **status** | applied |
| **date** | 2026-11-16 |
| **version** | 1.0 |

**Scope.** This repository only: the applied inventory of the placement
criterion for the marks the manuscript prints, plus the audit of the writing
rules against them.

**For:** the main author · **Applied:** 2026-11-16 · **Contract:** the family
witness standard, [`witness-contract.md`](../witness-contract.md) §6 (grammar
and writing rules §6.5, alphabet §6.9, placement criterion §6.10), linked from
[`style-guide.md`](../style-guide.md).
This file is the applied inventory of §8.5 for this repository — the
counterpart of `05-kkgt/docs/reports/20261115_WIT-001_criterion_sites.md` —
plus the compliance audit of every rule of §8.2 against every mark the
manuscript prints. The open author gates about *what the tags say* are now
rows of the family ledger [`witness-decisions.md`](../witness-decisions.md); the
gates §1–§3, §5–§7 it replaced are the historical trace
[`20261116_DEC-001_witness_decision_gates.md`](20261116_DEC-001_witness_decision_gates.md).
This file settles only *where the marks sit and how they are spelled*.

## 1. Counters

| | at `19e96cb` | now | change |
|---|---:|---:|---|
| marks in `src/chapters/` | 228 | 223 | −5: the three `H` marks (class removed, gate §4) and the two marks of the gloss that printed the compound example |
| on a line of its own (`\witness{X}{ids}`) | 189 | 123 | −66 |
| inline (`\tier[ids]{X}`) | 39 | 100 | +61 |
| **claim marks** (excluding legend/meta uses) | **217** | **217** | **unchanged — every claim keeps its tag** |
| legend/meta uses (`{...}`) | 11 | 6 | `H` gone (3), compound example gone (2) |
| shape moves applied | — | 72 | 69 block → inline, 3 inline → block |

Per chapter, before → after (block / inline):

| File | before (block / inline) | after (block / inline) |
|---|---|---|
| `01-introduction.tex` | 2 / 4 | 1 / 3 |
| `02-methods.tex` | 76 / 1 | 46 / 31 |
| `03-derivations.tex` | 23 / 2 | 14 / 11 |
| `04-implications.tex` | 77 / 24 | 55 / 46 |
| `05-discussion.tex` | 0 / 1 | 0 / 1 |
| `06-conclusions.tex` | 0 / 2 | 0 / 2 |
| `appendix.tex` | 11 / 2 | 7 / 6 |
| **total** | **189 / 39** | **123 / 100** |

## 2. The rules of §8.2, checked here

| # | Rule (`witness-contract.md` §6.5) | State in this manuscript |
|---|---|---|
| 1 | **One claim, one tag** — no two tags adjacent | **0 violations.** Every pair of marks in the document is separated by a sentence terminator (198 pairs), an environment or display (8), a paragraph break (2) or the paragraph break a `\witness` block issues (3). The five lines that used to carry two tags on one claim were split (§4). |
| 2 | **An external source is the citation, not a tag — and never the key of one** | **0 tag keys hold a `\cite` or a bibliography key** (checked against `src/bibliography.bib`); external sources stay outside the bracket as `in~\cite{key}` / `~\cite{key}` next to the tag. The preamble raises `\PackageError` if a `\cite` is ever written inside the optional argument of `\tier` (the guard of `05-kkgt/main.tex`, ported with the grammar). |
| 3 | A bare tag needs a witness in its sentence | Not re-opened here: every id in this manuscript is the existing one; whether an id should be a `\ref` key or a Lean name is gate §2/§3 of the superseded `20261116_DEC-001_witness_decision_gates.md`, still the author's. |
| 4 | Every `\tier{N}` carries a `\testref{}` | 03 has no `\testref` macro; the `N` keys are the label keys of gate §1 of the superseded `20261116_DEC-001_witness_decision_gates.md` — unchanged, still open. |
| 5 | `\tier{P}` bare = proved here, no name quoted | Used only where a name is not quoted at that point; every other mark carries its ids. |
| 6 | The legend defines the classes and nothing else | The gloss at `01-introduction.tex:302` names the two classes it prints and is exempt from rules 1 and 3. |
| 7 | `P*` available, never printed | Not defined here; the alphabet of this manuscript is `P` and `N`. |
| 8 | **No status tags in captions** | **0** — every `\caption{…}` in `src/chapters/` is free of `\tier`/`\witness`. |

## 3. Placement criterion (§8.5) and how it was applied

The shape of each mark is decided by its ids, never by its class: a claim
goes on a line of its own `\witness{X}{ids}` **iff** `k ≥ 2 ∧ L ≥ 35 ∧
r = 0 ∧ i = 0 ∧ d ≥ 75`, amended by the two labelled heuristics — `u`
(uniformity of the list the mark sits in) and `p` (mark at the close of its
paragraph) — in the order of §8.5: gate 1, gate 3, `u`, `p`, gates 2 and 4.

Read off the manuscript, the quantities are:

- `k ≥ 2` at 131 of 223 marks; `k < 2` at 92 — gate 1 alone forces 92 marks inline;
- `r > 0` at 25 marks — gate 3 forces them inline (4 of them with `k ≥ 2`);
- `i = 1` at **0** marks (no mark closes an `\item`);
- `u` gives no verdict anywhere: **no mark sits inside an `enumerate`,
  `itemize` or `description`** — the run has no census, so `u` abstains at
  every site (a vacuity of this manuscript, recorded, not a defect);
- `p = 1` at 175 marks, which is what keeps most of the 123 blocks in place;
- `d` is `—` (no other block in the paragraph) at 190 marks.

Verdicts: **123 own line** (118 by `p`, 5 by gates 2+4) and **100 inline**
(92 by gate 1, 4 by gate 3, 4 by gates 2/4). The applied state matches the
verdict at **all 223 sites — 0 pending moves**.

**Calibration.** The same code run over `05-kkgt/main.tex` reproduces that
manuscript's own inventory: 231 marks, 17 on a line of its own today, verdict
18 — **not one of 05's own blocks is moved inline**, and one inline mark of
its own would move to a line of its own (a pending move of its WIT-002 pass).
The criterion implemented here is therefore the contract's, not a local
reading of it.

## 4. Reading pass — where the criterion and the prose were reconciled

The site table below prints, for every mark, the tail its rule rests on. The
pass asked one question per row and produced these notes; nothing was left
against the criterion, and nothing was moved against the prose.

1. **Three stacked pairs would have collided.** At `02-methods.tex:707`
   (even zeta), `02-methods.tex:1338` (repulsion) and
   `04-implications.tex:478` (back-reaction) two blocks stood one under the
   other; the criterion sends both inline, and two inline tags at the same
   sentence close would be adjacent (rule 1). Each tag was therefore given
   its own claim instead: the `P` tag moved to the statement it witnesses
   (the display of `eq:even-zeta`, the first sentence of
   `repulsion_modulus_is_one`, the cumulative sum of `rmk:backreaction`) and the
   `N` tag stayed on the sentence it checks. Both are inline, neither pair is
   adjacent, and each tag now sits with the claim it supports.
2. **Three inline marks became blocks** — `04-implications.tex:218`, `:497`
   and `:526`. Each was wrapped in parentheses that held nothing but the tag;
   the parentheses went with the move, so `… as observer (P[…]).` became
   `… as observer.` followed by the block. The paragraph is split there by
   `\witness`, which is what gate 4 (`d ≥ 75`) buys: no second block within
   75 words.
3. **Five pairs of marks share a sentence with no terminator between them**
   and were left as they are, each for a recorded reason: the two glosses
   (`01-introduction.tex:302`, `06-conclusions.tex:32`) define the vocabulary
   and claim nothing (rule 6); `04-implications.tex:30` and `:526` are
   pre-existing sentences that carry one tag per clause and were already
   inline before this pass; and `02-methods.tex:712` is the first note above —
   one sentence, two claims, one tag each, joined by a semicolon.
4. **Marks that follow a display stay where they stood** (the `inplace`
   conversions of the table): the tag replaces the block at the same point,
   so the statement it marks is untouched; the sentence the display closes
   already ends with the display, and no tag was ever written inside a
   display (checked: 0).
5. **Prose was not touched by the criterion.** Stripping every tag from the
   text before and after the pass leaves identical word streams apart from
   the three parenthesis pairs of note 2, the two removed `%` markers and the
   space that now stands between a sentence and its tag — no word, id, claim
   or citation was added, dropped or reworded by the placement pass.

## 5. Site table — every mark, with the seven quantities

`k` ids · `L` characters of the id list · `r` words of the sentence after the
mark · `i` closes an `\item` · `d` words to the nearest block of the
paragraph (`—` = none) · `u` uniformity of the run · `p` paragraph close.
"Rule" is the clause of §8.5 that decided the shape.


| # | Site | Shape before → now | Class | k | L | r | i | d | u | p | Rule that decides it |
|---|------|--------------------|------:|--:|--:|--:|--:|--:|:-:|--:|------|
| 1 | `01-introduction.tex:302` | inline | P | 1 | 3 | 3 | 0 | — | — | 0 | gate 1 (k < 2) |
| 2 | `01-introduction.tex:302` | inline | N | 1 | 3 | 2 | 0 | — | — | 0 | gate 1 (k < 2) |
| 3 | `01-introduction.tex:345` | block → **inline** | P | 1 | 6 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 4 | `01-introduction.tex:376` | block | P | 3 | 53 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 5 | `02-methods.tex:31` | block | P | 4 | 50 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 6 | `02-methods.tex:38` | block | P | 2 | 52 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 7 | `02-methods.tex:43` | block → **inline** | P | 1 | 15 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 8 | `02-methods.tex:56` | block | P | 4 | 72 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 9 | `02-methods.tex:67` | block → **inline** | P | 1 | 23 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 10 | `02-methods.tex:86` | block → **inline** | P | 1 | 17 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 11 | `02-methods.tex:94` | block → **inline** | P | 1 | 14 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 12 | `02-methods.tex:99` | block | P | 3 | 56 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 13 | `02-methods.tex:107` | block → **inline** | P | 1 | 14 | 0 | 0 | 8 | — | 1 | gate 1 (k < 2) |
| 14 | `02-methods.tex:121` | block | P | 4 | 88 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 15 | `02-methods.tex:134` | block | P | 2 | 32 | 0 | 0 | 37 | — | 1 | p (paragraph close) |
| 16 | `02-methods.tex:139` | block → **inline** | P | 1 | 13 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 17 | `02-methods.tex:150` | block → **inline** | P | 1 | 16 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 18 | `02-methods.tex:161` | block → **inline** | P | 1 | 26 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 19 | `02-methods.tex:168` | block → **inline** | N | 1 | 8 | 0 | 0 | 1 | — | 1 | gate 1 (k < 2) |
| 20 | `02-methods.tex:169` | block | P | 2 | 43 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 21 | `02-methods.tex:174` | block → **inline** | P | 1 | 19 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 22 | `02-methods.tex:198` | block | P | 2 | 52 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 23 | `02-methods.tex:212` | block | P | 2 | 43 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 24 | `02-methods.tex:234` | block | P | 3 | 47 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 25 | `02-methods.tex:267` | block | P | 4 | 68 | 0 | 0 | 132 | — | 1 | p (paragraph close) |
| 26 | `02-methods.tex:279` | block → **inline** | P | 1 | 22 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 27 | `02-methods.tex:295` | block | P | 2 | 43 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 28 | `02-methods.tex:306` | block → **inline** | P | 1 | 14 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 29 | `02-methods.tex:316` | block → **inline** | P | 1 | 13 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 30 | `02-methods.tex:332` | block → **inline** | P | 1 | 24 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 31 | `02-methods.tex:362` | block → **inline** | N | 1 | 12 | 0 | 0 | — | — | 0 | gate 1 (k < 2) |
| 32 | `02-methods.tex:410` | block | P | 3 | 70 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 33 | `02-methods.tex:414` | inline | P | 1 | 25 | 16 | 0 | 25 | — | 0 | gate 1 (k < 2) |
| 34 | `02-methods.tex:440` | block | P | 3 | 70 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 35 | `02-methods.tex:502` | block | P | 10 | 235 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 36 | `02-methods.tex:531` | block | P | 2 | 40 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 37 | `02-methods.tex:539` | block | P | 2 | 28 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 38 | `02-methods.tex:545` | block | P | 2 | 29 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 39 | `02-methods.tex:568` | block → **inline** | P | 1 | 17 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 40 | `02-methods.tex:576` | block | P | 4 | 49 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 41 | `02-methods.tex:590` | block | P | 2 | 40 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 42 | `02-methods.tex:607` | block | P | 2 | 44 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 43 | `02-methods.tex:623` | block | P | 2 | 28 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 44 | `02-methods.tex:645` | block | P | 2 | 26 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 45 | `02-methods.tex:656` | block | P | 3 | 41 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 46 | `02-methods.tex:677` | block | P | 2 | 23 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 47 | `02-methods.tex:701` | block | P | 3 | 73 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 48 | `02-methods.tex:704` | block → **inline** | P | 1 | 11 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 49 | `02-methods.tex:712` | block → **inline** | P | 1 | 19 | 7 | 0 | — | — | 0 | gate 1 (k < 2) |
| 50 | `02-methods.tex:714` | block → **inline** | N | 1 | 9 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 51 | `02-methods.tex:738` | block | P | 2 | 53 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 52 | `02-methods.tex:750` | block | P | 3 | 48 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 53 | `02-methods.tex:783` | block | P | 7 | 156 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 54 | `02-methods.tex:819` | block | P | 3 | 62 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 55 | `02-methods.tex:860` | block | P | 3 | 75 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 56 | `02-methods.tex:878` | block → **inline** | P | 1 | 9 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 57 | `02-methods.tex:896` | block | P | 3 | 71 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 58 | `02-methods.tex:947` | block | P | 2 | 42 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 59 | `02-methods.tex:963` | block | P | 2 | 56 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 60 | `02-methods.tex:980` | block | P | 3 | 68 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 61 | `02-methods.tex:999` | block | P | 3 | 64 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 62 | `02-methods.tex:1017` | block → **inline** | P | 1 | 14 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 63 | `02-methods.tex:1080` | block | P | 2 | 41 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 64 | `02-methods.tex:1108` | block | P | 3 | 44 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 65 | `02-methods.tex:1115` | block → **inline** | P | 1 | 22 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 66 | `02-methods.tex:1123` | block | P | 7 | 154 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 67 | `02-methods.tex:1172` | block → **inline** | P | 1 | 20 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 68 | `02-methods.tex:1190` | block | P | 5 | 137 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 69 | `02-methods.tex:1206` | block | P | 7 | 147 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 70 | `02-methods.tex:1218` | block | P | 2 | 43 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 71 | `02-methods.tex:1232` | block | P | 6 | 100 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 72 | `02-methods.tex:1240` | block → **inline** | P | 1 | 18 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 73 | `02-methods.tex:1260` | block | P | 3 | 53 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 74 | `02-methods.tex:1274` | block | P | 3 | 50 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 75 | `02-methods.tex:1283` | block → **inline** | P | 1 | 22 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 76 | `02-methods.tex:1293` | block → **inline** | P | 1 | 17 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 77 | `02-methods.tex:1325` | block | P | 2 | 68 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 78 | `02-methods.tex:1335` | block → **inline** | P | 1 | 24 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 79 | `02-methods.tex:1339` | block → **inline** | N | 1 | 22 | 0 | 0 | — | — | 0 | gate 1 (k < 2) |
| 80 | `02-methods.tex:1340` | block → **inline** | P | 1 | 27 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 81 | `02-methods.tex:1410` | block → **inline** | P | 1 | 30 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 82 | `03-derivations.tex:34` | block → **inline** | P | 1 | 24 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 83 | `03-derivations.tex:53` | block | P | 3 | 70 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 84 | `03-derivations.tex:86` | block | P | 2 | 40 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 85 | `03-derivations.tex:121` | block | P | 2 | 46 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 86 | `03-derivations.tex:196` | block → **inline** | P | 2 | 32 | 0 | 0 | — | — | 0 | gates 2/4 not met |
| 87 | `03-derivations.tex:201` | block → **inline** | N | 1 | 14 | 39 | 0 | — | — | 0 | gate 1 (k < 2) |
| 88 | `03-derivations.tex:216` | block → **inline** | N | 1 | 11 | 0 | 0 | 1 | — | 1 | gate 1 (k < 2) |
| 89 | `03-derivations.tex:217` | block | P | 2 | 38 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 90 | `03-derivations.tex:229` | block | P | 2 | 47 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 91 | `03-derivations.tex:278` | block | P | 2 | 53 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 92 | `03-derivations.tex:298` | block | P | 2 | 43 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 93 | `03-derivations.tex:307` | block → **inline** | P | 1 | 12 | 0 | 0 | — | — | 0 | gate 1 (k < 2) |
| 94 | `03-derivations.tex:362` | block → **inline** | P | 4 | 45 | 0 | 0 | 43 | — | 0 | gates 2/4 not met |
| 95 | `03-derivations.tex:372` | block | P | 2 | 33 | 0 | 0 | 5 | — | 1 | p (paragraph close) |
| 96 | `03-derivations.tex:373` | block | P | 4 | 59 | 0 | 0 | 5 | — | 1 | p (paragraph close) |
| 97 | `03-derivations.tex:398` | block → **inline** | P | 3 | 67 | 0 | 0 | 36 | — | 0 | gates 2/4 not met |
| 98 | `03-derivations.tex:404` | block | P | 11 | 183 | 0 | 0 | 184 | — | 1 | p (paragraph close) |
| 99 | `03-derivations.tex:428` | block | P | 3 | 67 | 0 | 0 | 152 | — | 0 | gates 2+4 |
| 100 | `03-derivations.tex:463` | block → **inline** | P | 1 | 19 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 101 | `03-derivations.tex:497` | block → **inline** | P | 1 | 13 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 102 | `03-derivations.tex:506` | block | P | 2 | 43 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 103 | `03-derivations.tex:549` | inline | N | 1 | 16 | 3 | 0 | — | — | 0 | gate 1 (k < 2) |
| 104 | `03-derivations.tex:550` | inline | N | 1 | 15 | 30 | 0 | — | — | 0 | gate 1 (k < 2) |
| 105 | `03-derivations.tex:585` | block | P | 3 | 46 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 106 | `03-derivations.tex:624` | block | P | 3 | 57 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 107 | `04-implications.tex:30` | inline | P | 2 | 44 | 27 | 0 | — | — | 0 | gate 3 (r > 0) |
| 108 | `04-implications.tex:31` | inline | P | 2 | 39 | 13 | 0 | — | — | 0 | gate 3 (r > 0) |
| 109 | `04-implications.tex:80` | inline | P | 1 | 25 | 0 | 0 | 63 | — | 0 | gate 1 (k < 2) |
| 110 | `04-implications.tex:91` | block | P | 2 | 48 | 0 | 0 | 121 | — | 0 | gates 2+4 |
| 111 | `04-implications.tex:101` | block | P | 4 | 68 | 0 | 0 | 121 | — | 1 | p (paragraph close) |
| 112 | `04-implications.tex:104` | inline | P | 1 | 20 | 0 | 0 | 22 | — | 0 | gate 1 (k < 2) |
| 113 | `04-implications.tex:108` | block | P | 3 | 46 | 0 | 0 | 46 | — | 1 | p (paragraph close) |
| 114 | `04-implications.tex:118` | block | P | 4 | 68 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 115 | `04-implications.tex:125` | block | P | 2 | 27 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 116 | `04-implications.tex:134` | inline | P | 2 | 27 | 0 | 0 | — | — | 0 | gates 2/4 not met |
| 117 | `04-implications.tex:139` | inline | P | 1 | 19 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 118 | `04-implications.tex:164` | inline | P | 1 | 10 | 5 | 0 | 86 | — | 0 | gate 1 (k < 2) |
| 119 | `04-implications.tex:178` | block | P | 3 | 53 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 120 | `04-implications.tex:207` | block → **inline** | P | 1 | 23 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 121 | `04-implications.tex:211` | block → **inline** | P | 1 | 18 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 122 | `04-implications.tex:217` | inline | P | 2 | 48 | 16 | 0 | 17 | — | 0 | gate 3 (r > 0) |
| 123 | `04-implications.tex:219` | inline → **block** | P | 2 | 36 | 0 | 0 | — | — | 0 | gates 2+4 |
| 124 | `04-implications.tex:278` | inline | P | 2 | 52 | 11 | 0 | — | — | 0 | gate 3 (r > 0) |
| 125 | `04-implications.tex:299` | inline | P | 1 | 19 | 21 | 0 | — | — | 0 | gate 1 (k < 2) |
| 126 | `04-implications.tex:317` | inline | P | 1 | 12 | 0 | 0 | — | — | 0 | gate 1 (k < 2) |
| 127 | `04-implications.tex:317` | inline | N | 1 | 12 | 18 | 0 | — | — | 0 | gate 1 (k < 2) |
| 128 | `04-implications.tex:333` | block | P | 3 | 67 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 129 | `04-implications.tex:338` | block | P | 4 | 79 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 130 | `04-implications.tex:345` | block | P | 2 | 39 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 131 | `04-implications.tex:349` | block → **inline** | P | 1 | 19 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 132 | `04-implications.tex:369` | block → **inline** | P | 1 | 24 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 133 | `04-implications.tex:413` | block | P | 2 | 31 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 134 | `04-implications.tex:422` | block → **inline** | P | 1 | 24 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 135 | `04-implications.tex:430` | block → **inline** | P | 1 | 23 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 136 | `04-implications.tex:445` | block → **inline** | P | 1 | 24 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 137 | `04-implications.tex:466` | block | P | 2 | 40 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 138 | `04-implications.tex:480` | block → **inline** | P | 1 | 23 | 0 | 0 | — | — | 0 | gate 1 (k < 2) |
| 139 | `04-implications.tex:483` | block → **inline** | N | 1 | 16 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 140 | `04-implications.tex:494` | inline → **block** | P | 3 | 40 | 0 | 0 | — | — | 0 | gates 2+4 |
| 141 | `04-implications.tex:509` | inline | P | 1 | 16 | 0 | 0 | — | — | 0 | gate 1 (k < 2) |
| 142 | `04-implications.tex:519` | inline | P | 1 | 38 | 14 | 0 | 34 | — | 0 | gate 1 (k < 2) |
| 143 | `04-implications.tex:523` | inline → **block** | P | 2 | 39 | 0 | 0 | — | — | 0 | gates 2+4 |
| 144 | `04-implications.tex:526` | inline | P | 1 | 26 | 12 | 0 | 18 | — | 0 | gate 1 (k < 2) |
| 145 | `04-implications.tex:527` | inline | P | 1 | 24 | 0 | 0 | 30 | — | 0 | gate 1 (k < 2) |
| 146 | `04-implications.tex:534` | block | P | 2 | 34 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 147 | `04-implications.tex:538` | inline | P | 1 | 3 | 1 | 0 | 210 | — | 0 | gate 1 (k < 2) |
| 148 | `04-implications.tex:568` | block → **inline** | N | 1 | 16 | 0 | 0 | 1 | — | 1 | gate 1 (k < 2) |
| 149 | `04-implications.tex:569` | block | P | 2 | 39 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 150 | `04-implications.tex:579` | block → **inline** | P | 1 | 8 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 151 | `04-implications.tex:593` | block | P | 7 | 90 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 152 | `04-implications.tex:605` | block | P | 3 | 43 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 153 | `04-implications.tex:628` | block | P | 7 | 136 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 154 | `04-implications.tex:631` | inline | P | 1 | 18 | 47 | 0 | — | — | 0 | gate 1 (k < 2) |
| 155 | `04-implications.tex:633` | inline | P | 1 | 19 | 39 | 0 | — | — | 0 | gate 1 (k < 2) |
| 156 | `04-implications.tex:642` | block → **inline** | P | 1 | 9 | 0 | 0 | — | — | 0 | gate 1 (k < 2) |
| 157 | `04-implications.tex:650` | block → **inline** | N | 1 | 15 | 0 | 0 | 1 | — | 1 | gate 1 (k < 2) |
| 158 | `04-implications.tex:651` | block | P | 5 | 82 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 159 | `04-implications.tex:662` | block → **inline** | P | 1 | 17 | 0 | 0 | 71 | — | 0 | gate 1 (k < 2) |
| 160 | `04-implications.tex:732` | block → **inline** | N | 1 | 24 | 0 | 0 | 1 | — | 1 | gate 1 (k < 2) |
| 161 | `04-implications.tex:733` | block | P | 11 | 204 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 162 | `04-implications.tex:758` | block | P | 3 | 74 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 163 | `04-implications.tex:1024` | block → **inline** | N | 1 | 17 | 0 | 0 | — | — | 0 | gate 1 (k < 2) |
| 164 | `04-implications.tex:1025` | block → **inline** | P | 1 | 19 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 165 | `04-implications.tex:1052` | block | P | 2 | 25 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 166 | `04-implications.tex:1067` | block | P | 4 | 79 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 167 | `04-implications.tex:1082` | block | P | 2 | 51 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 168 | `04-implications.tex:1111` | block | P | 5 | 99 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 169 | `04-implications.tex:1135` | block | P | 3 | 38 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 170 | `04-implications.tex:1152` | block | P | 6 | 141 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 171 | `04-implications.tex:1162` | block | P | 2 | 54 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 172 | `04-implications.tex:1170` | block | P | 3 | 43 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 173 | `04-implications.tex:1181` | block | P | 3 | 49 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 174 | `04-implications.tex:1195` | block | P | 3 | 73 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 175 | `04-implications.tex:1221` | block | P | 2 | 39 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 176 | `04-implications.tex:1240` | block | P | 2 | 39 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 177 | `04-implications.tex:1250` | block | P | 2 | 36 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 178 | `04-implications.tex:1277` | block | P | 2 | 33 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 179 | `04-implications.tex:1288` | block | P | 4 | 98 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 180 | `04-implications.tex:1301` | block | P | 4 | 78 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 181 | `04-implications.tex:1330` | block | P | 4 | 114 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 182 | `04-implications.tex:1359` | block → **inline** | P | 1 | 13 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 183 | `04-implications.tex:1377` | block → **inline** | P | 1 | 19 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 184 | `04-implications.tex:1415` | block | P | 9 | 201 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 185 | `04-implications.tex:1451` | block | P | 3 | 71 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 186 | `04-implications.tex:1467` | block | P | 5 | 125 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 187 | `04-implications.tex:1482` | block | P | 3 | 75 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 188 | `04-implications.tex:1488` | block → **inline** | P | 1 | 13 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 189 | `04-implications.tex:1494` | block → **inline** | P | 1 | 22 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 190 | `04-implications.tex:1509` | block → **inline** | N | 1 | 14 | 0 | 0 | 1 | — | 1 | gate 1 (k < 2) |
| 191 | `04-implications.tex:1510` | block | P | 2 | 53 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 192 | `04-implications.tex:1532` | inline | N | 1 | 17 | 4 | 0 | — | — | 0 | gate 1 (k < 2) |
| 193 | `04-implications.tex:1540` | inline | P | 1 | 22 | 13 | 0 | 159 | — | 0 | gate 1 (k < 2) |
| 194 | `04-implications.tex:1563` | block | P | 4 | 81 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 195 | `04-implications.tex:1568` | block | P | 4 | 88 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 196 | `04-implications.tex:1577` | block | P | 5 | 135 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 197 | `04-implications.tex:1582` | block | P | 3 | 52 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 198 | `04-implications.tex:1587` | block → **inline** | P | 1 | 9 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 199 | `04-implications.tex:1592` | block | P | 2 | 28 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 200 | `04-implications.tex:1664` | block | P | 3 | 67 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 201 | `04-implications.tex:1680` | block → **inline** | N | 1 | 16 | 0 | 0 | 1 | — | 1 | gate 1 (k < 2) |
| 202 | `04-implications.tex:1681` | block | P | 4 | 77 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 203 | `04-implications.tex:1690` | block → **inline** | P | 1 | 19 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 204 | `04-implications.tex:1696` | block | P | 9 | 206 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 205 | `04-implications.tex:1700` | block | P | 4 | 74 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 206 | `04-implications.tex:1736` | block | P | 3 | 46 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 207 | `04-implications.tex:1773` | block | P | 3 | 58 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 208 | `05-discussion.tex:94` | inline | P | 1 | 14 | 0 | 0 | — | — | 0 | gate 1 (k < 2) |
| 209 | `06-conclusions.tex:32` | inline | P | 1 | 3 | 2 | 0 | — | — | 0 | gate 1 (k < 2) |
| 210 | `06-conclusions.tex:32` | inline | N | 1 | 3 | 1 | 0 | — | — | 0 | gate 1 (k < 2) |
| 211 | `appendix.tex:6` | inline | P | 1 | 3 | 26 | 0 | — | — | 0 | gate 1 (k < 2) |
| 212 | `appendix.tex:39` | block → **inline** | P | 1 | 38 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 213 | `appendix.tex:99` | block → **inline** | P | 1 | 27 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 214 | `appendix.tex:201` | block | P | 2 | 43 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 215 | `appendix.tex:229` | block | P | 5 | 91 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 216 | `appendix.tex:250` | block → **inline** | P | 1 | 15 | 0 | 0 | — | — | 0 | gate 1 (k < 2) |
| 217 | `appendix.tex:264` | block | P | 3 | 75 | 0 | 0 | 11 | — | 1 | p (paragraph close) |
| 218 | `appendix.tex:265` | block | N | 2 | 28 | 0 | 0 | 11 | — | 1 | p (paragraph close) |
| 219 | `appendix.tex:276` | inline | P | 1 | 14 | 18 | 0 | 47 | — | 0 | gate 1 (k < 2) |
| 220 | `appendix.tex:281` | block | P | 4 | 96 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 221 | `appendix.tex:303` | block → **inline** | P | 1 | 15 | 0 | 0 | — | — | 1 | gate 1 (k < 2) |
| 222 | `appendix.tex:313` | block | P | 2 | 43 | 0 | 0 | — | — | 1 | p (paragraph close) |
| 223 | `appendix.tex:336` | block | P | 7 | 136 | 0 | 0 | — | — | 1 | p (paragraph close) |
## 6. Verification (literal output)

```
$ grep -rn 'HypWitness' src/ main.tex | wc -l
0

$ grep -rn 'ProofWitness\|NumericalWitness\|HypWitness' src/ main.tex | wc -l
0

$ grep -rln 'ProofWitness\|NumericalWitness\|HypWitness' . --exclude-dir=...
./CHANGELOG.md
./docs/witness-decisions.md
        (the generated release history and this family of decision records;
         no .tex file of the manuscript mentions a retired macro)

$ <scan every \caption{...} for \tier[ / \witness{>
captions with a tag: 0

$ python3 witness_criterion.py        # the criterion, re-read on the applied tree
marks: 223 {'inline': 100, 'block': 123} -> verdict {'inline': 100, 'block': 123}
MOVES: 0 {}

$ pnpm run type-check
> tsc --noEmit
(exit 0, no diagnostics)

$ uv run python -m pytest tests/ -q
============================= 571 passed in 23.77s =============================
        (570 at the start of this pass; the suite grew by one under the
         concurrent work in tests/, which this pass does not touch)

$ pnpm run build
Output written on build/main.pdf (97 pages, 2247283 bytes).
✅ Build completed successfully for v1.2.1
(final build/main.log: 0 lines starting with "!", 0 "undefined" references,
 7 Overfull \hbox — the baseline carried 6, and not one of the seven sits on
 a line that contains a tag: they are the pre-existing heading, math and
 long \texttt lines)
```

**Census of claim marks:** 217 at `19e96cb` → **217** now — every claim
carries its tag, with the same ids, before and after the pass.
