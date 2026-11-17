# Witness decision gates — 03-crystalline-worldsheet

**For:** the main author.
**Purpose:** every remaining choice about the verification-tag system (`\ProofWitness*`, `\NumericalWitness*`, `\HypWitness*`) is written here as a *gate*: one row, one decision, one recommendation, one exact replacement text. Nothing in this file has been applied except §0, which records the mechanical pass already done.
**How to use it:** read the *Recommendation* cell, then tick the checkbox. `[ ]` = open gate, `[x]` = you accepted the recommendation as written. A row with a different choice: write your variant in *Notes* — the recommended text is there so you never have to compose an edit yourself. Every gate in this file ships with a recommendation, so the whole document is green once you tick it.

---

## Executive summary

| § | Decision class | Gates | Recommended outcome |
|---|----------------|------:|---------------------|
| 0 | Mechanical normalization (already applied, no decision needed) | — (12 edits) | done; verified by build + test suite |
| 1 | `N` focus — a real test id for every `\NumericalWitness*` argument | 19 | (i) use exact id ×16 · (ii) new test ×2 · (iii) reformulate ×1 |
| 2 | Redundancy: tag key = `\ref` key in the same paragraph | 12 | replace the duplicated key with the witness id (×10) · accept as documented rule (×2) |
| 3 | Tag whose key has no `\ref` in its paragraph | 7 | add `\eqref` (×5) · accept — equation displayed in the same paragraph (×2) |
| 4 | Class `H` — "hypothesis from the literature", 0 uses on claims | 1 (3 edits) | **applied 2026-11-16**: remove the class (same precedent as `L` in 05-kk) — see §4 |
| 5 | Dead macros `\tier`, `\HypWitnessBlock`, `\Conj` | 3 | delete `\Conj` · tie `\HypWitnessBlock` to §4 · tie `\tier` to §6 |
| 6 | Family alignment with 05-kk grammar (`\tier{X}` / `\tier[KEY]{X}`) | 1 | adopt in a later pass (not now) |
| 7 | Prose uniformity, orphan fragments, tag-vs-phrase contradictions, census test | 8 | unify verbs (×1), repair 2 orphan fragments, 1 environment line, add census test (×1), resolve 3 tag-vs-phrase contradictions |
| | **Total open gates** | **50** | (51 checkboxes: §6 is one decision with two mutually exclusive ticks; §4 closed 2026-11-16) |

Counts behind §1: 19 `N` keys over 18 `\NumericalWitness*` calls (`appendix.tex:266` carries two keys). 3 further calls are legend/meta uses with `{...}` and are *not* gates (§1.0).

---

## §0 — Applied mechanical pass (no author decision; recorded for the record)

Re-verified from scratch before editing. Applied changes, by file:line (numbers **after** the edit):

| # | File:line | Change |
|---|-----------|--------|
| A1 | `appendix.tex:265-266` | two blocks that shared one source line → split, `P` block then `N` block, one per line |
| A2 | `01-introduction.tex:317 → 342` | `\ProofWitnessBlock{phi\_sq}` moved from mid-sentence (after `\end{equation}` of `eq:phisq`, before "which extends…") to the end of the paragraph ("…mounted on a torus.") |
| A3 | `01-introduction.tex:361 → 373` | `\ProofWitnessBlock{lambda\_log, lambda\_log\_mul\_regulator, mersenne\_bridge}` moved from mid-sentence ("…anchored by the algebraic bridge [eq] BLOCK so that…") to the end of the paragraph ("…spectrum of the primes.") |
| A4 | `02-methods.tex:629 → 631` | block moved out of the middle of the proposition statement to just before `\end{proposition}` (after the `Lucas1878` citation) |
| A5 | `03-derivations.tex:370 → 377` | `\ProofWitnessBlock{hopf\_latitude, hopf\_from\_clifford}` moved from between two sentences to the end of its paragraph (immediately before the `hypercube_card…` block, preserving sentence order) |
| A6 | `04-implications.tex:330 → 329 + 332` | orphan fragment restored: `$S=\ln N$.` + `(by \texttt{rfl}---the most direct realisation).` → `$S=\ln N$ (by \texttt{rfl}---the most direct realisation).` (every word of the fragment kept, no new wording); block moved to the end of the paragraph, after "…the unitarity branch is ``realised''." Git evidence: commit `01f8e35` ("remove orphaned Proof:, dots, and parentheses around ProofWitnessBlocks") deleted the sentence's subject and left the parenthesis dangling |
| A7 | `03-derivations.tex:502 → 504` | `\ProofWitness{c\_tendsto\_two}` removed from inside the `align` environment (last row) → `\ProofWitnessBlock{c\_tendsto\_two}` on its own line after `\end{align}`; `\label{eq:bridge-fixed}` stays in the row |
| A8 | `02-methods.tex:370` | `\NumericalWitness{eq:certainty}` alone on a left-aligned line → `\NumericalWitnessBlock{eq:certainty}`: same pattern as every other marker that closes a display (`01:342`, `02:709`, `03:203`); a left-floated inline tag on its own line was the only instance of its kind |
| A9 | `04-implications.tex:739-740` | inverted stack corrected: `P` block now first, `N` block second (order used at every other stacked pair) |
| A10 | `02-methods.tex:709` | broken `P` name: `{eq:local-dedekind}` → `{local\_dedekind\_ramified\_K, local\_dedekind\_split\_K, local\_dedekind\_inert\_K}` (verified `lean/CW6_complete_v2.lean:3655/3660/3665`; same three names already used at `02-methods.tex:791`) |
| A11 | `04-implications.tex:423` | broken `P` name: `{prop:shell-tension}` → `{shell\_tension\_determined}` (verified `lean/CW6_complete_v2.lean:5568`) |
| A12 | `04-implications.tex:536` | broken `P` name: `dS\_temperature` → `ds\_temperature` (verified `lean/CW6_complete_v2.lean:2110`; `dS_temperature` does not exist in the file) |

Also incidentally: dropped one stray leading space at `04-implications.tex:536` (cosmetic, same edit as A12).

**Left alone on purpose:** all `{...}` placeholders (5 `P` + 3 `N`) — they are legend/meta prose, not witnesses on a claim: `02-methods.tex:8,10` (the legend), `06-conclusions.tex:32` (points at "the tags of the abstract"), `04-implications.tex:540` ("their proofs are those of the corresponding `\ProofWitness{...}` tags"), `appendix.tex:6` ("The `\ProofWitness{...}` tags certify…"). None asserts a specific witness, so none is a false witness. No mathematical text, no citation and no `lean/` file was touched.

**Post-edit census** (all names re-checked against `lean/CW6_complete_v2.lean`):
`\ProofWitnessBlock` 175 · `\ProofWitness` 29 · `\NumericalWitnessBlock` 14 · `\NumericalWitness` 7 · `\HypWitness` 3 (1 is a comment) · `\HypWitnessBlock` 0 · `\tier` 0 · `\Conj` 0 · Lean names named by `P` tags: **491/491 resolve** (was 489/492).

**Verification (literal output):**

```
$ pnpm run type-check
> tsc --noEmit
(exit 0, no diagnostics)

$ uv run python -m pytest tests/ -q
============================= 570 passed in 20.45s =============================

$ pnpm run build
Output written on build/main.pdf (97 pages, 2051994 bytes).
✓ Compiled build/document-v1.2.1.pdf with SOURCE_DATE_EPOCH=1794283980
✅ Build completed successfully for v1.2.1
(final build/main.log: 0 lines starting with "!", 0 "undefined" references, 6 Overfull \hbox)
```

The **first** build attempt failed (`latexmk failed with exit code 12`, `! Missing $ inserted` twice, `build/main.log:3293,3305`): the patch that moved the block at `03-derivations.tex:370` had swallowed the `$…$` delimiters of `S(\sigma)=\pi\golden^{\sigma}`. Repaired by restoring the delimiters exactly as in `HEAD`; the successful build above is the re-run. Nothing else was reverted — every other edit survives verification.

Side effects of running the build (regenerated by the pipeline, not edited by hand): `build/document-v1.2.1.pdf`, `checksums.txt`, `CITATION.cff` / `.zenodo.json` (`date-released` rolled `2026-11-10 → 2026-11-11` in UTC). No commit was made; `git status` shows only these files plus the five `.tex` chapters and this document.

---

## §1 — The `N` focus: one real test id per numerical witness

Same contract as 05-kk §8: an `N` tag is valid only if a test actually recomputes the number next to it. The ids below were collected from this repo with `uv run python -m pytest tests/ --collect-only -q` (570 tests) and matched to each claim by reading the test body, not by name alone.

**Gate options** (per row): **(i)** put that exact test id in the tag · **(ii)** add a new test (name + what it must assert, given) and use it · **(iii)** rewrite the sentence/tag so it says what is actually checked (replacement text given) · **(iv)** drop the tag.

| ✓ | # | Site (post-fix) | Claim the tag supports | Real test id (or the gap) | Recommendation |
|---|---|---|---|---|---|
| [ ] | 1 | `02-methods.tex:176` `N[eq:phisq]` | the root behind `thm:fib-min` satisfies $\varphi^2=\varphi+1$ | `tests/test_core_identities.py::TestDimensionLadder::test_phi_identity` (`assert abs(PHI**2 - (PHI+1)) < 1e-12`) | **(i)** |
| [ ] | 2 | `02-methods.tex:370` `N[eq:certainty]` | the Certainty Principle $\varepsilon_0 M_{\rm PCF}=\pi$ | `tests/test_core_identities.py::TestCertainty::test_certainty_product` | **(i)** |
| [ ] | 3 | `02-methods.tex:723` `N[thm:basel]` | $k=1$ of the even-zeta formula: $\zeta(2)=\pi^2/6$ | **no test asserts it.** `tests/test_arithmetic.py::TestSigmaDiagram::test_analytic_route` *consumes* `mpzeta(2)` as an input; nothing compares it to $\pi^2/6$ | **(ii)** add `tests/test_arithmetic.py::TestEvenZeta::test_basel` asserting `abs(mpzeta(2) - pi**2/6) < mpf('1e-20')`; fallback **(iv)** |
| [ ] | 4 | `02-methods.tex:1357` `N[prop:repulsion-modulus]` | under the hypotheses, $|1-1/\rho|=1$ exactly | `tests/test_spectral.py::TestLiModulus::test_equivalence` (docstring: `eq:li-modulus: |1-1/rho| = 1 iff Re rho = 1/2`) | **(i)** — see also §3 row 4 (only key never `\ref`'d anywhere in the document) |
| [ ] | 5 | `03-derivations.tex:203` `N[eq:tower-modes]` | $N_{\rm modes}(\sigma)=\lfloor\pi\varphi^\sigma\rfloor$ | `tests/test_tower.py::TestTowerModes::test_individual[6-56]` (parametrised over $\sigma=0..6$) | **(i)** |
| [ ] | 6 | `03-derivations.tex:220` `N[thm:fib-min]` | prose: $N_{\rm modes}(6)=56$ while the Fibonacci value is $55$; "the staircase is $\pi$-scaled and only *shadows* the recurrence" | the theorem itself is Lean-only (P tag on line 219); **no test asserts `thm:fib-min`** (depth-2 minimality). `test_individual[6-56]` checks the 56, not the theorem | **(iii)** retag to what is checked: `\NumericalWitnessBlock{eq:tower-modes}` (sentence unchanged); alternative **(ii)** `tests/test_tower.py::TestTowerModes::test_six_not_fib` asserting `nmodes(6) == 56 and 55 != 56` |
| [ ] | 7 | `03-derivations.tex:556` `N[eq:obs-swampland]` | $|\partial_\sigma V|/V=\ln\varphi$ | `tests/test_observer.py::TestObserverSwampland::test_logarithmic_derivative[0.0]` (+ `[1.5]`, `[3.0]`, `[6.0]`) | **(i)** — same line also has `\eqref{eq:obs-swampland}` → §2 |
| [ ] | 8 | `03-derivations.tex:556` `N[eq:obs-jacobson]` | $R_{AB}k^Ak^B=0$ for all null $k$ | `tests/test_observer.py::TestObserverJacobson::test_null_contraction_vanishes` (+ `test_discriminates_nonnull`) | **(i)** |
| [ ] | 9 | `04-implications.tex:316` `N[eq:certainty]` | "…and checked numerically" in the `asm:bridge` sentence | `tests/test_core_identities.py::TestCertainty::test_certainty_product` | **(i)** — also §2 |
| [ ] | 10 | `04-implications.tex:487` `N[eq:shell-tension]` | $\lambda_\sigma=N_{\rm modes}(\sigma)/M_{\rm PCF}$, feeding the cumulative back-reaction $3,8,16,29,50,84,140$ | the **sequence** is checked (`tests/test_tower.py::TestTowerModes::test_cumulative`), **eq:shell-tension itself is asserted nowhere** (`grep -rE 'shell_tension\|lambda_sigma' tests/` → 0) | **(ii)** add `tests/test_gravity.py::TestShellTension::test_lambda_eq_nmodes_over_mpcf` asserting `abs(nmodes(s)/M_PCF - lam(s)) < 1e-12 for s in range(7)`; alternative **(iii)** retag to the cumulative claim and use `test_cumulative`; fallback **(iv)** |
| [ ] | 11 | `04-implications.tex:572` `N[prop:entropy-max]` | $f_{\rm crit}=\mu_3=1/2$ is the maximum-entropy point $H(1/2)=1$ bit | `tests/test_arithmetic.py::TestEntropyMax::test_max_at_half` (+ `test_below_one`) | **(i)** |
| [ ] | 12 | `04-implications.tex:656` `N[eq:obs-landauer]` | Landau–Lifshitz/energy-per-bit claim of `thm:LL-energy` | `tests/test_observer.py::TestObserverLandauer::test_energy_per_bit` (docstring: `eq:obs-landauer: energy/bit = 1/M_PCF; S_BH/k_B = log 2`) | **(i)** |
| [ ] | 13 | `04-implications.tex:740` `N[eq:Lambda-from-curvature]` | the scale from curvature, $\sigma_{\rm obs}=\ln(6/\Lambda_{\rm obs})/\ln\varphi$ with $\Lambda_5=-d(d-1)/2=-6$ | `tests/test_gravity.py::TestEinsteinCurvature::test_lambda5` (`assert LAMBDA_5 == -6`) | **(i)**; optional **(ii)** a new test `tests/test_observer.py::TestDeSitterGeometry::test_sigma_obs` (does not exist yet) asserting `sigma_obs == log(6/LAMBDA)/log(PHI)` if you want the $\sigma_{\rm obs}$ step itself covered |
| [ ] | 14 | `04-implications.tex:1031` `N[cor:golden-growth]` | "the growth is golden, $\varphi$ per level" | `tests/test_tower.py::TestTowerModes::test_ratio_is_phi` ("Tower step ratio is exactly φ") — contrary to the earlier audit, a test *does* check the rate | **(i)** — also §2 (the sentence already cites `Corollary~\ref{cor:golden-growth}`) |
| [ ] | 15 | `04-implications.tex:1519` `N[prop:veneziano]` | Regge tower = Euler product = $\zeta(s)$ | `tests/test_places.py::TestReggeTower::test_dirichlet_eq_zeta[s0]` (+ `test_euler_product`) | **(i)** |
| [ ] | 16 | `04-implications.tex:1541` `N[eq:string-tension]` | dual-superconductor: $\sigma_{\rm tension}=q_m^2V>0$, $\Delta=\sqrt{\sigma}>0$ | `tests/test_transmutation.py::TestColourGap::test_positive` (asserts exactly `q**2*V_MEISSNER > 0` and its square root) | **(i)** — see §7.4: this inline tag currently splits the sentence |
| [ ] | 17 | `04-implications.tex:1691` `N[eq:transmutation]` | gap independent of the cutoff; $\Lambda_{\rm QCD}=\Lambda>0$ | `tests/test_transmutation.py::TestGapSurvivesTransmutation::test_finite` + `tests/test_transmutation.py::TestLambdaQCDPositivity::test_positive` | **(i)** |
| [ ] | 18 | `appendix.tex:266` `N[eq:kk-rowsum]` | the row-sum numerator equals 1 only for $\varphi$ | `tests/test_kk.py::TestKKSpectrum::test_interior_row_sum` ("Interior row sum = 1/ln²φ (the numerator is 1)") + `tests/test_kk.py::TestKKNumerator::test_numerator_value` | **(i)** |
| [ ] | 19 | `appendix.tex:266` `N[eq:kk-spectrum]` | numerical KK spectrum = closed form, $m^2>0$ | `tests/test_kk.py::TestKKSpectrum::test_numerical_equals_closed` (+ `test_mass_squared_positive`) | **(i)** |

**§1.0 — the three `{...}` `N` uses** (`02-methods.tex:8,10`, `06-conclusions.tex:32`): illustrative legend/abstract prose; **leave as they are** (no gate).

**The four "no test possible" rows from the previous audit, made explicit** — each needs your tick, not a guess from me:

- `thm:basel` (#3): **new test or drop the tag?** Recommendation: new test (one line, `mpzeta(2)` vs `pi**2/6`).
- `thm:fib-min` (#6): **new test or retag/rewrite?** Recommendation: retag to `eq:tower-modes` — the prose already states the checked numbers.
- `eq:shell-tension` (#10): **new test or rewrite?** Recommendation: new test (one line, $\lambda_\sigma=N_{\rm modes}(\sigma)/M_{\rm PCF}$).
- `cor:golden-growth` (#14): audit said "no test possible"; `test_ratio_is_phi` does check the rate → recommendation **(i)** instead of a new test.

---

## §2 — Redundancy: tag key and `\ref` of the *same* key in the same paragraph

Criterion used (reproducible): the witness argument `K` is redundant when the source paragraph that contains the tag also contains `\ref{K}` or `\eqref{K}` — the bracket then says twice what the same label says once. 12 instances post-fix (the audit's 11 + `appendix` `eq:kk-rowsum`; `04:423` and `02:709` *left* this list because A11/A10 renamed their keys to Lean names, which is exactly the fix recommended here).

**Gate options:** **(A)** replace the duplicated key by the witness id from §1 (tag and `\ref` then carry different information: the ref points at the statement, the tag names what verifies it) · **(B)** drop the tag · **(C)** keep both and codify in `docs/citations.md` "the tag marks the class, the ref points at the statement".

| ✓ | # | Site | Key (tag = ref) | Recommendation |
|---|---|------|-----------------|----------------|
| [ ] | 1 | `02-methods.tex:723` | `thm:basel` | **(A)** → §1 #3 |
| [ ] | 2 | `03-derivations.tex:203` | `eq:tower-modes` | **(A)** → §1 #5 |
| [ ] | 3 | `03-derivations.tex:220` | `thm:fib-min` | **(A)** → §1 #6 (retag `eq:tower-modes`) |
| [ ] | 4 | `03-derivations.tex:556` | `eq:obs-swampland` | **(A)** → §1 #7 |
| [ ] | 5 | `03-derivations.tex:556` | `eq:obs-jacobson` | **(A)** → §1 #8 |
| [ ] | 6 | `04-implications.tex:316` | `eq:certainty` | **(A)** → §1 #9 |
| [ ] | 7 | `04-implications.tex:487` | `eq:shell-tension` | **(A)** → §1 #10 |
| [ ] | 8 | `04-implications.tex:572` | `prop:entropy-max` | **(A)** → §1 #11 |
| [ ] | 9 | `04-implications.tex:1031` | `cor:golden-growth` | **(A)** → §1 #14 |
| [ ] | 10 | `04-implications.tex:1519` | `prop:veneziano` | **(A)** → §1 #15 |
| [ ] | 11 | `04-implications.tex:1541` | `eq:string-tension` | **(A)** → §1 #16; if you prefer not to touch it, **(C)** |
| [ ] | 12 | `appendix.tex:266` | `eq:kk-rowsum` | **(A)** → §1 #18 |

If §1 ends up choosing **(iv)** for a row, its §2 row closes automatically (no tag, no redundancy) — mark it `[x]` when that happens.

---

## §3 — Tags whose key has no `\ref` in its paragraph

7 instances (the audit listed 2 — `04:1541` and `02:370` — both are included here; the wider count comes from the paragraph criterion above). Every key **does** have a `\label` somewhere, so none is broken — the question is whether the tag is the reader's only pointer.

**Gate options:** **(A)** add `\eqref{KEY}` in the sentence · **(B)** accept the block tag as the pointer (equation/proposition is displayed in the same paragraph) and codify that rule · **(C)** drop the tag.

| ✓ | # | Site | Key | Where its label lives | Recommendation |
|---|---|------|-----|-----------------------|----------------|
| [ ] | 1 | `02-methods.tex:176` | `eq:phisq` | `01-introduction.tex:314` (another chapter) | **(A)** — the tag points across a chapter boundary with no `\eqref` in sight; add `\eqref{eq:phisq}` after "…positive root of $r^2=r+1$ is $\golden$." |
| [ ] | 2 | `02-methods.tex:370` | `eq:certainty` | `02-methods.tex:367` — displayed four lines above | **(B)**: the equation is right there; the tag is the marker, not a missing pointer |
| [ ] | 3 | `02-methods.tex:1357` | `prop:repulsion-modulus` | `02-methods.tex:1353` — the proposition the tag sits in. **Never `\ref`'d anywhere in the document** (only such key) | **(B)** for the tag (it is inside its own environment); separately consider adding a `\ref{prop:repulsion-modulus}` where the result is later used, or dropping the label — *your call, outside the tag system* |
| [ ] | 4 | `04-implications.tex:656` | `eq:obs-landauer` | `04-implications.tex:392` (displayed 260 lines earlier) | **(A)** — add `\eqref{eq:obs-landauer}` in the `thm:LL-energy` statement |
| [ ] | 5 | `04-implications.tex:740` | `eq:Lambda-from-curvature` | `04-implications.tex:662` (displayed in the previous remark) | **(A)** — add `\eqref{eq:Lambda-from-curvature}` after the $\sigma_{\rm obs}$ display |
| [ ] | 6 | `04-implications.tex:1691` | `eq:transmutation` | `04-implications.tex:1680` — displayed in the same paragraph | **(B)** |
| [ ] | 7 | `appendix.tex:266` | `eq:kk-spectrum` | `appendix.tex:222` (its sibling `eq:kk-rowsum` *is* `\eqref`'d in the paragraph) | **(A)** — add `\eqref{eq:kk-spectrum}` where the closed-form spectrum is written, or **(B)** if you consider the paragraph's $\varphi^2+\varphi^{-2}=3$ line sufficient |

---

## §4 — The `H` class ("hypothesis from the literature")

**State:** defined in the legend (`02-methods.tex:9`), mentioned once in the conclusions (`06-conclusions.tex:32`), one commented use (`03-derivations.tex:45`), **zero uses on a claim**. Every hypothesis-from-the-literature statement in the text already carries its `\cite`.

**Gate:** **(R)** remove the class — the same decision 05-kk took when it deleted `L`: the citation *is* the witness for an external claim, and a legend sentence that describes a class the paper never prints is a promise the text does not keep. · **(K)** keep it and start using it on claims · **(P)** keep it defined but unmentioned (delete the legend clause only).

| ✓ | Recommendation |
|---|----------------|
| [x] | **(R) remove.** Exact edits: `02-methods.tex:9` drop `$\HypWitness{...}$ hypothesis from the literature.` (legend becomes "…$N$ numerical check. Compound tags …"); `06-conclusions.tex:32` drop `$\HypWitness{...}/`; `03-derivations.tex:45` delete the commented `% \HypWitness{}`; then §5's `\HypWitnessBlock` gate closes automatically. Reason for (R) over (K): a zero-use class costs a legend sentence and a macro, and the 05-kk precedent says the alphabet should list only what the text prints. |

**Applied (2026-11-16).** The legend had moved to `01-introduction.tex:302-304` since the audit, so the three edits landed there: the gloss clause was dropped (the sentence now closes at "…numerical check."), the conclusions list at `06-conclusions.tex:32` now reads `$\ProofWitness{...}$/$\NumericalWitness{...}$`, the comment `% \HypWitness{}` was deleted from `03-derivations.tex:45`, and both macros (`\HypWitness`, `\HypWitnessBlock`) were deleted from `main.tex`. Verification: `grep -rn 'HypWitness' src/ main.tex` → **0**. The only remaining mentions in the repository are this decision record and the generated `CHANGELOG.md` history, which describe the removal rather than use the class.

---

## §5 — Dead macros in `main.tex`

| ✓ | Macro | Line | Uses | Recommendation |
|---|-------|------|-----:|----------------|
| [ ] | `\Conj` | `main.tex:126` | 0 (already removed from the legend by commit `7bb9d93`) | **delete** — a class the printed text cannot show; leaving it invites an unreachable tag |
| [ ] | `\HypWitnessBlock` | `main.tex:125` | 0 | **delete iff §4 = (R)**; otherwise keep for symmetry with `\HypWitness`. *Factual note: §4 was ticked (R) on 2026-11-16, so the macro was deleted with it — the box is left for the author.* |
| [ ] | `\tier` | `main.tex:79` | 0 | **decide with §6**: if you adopt the family grammar, `\tier` becomes the core macro (keep/extend); if you keep 03's own system, **delete** it. It is the only one of the three whose fate is genuinely a family question |

*(Colours `tagP/tagN/tagH` at `main.tex:86-88` are all in use except `tagH`, which follows §4.)*

---

## §6 — Family alignment with 05-kk (optional, **not applied**)

05-kk's grammar: one macro, `\tier{X}` → `[X]` when the witness sits in the sentence, `\tier[KEY]{X}` → `X[n]` fused with an AMS citation, `\witness{X}{a,b}` for the flush-right block; alphabet `P`/`N` only (`L`, `R` deleted); "one claim, one tag"; the set of cited tests pinned by `tests/test_section_census.py`.

| ✓ | Option | Pros | Cons |
|---|--------|------|------|
| [ ] | **(F1) Adopt the family grammar in 03** | one macro instead of six; the bracket-tag-with-witness rule is already written down in `05-kk/docs/citations.md` §8; the `P/N` alphabet is identical to what 03 prints today; makes §1's test ids the *standard* witness form | touches ~189 witness call sites and `main.tex`; 03's block-flush-right convention differs from `\witness`; needs a migration commit and a re-build |
| [ ] | **(F2) Keep 03's own system** | zero churn; the macros already render what the paper needs; §1–§4 fix the semantics without a migration | two grammars inside the family; every future cross-repo edit must know which one it is in |

**Recommendation: (F1), in a later pass of its own** — the semantics gates (§1–§4) should land first, because they change *what* the tags say, and only then should a migration change *how* they are spelled. Not applied here, as instructed.

**Documentary progress (the gate stays open).** Both references F1 depends on are now reachable from inside this repository:

- the family witness contract, `05-kkgt/docs/citations.md` §8: <https://github.com/omega-pcf/05-kkgt/blob/main/docs/citations.md>;
- the family style guide, ported to this repository as [`style-guide.md`](style-guide.md) (port of `05-kkgt/docs/style-guide.md` v2.2), whose header links that §8 instead of copying it — this repository's own [`citations.md`](citations.md) still ends at §7.

Nothing of the decision itself has moved: the checkbox stays `[ ]`. Aligning the alphabet, the compound-tag form (`\tier[KEY]{X}`) and the quantified criterion is still the author's decision, and no macro, gloss, `.tex` file, test or `lean/` file was touched in recording this.

---

## §7 — Prose consistency after the mechanical pass

### 7.1 Verb inventory (whole `src/chapters/`)

| Phrase | Count | Lines |
|--------|------:|-------|
| "numerically" (incl. the two above) | 7 | `01:259`, `02:629`, `02:1424`, `03:7`, `03:556` ×2, `04:316` |
| "verified numerically" | 3 | `01:259`, `02:629`, `03:7` |
| "checked numerically" | 2 | `03:556`, `04:316` |
| "verified with code" | 1 | `06:31` |
| "in Lean" | 3 | `02:4`, `02:629`, `06:29` |
| "proved here" | 6 | `01:505`, `01:528`, `02:1098`, `03:391`, … |

| ✓ | Gate | Recommendation |
|---|------|----------------|
| [ ] | pick one verb per class and normalise | **`N` → "checked numerically"** (2 current, needs `01:259`, `02:629`, `03:7`, `06:31`); **`P` → "proved in Lean"**. Exact swaps: `verified numerically` → `checked numerically` (3 sites); `verified with code` → `checked numerically` (1 site, `06:31`). "proved here" stays (it means proved-in-this-paper, a different claim) |

### 7.2 Orphan fragments **not** repaired in §0 (they need wording, not moving)

| ✓ | Site | Problem | Proposed text |
|---|------|---------|---------------|
| [ ] | `02-methods.tex:629` | after the block move the statement still reads `…without factoring anything in $\OK$.  for the thirteen primes decided in Lean and the twenty-three verified numerically; the general congruence…` — lowercase "for" after a full stop, double space, no subject | `…without factoring anything in $\OK$. The thirteen primes decided in Lean and the twenty-three verified numerically are covered by the witnesses above; the general congruence for every $q\neq2,5$ is Lucas'~\cite{Lucas1878}` |
| [ ] | `04-implications.tex:536` | `…thermal at that temperature.\n(\S\ref{app:embedding}) \cite{GibbonsHawking77}. \ProofWitnessBlock{…}` — a citation clause with no sentence | `…thermal at that temperature (\S\ref{app:embedding}, \cite{GibbonsHawking77}).` then the block on its own line |
| [ ] | `04-implications.tex:657` | `\end{theorem}\begin{remark}[…]` — two environments on one line, no paragraph break (found during this pass, not in the original audit) | insert a blank line between them |

### 7.3 Census

| ✓ | Gate | Recommendation |
|---|------|----------------|
| [ ] | no test verifies the tag census (0 matches for `*.py`/`*.ts`; 05-kk has `tests/test_section_census.py`) | add `tests/test_witness_census.py` asserting (a) every `\NumericalWitness*` argument is either `...` or an id collected by pytest, (b) every `\ProofWitness*` name exists in `lean/CW6_complete_v2.lean`, (c) no witness key is repeated. This turns §1 from a one-off audit into a rule the suite keeps |

### 7.4 Tag vs. phrase contradictions

| ✓ | Site | Contradiction | Recommendation |
|---|------|---------------|----------------|
| [ ] | `04-implications.tex:1031` | the sentence presents the rate as a *derived* result — "(Corollary~\ref{cor:golden-growth})" — and the tag then says `N`, i.e. numerically checked, with no numeric content in the sentence | keep the tag **after** §1 #14 names `test_ratio_is_phi`, and add the number to the sentence: "the growth is golden, $\varphi$ per level (`test_ratio_is_phi`)" — or drop the tag with **(iv)** |
| [ ] | `03-derivations.tex:219-220` | a `P` block (Lean) and an `N` block tag the *same* paragraph, but the `N` names `thm:fib-min`, whose proof is the Lean one; nothing numeric about the theorem is checked | resolved by §1 #6 (retag to `eq:tower-modes`) |
| [ ] | `06-conclusions.tex:31-32` | "…not demonstrated but is verified with code… the verification tags $P/H/N$ of the abstract" advertises `H` although no claim carries it | follows §4: with `(R)` rewrite the list to `$\ProofWitness{...}$/$\NumericalWitness{...}$` |

---

## §8 — Cover

1. **Start at §0** — the mechanical pass is already applied and verified; read it only to know what moved.
2. **Then §1** — 19 rows, each one tick; rows 3, 6, 10 are the four "no test possible" ones, row 14 un-does an audit claim. Tick = use the recommendation as written; a different choice goes in *Notes* with your replacement text.
3. **§2 and §3 close themselves** once §1 is ticked (they point at §1 rows).
4. **§4 → §5 → §6** are three linked decisions about the class `H`, the dead macros, and the family grammar; tick §4 first.
5. **§7** is prose; every row ships a ready-made sentence.
6. Nothing here has been committed. After you tick, the edits are mechanical again and can be applied in one pass.

**Executive counts:** 50 open gates (51 checkboxes) — §1: 19 (16 × gate (i), 2 × (ii), 1 × (iii)) · §2: 12 · §3: 7 · §4: **closed 2026-11-16** · §5: 3 · §6: 1 decision with 2 mutually exclusive ticks · §7: 8.
