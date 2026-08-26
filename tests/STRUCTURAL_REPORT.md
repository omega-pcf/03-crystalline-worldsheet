# Structural / Topological Claims — Upstream Report
**Date**: 2026-08-26 · For the lead author

These 12 claims from CW6_paper_v4.tex are **not numerically testable** — they are structural, topological, or algebraic-definitional. They are either covered by the Lean formalization or require manual verification against the manuscript.

**No pytest action needed.** This report exists so the lead author can decide whether any require tex clarification or additional formal proof.

---

## Claims Requiring Attention

| # | Label | Section | Content | Status |
|---|-------|---------|---------|--------|
| 1 | `def:dsr` | §2.3 | Distributed self-reference (definition) | Definitional — no test needed |
| 2 | `prop:mobius-torus` | §2.5 | Fibre of the Möbius torus is independent of base | Topological — covered by Lean or manual proof |
| 3 | `prop:coupling-isometries` | §2.6 | 4 isometry maps on the coupling space | Algebraic — verify the 4 maps are listed correctly in tex |
| 4 | `def:frobenius` | §2.11 | Frobenius lift on the golden monoid | Definition — ensure the axioms are stated precisely |
| 5 | `prop:euler-colimit` | §2.8 | Euler product colimit exists | Structural — the numerical partial products converge (tested in test_places.py) but the *colimit statement* is topological |
| 6 | `prop:obs-nofirewall` | §4 | No firewall in the observer construction | Structural — depends on RP (now tested) + OS reconstruction (not testable) |
| 7 | `prop:no-parts` | §4 | No separable parts in the microstate | Structural — follows from irreducibility |
| 8 | `thm:graviton` | §4 | Graviton = entropy response of the bridge | The TT wave equation is tested numerically; the *physical interpretation* is structural |
| 9 | `prop:fluid` | §5 | Solitons from the condensate | Numerical but specialized — the hydrodynamic limit would need a separate simulation |
| 10 | `thm:os` | §5 | Osterwalder–Schrader reconstruction | Structural — the RP condition is now tested; the *reconstruction theorem* itself is a mathematical result |
| 11 | `prop:two-towers` | §4 | Two towers (Virasoro + superpoint) meet at one vertex | Conceptual — the *structural* claim that both paths lead to c=3 is tested numerically |
| 12 | `thm:zeros-apex` | §2.12 | Closure under στ + repulsion ⟹ Re ρ = ½ | The central RH-adjacent result. RP is tested; the *logical chain* closure → apex is a theorem, not a computation |

---

## Recommendations

1. **Items 1, 4, 7**: Definitions — ensure the tex states them precisely enough for formalization.
2. **Items 2, 3, 5, 6, 10**: Structural theorems — verify the Lean proofs cover these (check `\\lean{...}` tags).
3. **Items 8, 9, 11**: Physical interpretations — these connect the math to physics; the lead author should confirm the narrative is clear.
4. **Item 12**: The most important. The numerical tests verify RP and the apex property separately. The *implication* (RP + στ-closure → Re ρ = ½) is the theorem. Ensure the tex proof is complete.

---

## What IS tested numerically (for reference)

The following *components* of these structural claims ARE backed by pytest:
- RP positivity (`test_places.py::TestReflectionPositivity`)
- The transfer matrix (`test_places.py::TestReflectionPositivity::test_first_equality`)
- The KK spectrum (`test_kk.py`)
- The bridge cocycle (`test_tower.py::TestBridgeCocycle`)
- The tower modes (`test_tower.py::TestTowerModes`)
- The conjugate pair (`test_gravity.py::TestConjugatePair`)
- The ETS flatness (`test_spectral.py::TestETSMetric`)
- The modular LL identification (`test_gravity.py::TestModularLL`)

The gap is the *logical connective* between these tested components — which is where the theorem lives.
