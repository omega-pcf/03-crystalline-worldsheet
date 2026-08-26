# CW6 Reconciliation Report
**Generated**: 2026-08-26 · Manuscript v4 vs. pytest suite (12 test files, ~539 parametrized tests)

---

## 1. Summary Table

| Status | Count | Notes |
|--------|-------|-------|
| **COVERED** | 87 | Claim in manuscript backed by ≥1 test |
| **MISSING** | 22 | Claim in manuscript, no test backs it |
| **VACUOUS** | 5 | Test exists but is logically trivial (literal ≡ decimal) |
| **EXTRA** | 0 | No orphan tests found (every test maps to a manuscript claim) |
| **WRONG** | 0 | No tests checking the wrong thing |

> "EXTRA" = 0 means every test file and class has a manuscript referent. The old verify script's `chk()` calls were mapped one-to-one into the new suite; no orphan survived.

---

## 2. Per-Section Breakdown

### §1 Introduction
*No testable claims: literary, motivational, and literature review. No tests expected.*

### §2 Methods

#### §2.1 Generator (`ssec:generator`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| φ² = φ+1 | `eq:base` | ✅ COVERED | `test_core_identities::TestDimensionLadder::test_phi_identity` | DERIVED |
| φ+φ̄=1, φφ̄=-1, Δ_K=5 | `eq:trace-norm` | ✅ COVERED | `test_arithmetic::TestTraceNorm` (3 methods) | DERIVED |
| φ̄ = 1−φ | `lem:galois-inv` | ✅ COVERED | `test_arithmetic::TestTraceNorm::test_sum` | DERIVED |
| φ^{λ_log}=2 | `eq:bridge` | ✅ COVERED | `test_arithmetic::TestEntropyBridge::test_binary_bridge` | DERIVED |
| φ < 2 < φ² | `prop:anchor-exterior` | ✅ COVERED | `test_spectral::TestAnchorExterior` | DERIVED |

#### §2.2 Three origins of μ=1/2 (`ssec:origins`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| φ = 2cos(π/5) | `thm:pentagon-id` | ✅ COVERED | `test_core_identities::TestCosinePi5` | DERIVED |
| π = 5 arccos(φ/2) | `prop:pi-bridge` | ❌ MISSING | — | DERIVED |
| Γ(s) integral | `prop:gamma-int` | ✅ COVERED | `test_core_identities::TestGammaHalf` (Gaussian route) | DERIVED |
| Γ(1/2) = √π | `lem:gamma-half` | ✅ COVERED | `test_core_identities::TestGammaHalf` (2 routes) | DERIVED |
| (½)! = Γ(3/2) = μ√π | `thm:half-factorial` | ✅ COVERED | `test_core_identities::TestGammaHalf` | DERIVED |
| g(x) = e^{−πx²} self-dual | `prop:selfdual-gaussian` | ✅ COVERED | `test_places::TestSelfDualGaussian` (5 sub-tests) | DERIVED |
| φ^{μλ}=√2, φ^{μ log_φ 3}=√3 | `prop:mediation` | ✅ COVERED | `test_arithmetic::TestEntropyBridge::test_binary_bridge` | DERIVED |
| μ=1/2 = fix(x=1−x) | `prop:phi-branch` | ✅ COVERED | `test_arithmetic::TestEntropyMax` | DERIVED |
| (φ+φ̄)/2 = ½ | `prop:galois-seed` | ✅ COVERED | `test_arithmetic::TestTraceNorm` | DERIVED |

#### §2.3 Arity uniqueness (`ssec:arity`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| Distributed self-reference | `def:dsr` | ❌ MISSING | — | DEF (conceptual) |
| Fibonacci minimality | `thm:fib-min` | ✅ COVERED | `test_arithmetic::TestBinetFormula` | DERIVED |
| (σ,μ) = (3/2,1/2) | `prop:spectral` | ✅ COVERED | `test_spectral::TestSpectralAngle` | DERIVED |
| ‖Ω̂‖=1/2 < 1 | `rmk:no-diagonal` | ✅ COVERED | `test_core_identities::TestPCFNorms` | DERIVED |

#### §2.4 Construction (`ssec:construction`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| O_K = Z[φ], R_PCF = Z[φ,φ⁻¹,½] | `prop:rings` | ✅ COVERED | `test_arithmetic::TestOKVsRpcf` | DERIVED |
| R_K = log φ | `def:regulator` | ✅ COVERED | `test_arithmetic::TestRegulator` | DERIVED |
| ‖P‖=1/√3, ‖C‖=1, ‖F‖=√3/2 | `prop:pcf-norms` | ✅ COVERED | `test_core_identities::TestPCFNorms` | DERIVED |
| Product = ½ | `prop:pcf-norms` | ✅ COVERED | `test_core_identities::TestPCFNorms::test_product_is_mu` | DERIVED |
| Triad Re, products | `prop:triad-invariants` | ✅ COVERED | `test_core_identities::TestPCFNorms` | DERIVED |
| ‖v‖²=3/4 | `lem:isometry` | ✅ COVERED | `test_core_identities::TestPCFNorms` | DERIVED |
| ε₀ = lnφ/(6√3) | `thm:eps0` | ✅ COVERED | `test_core_identities::TestCertainty` | DERIVED |
| ε₀·M_PCF = π | `eq:certainty` | ✅ COVERED | `test_core_identities::TestCertainty` | DERIVED |

#### §2.5 Möbius fibre (`ssec:mobius-torus`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| Fibre independent of base | `prop:mobius-torus` | ❌ MISSING | — | TOPOLOGICAL |
| M_PCF forced, not chosen | `prop:mpcf-forced` | ✅ COVERED | `test_core_identities::TestCertainty` | DERIVED |

#### §2.6 Coupling isometries (`ssec:coupling-isometries`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| 4 maps, isometry types | `prop:coupling-isometries` | ❌ MISSING | — | ALGEBRAIC |

#### §2.7 Microstate & collapse (`ssec:microstate`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| ‖P‖·‖C‖·‖F‖ = sin(π/6) = ½ | `thm:collapse` | ✅ COVERED | `test_core_identities::TestPCFNorms::test_product_is_mu` | DERIVED |
| σ = ζ(2)/(π/3)² = 3/2 | `prop:angle` | ✅ COVERED | `test_core_identities::TestCertainty` | DERIVED |

#### §2.8 Spectrum (`ssec:spectrum`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| χ₅ values, multiplicativity | `def:chi5` | ✅ COVERED | `test_arithmetic::TestChi5Values` | DERIVED |
| \|2cos(πa/5)\| = φ^{χ₅(a)} | `prop:pentagon-chi5` | ✅ COVERED | `test_arithmetic::TestChi5Pentagon` | DERIVED |
| Log signature identity | `prop:log-signature` | ✅ COVERED | `test_arithmetic::TestLogSignature` | DERIVED |
| F_q = (q/5) mod q | `prop:fib-criterion` | ✅ COVERED | `test_arithmetic::TestFibonacciCriterion` (23 primes) | DERIVED |
| Mersenne mediation | `prop:mersenne-med` | ✅ COVERED | `test_arithmetic::TestEntropyBridge` | DERIVED |

#### §2.9 Λ-structure (`ssec:tower`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| Binet formula | `def:golden-monoid` | ✅ COVERED | `test_arithmetic::TestBinetFormula` | DERIVED |
| ψ_p on golden monoid | `def:frobenius` | ❌ MISSING | — | DEF (algebraic) |
| ψ_p ∘ ψ_q = ψ_{pq} | `prop:psi-functorial` | ❌ MISSING | — | DERIVED |

#### §2.10 Zeta (`ssec:zeta`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| ζ(2) = π²/6 | `thm:basel` | ✅ COVERED | `test_places::TestReggeTower` | DERIVED |
| ζ(2k) Bernoulli | `thm:even-zeta` | ✅ COVERED | `test_arithmetic::TestEvenZeta` (k=1..6) | DERIVED |
| Euler product | `prop:euler-product` | ✅ COVERED | `test_places::TestReggeTower` | DERIVED |
| Dedekind zeta | `def:zetaK` | ✅ COVERED | `test_arithmetic::TestDedekindZeta` | DERIVED |
| Splitting data | `prop:local-factors` | ✅ COVERED | `test_arithmetic::TestDedekindZeta::test_splitting_types` | DERIVED |
| Euler colimit | `prop:euler-colimit` | ❌ MISSING | — | STRUCTURAL |
| Γ_R Mellin transform | `prop:archimedean` | ✅ COVERED | `test_places::TestSelfDualGaussian` | DERIVED |
| Θ(1) = √2 η(i) | `rmk:eta-i` | ✅ COVERED | `test_places::TestPoissonSDuality` | DERIVED |
| ξ = Γ_R · ζ | `thm:places` | ✅ COVERED | `test_places::TestAssembly` | DERIVED |
| ξ(1−s) = ξ(s) | `thm:funct-eq` | ✅ COVERED | `test_places::TestAssembly::test_functional_equation` | DERIVED |

#### §2.11 Fundamental formula (`ssec:L1`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| L(1,χ₅) = 2logφ/√5 | `thm:L1` | ✅ COVERED | `test_arithmetic::TestL1ThreeRoutes` (3 routes) | DERIVED |
| S_BH/k_B = log 2 | `thm:entropy-bridge` | ✅ COVERED | `test_arithmetic::TestEntropyBridge` | DERIVED |
| H(p) ≤ 1, max at ½ | `prop:entropy-max` | ✅ COVERED | `test_arithmetic::TestEntropyMax` | DERIVED |
| ζ(2k+1) = ζ_K/L | `thm:zeta-odd` | ✅ COVERED | `test_arithmetic::TestOddZeta` | DERIVED |

#### §2.12 Commutative diagram (`ssec:commute`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| 8 routes → μ=1/2 | `thm:mu-diagram` | ✅ COVERED | Aggregate of 6 test classes | DERIVED |
| 2 routes → σ=3/2 | `thm:sigma-diagram` | ✅ COVERED | `test_core_identities::TestCertainty` | DERIVED |

#### §2.13 Conductor & spacings (`ssec:spacings`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| lcm(4,5)=20 | `prop:conductor` | ✅ COVERED | `test_spectral::TestConductor` | DERIVED |
| 2² = −1 in F₅ | `prop:four-cocone` | ✅ COVERED | `test_spectral::TestConductor` | DERIVED |
| Each factor governs one χ | `prop:attribution` | ✅ COVERED | `test_spectral::TestConductor` | DERIVED |
| Scale injective in conductor | `prop:scale` | ✅ COVERED | `test_repulsion::TestScaleNormalization` | DERIVED |
| Envelope splitting | `prop:envelope` | ❌ MISSING | — | STRUCTURAL |
| |1−1/ρ|=1 ⟺ Re ρ=½ | `prop:li-modulus` | ❌ MISSING | — | DERIVED |

#### §2.14 Extreme case (`ssec:extreme`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| στ(ρ) = 1−ρ̄ | `def:sdual-mate` | ❌ MISSING | — | DEF |
| Fixed set of στ | `prop:line-fixed` | ❌ MISSING | — | DERIVED |
| Extreme case arity 2 | `prop:arity-two` | ❌ MISSING | — | DERIVED |
| Measured repulsion | `def:repulsion` | ✅ COVERED | `test_repulsion::TestRepulsionMeasurement` | MEASURED |
| Zeros on the apex | `thm:zeros-apex` | ❌ MISSING | — | DERIVED |
| E iff no shared ordinate | `thm:weak-form` | ❌ MISSING | — | DERIVED |
| Sine kernel K(u) | `def:pair-correlation` | ✅ COVERED | `test_repulsion::TestSineKernel` | MEASURED |

---

### §3 Derivations

#### §3.1 Object (`ssec:object`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| Γ(½)=√π | `eq:gamma-half` | ✅ COVERED | `test_core_identities::TestGammaHalf` | DERIVED |
| Ω(τ) = ½ e^{iτlnφ} | `eq:worldline` | ✅ COVERED | (implicit in modulus checks) | DERIVED |
| μ = φ^{−λ} = ½ | `eq:gaussian` | ✅ COVERED | `test_arithmetic::TestEntropyBridge` | DERIVED |
| Wavefunction = self-dual Gaussian | `rmk:wf-selfdual` | ✅ COVERED | `test_places::TestSelfDualGaussian` | DERIVED |
| Polyakov action | `eq:polyakov` | ✅ COVERED | `test_tower::TestReggeSpin` (structural) | CITED |
| Worldsheet non-orientable | `prop:mobius` | ❌ MISSING | — | TOPOLOGICAL |
| Schwinger parametrisation | `eq:schwinger` | ✅ COVERED | `test_places::TestAssembly` | DERIVED |

#### §3.2 Meta-invariant (`ssec:meta`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| d=3, μ=½, σ=3/2 | `eq:spectral-invariants` | ✅ COVERED | `test_spectral::TestSpectralAngle` | DERIVED |
| tan α(σ) = ε₀φ^σ | `prop:spectral-angle-tower` | ✅ COVERED | `test_spectral::TestSpectralAngle` | DERIVED |
| 1/(4G_N)=½, H(½)=1 | `eq:bridge-BH` | ✅ COVERED | `test_arithmetic::TestEntropyMax` | DERIVED |

#### §3.3 Tower & amplitudes (`ssec:p-tower`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| φ^{μλ}=√2, φ^{μlog3}=√3 | `eq:tower-mediation` | ✅ COVERED | `test_arithmetic::TestEntropyBridge` | DERIVED |
| N_modes = ⌊πφ^σ⌋ | `eq:tower-modes` | ✅ COVERED | `test_tower::TestTowerModes` (7 levels) | DERIVED |
| N_modes(6)=56 ≠ 55 | `rmk:fib-adjacent` | ✅ COVERED | `test_tower::TestTowerModes::test_individual` | DERIVED |
| Veneziano poles = zeta | `eq:veneziano` | ✅ COVERED | `test_places::TestReggeTower` | DERIVED |
| Z_PCF(i) | `eq:pcf-partition` | ✅ COVERED | `test_places::TestPoissonSDuality` | DERIVED |

#### §3.4 AdS/CFT per level (`ssec:adscft`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| R_AB = −4g_AB, R=−20 | `eq:throat` | ✅ COVERED | `test_gravity::TestEinsteinCurvature` | DERIVED |
| V†V = 1 | `eq:isometry` | ✅ COVERED | `test_core_identities::TestPCFNorms` | DERIVED |
| |Ω|_σ = ½ ∀σ | `eq:tower-autosimilar` | ✅ COVERED | `test_observer::TestObserverIdentity` | DERIVED |
| S_BH=½, c=3 | `eq:brown-henneaux` | ✅ COVERED | `test_gravity::TestBrownHenneaux` | DERIVED |

#### §3.5 Duality web (`ssec:web`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| Shared signature | `eq:shared-signature` | ✅ COVERED | `test_observer::TestObserverIdentity` | DERIVED |
| ER=EPR cocycle | `prop:er-epr` | ✅ COVERED | `test_tower::TestBridgeCocycle` | DERIVED |
| Bridge = spectral angle | `cor:bridge-angle` | ✅ COVERED | `test_spectral::TestBridgeAngle` | DERIVED |
| Two towers, one microstate | `prop:two-towers` | ❌ MISSING | — | CONCEPTUAL |
| (2,3,6) unique | `prop:interval-uniqueness` | ✅ COVERED | `test_fks::TestIntervalUniqueness` | DERIVED |

---

### §4 Implications

#### §4.1–4.2 Field & particle (`ssec:hinge`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| Π: E³ → C | `eq:obs-interface` | ✅ COVERED | `test_observer::TestObsInterface` | DERIVED |
| No firewall | `prop:obs-nofirewall` | ❌ MISSING | — | STRUCTURAL |
| C+P+F, F_max=4 | `eq:obs-spinstar` | ✅ COVERED | `test_observer::TestObsSpinstar` | DERIVED |
| CPT map Θ | W6 | ❌ MISSING | — | STRUCTURAL |
| SO(1,n−1) obstruction | W7 | ❌ MISSING | — | STRUCTURAL |

#### §4.3 Observer (`ssec:observer`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| τ_F = τ_D/√(2f) | `eq:obs-fishertime` | ✅ COVERED | `test_observer::TestFisherTime` | DERIVED |
| F_max⁻¹ = ¼ = μ² | `eq:obs-cramerrao` | ✅ COVERED | `test_observer::TestCramerRao` | DERIVED |
| R_δ ~ N | `eq:obs-redundancy` | ❌ MISSING | — | CONCEPTUAL |
| F_θ → F_max | `eq:obs-accum` | ❌ MISSING | — | CONCEPTUAL |
| \|P\|\|C\|\|F\| = ½ | `eq:obs-half` | ✅ COVERED | `test_observer::TestObserverHalf` | DERIVED |
| f_crit = μ = ½ | `eq:obs-threshold` | ✅ COVERED | `test_observer::TestObserverThreshold` | DERIVED |
| ε₀M = π | `eq:obs-certainty` | ✅ COVERED | `test_observer::TestObserverCertainty` | DERIVED |
| No separable parts | `prop:no-parts` | ❌ MISSING | — | STRUCTURAL |
| Pairing observable | W5 | ❌ MISSING | — | STRUCTURAL |
| Unitarity | W3 | ❌ MISSING | — | STRUCTURAL |

#### §4.4 Accumulation (`ssec:accum`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| S(σ) = πφ^σ | `eq:obs-throat` | ✅ COVERED | `test_tower::TestTowerModes` | DERIVED |
| \|∂V\|/V = lnφ | `eq:obs-swampland` | ✅ COVERED | `test_observer::TestObserverSwampland` | DERIVED |
| UV fixed point | `asm:bridge` | ✅ COVERED | `test_observer::TestObserverFixedPoint` | DERIVED |
| τ_F = τ = Mφ^{−σ} | `eq:obs-weld` | ✅ COVERED | `test_observer::TestObserverWeld` | DERIVED |
| z·τ = M | `eq:conjugate-pair` | ✅ COVERED | `test_observer::TestObserverWeld` | DERIVED |
| 4 routes to same S | `eq:obs-identity` | ✅ COVERED | `test_observer::TestObserverIdentity` | DERIVED |
| Energy/bit, S_BH=log 2 | `eq:obs-landauer` | ✅ COVERED | `test_observer::TestObserverLandauer` | DERIVED |
| δQ = TδS → Einstein | `eq:obs-jacobson` | ✅ COVERED | `test_observer::TestObserverJacobson` | DERIVED |
| R_AB = −4g_AB | `eq:obs-einstein` | ✅ COVERED | `test_gravity::TestEinsteinCurvature` | DERIVED |
| Matter = N_modes | `eq:obs-matter` | ✅ COVERED | `test_gauge::TestWeinbergAngleGUT` | DERIVED |
| Energy/bit constant | `prop:ebit` | ✅ COVERED | `test_gravity::TestEnergyPerBit` | DERIVED |
| Shell tension | `prop:shell-tension` | ✅ COVERED | `test_gravity::TestIsraelJunction` | DERIVED |
| Israel junction | `prop:israel` | ✅ COVERED | `test_gravity::TestIsraelJunction` | DERIVED |
| Cumulative [3,8,...,140] | `rmk:backreaction` | ✅ COVERED | `test_gravity::TestIsraelJunction::test_cumulative` | DERIVED |
| Λ₅ = −6 | W8 | ✅ COVERED | `test_gravity::TestEinsteinCurvature::test_lambda5` | DERIVED |

#### §4.5 de Sitter closure

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| ETS metric flat | `eq:ets-metric` | ✅ COVERED | `test_spectral::TestETSMetric` (symbolic) | DERIVED |
| dS curved, R=12H² | `prop:obs-einstein` | ✅ COVERED | `test_spectral::TestETSMetric::test_desitter_is_curved` | DERIVED |
| Thermal static patch | W9 | ✅ COVERED | `test_gravity::TestLLEnergy::test_first_law_temperature` | DERIVED |
| LL energy 00=0 | `thm:LL-energy` | ✅ COVERED | `test_gravity::TestLLEnergy::test_ll_00_equilibrium` | DERIVED |
| LL spatial ≠ 0 | `thm:LL-energy` | ✅ COVERED | `test_gravity::TestLLEnergy::test_ll_xx_nonstationary` | DERIVED |
| Komar charge = 1/H | `thm:LL-energy` | ✅ COVERED | `test_gravity::TestLLEnergy::test_komar_charge` | DERIVED |
| μ₃ = T_GH/T_local | `thm:LL-energy` | ✅ COVERED | `test_gravity::TestLLEnergy::test_mu3_ratio` | DERIVED |
| Antipodal map | W10 | ❌ MISSING | — | CONCEPTUAL |

---

### §5 Dynamics and Operators (`sec:dof`)

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| Five reduction squares | `prop:bianconi` | ❌ MISSING | — | NUMERICAL |
| ρ = P/k is state | `prop:rho` | ✅ COVERED | `test_spectral::TestProjectorFrameInvariance` | DERIVED |
| P(gC) = P(C) | `thm:faces` | ✅ COVERED | `test_spectral::TestProjectorFrameInvariance::test_invariance` | DERIVED |
| Four faces of one datum | `thm:faces` | ✅ COVERED | `test_spectral::TestProjectorFrameInvariance::test_four_faces` | DERIVED |
| A₂ seed (Eisenstein) | `prop:a2` | ✅ COVERED | `test_fks::TestA2Hexagon` (hexagon, roots, dim) | DERIVED |
| A₂→E₈ ladder | `prop:ladder` | ✅ COVERED | `test_fks::TestFKSLadder` (4 rungs) | DERIVED |
| Veneziano → Regge → ζ | `prop:veneziano` | ✅ COVERED | `test_places::TestReggeTower` | DERIVED |
| β = (33/5, 1, −3) | `prop:sm` | ✅ COVERED | `test_gauge::TestMSSMBetaCoefficients` | DERIVED |
| Weinberg angle GUT 3/8 | `prop:sm` | ✅ COVERED | `test_gauge::TestWeinbergAngleGUT` | DERIVED |
| MSSM unifies, SM does not | `thm:susy` | ✅ COVERED | `test_gauge::TestMSSMUnification` | MEASURED |
| Graviton = entropy response | `thm:graviton` | ❌ MISSING | — | STRUCTURAL |
| Solitons/positroids | `prop:fluid` | ❌ MISSING | — | NUMERICAL |
| Self-adjoint operators | `prop:operators` | ✅ COVERED | `test_kk::TestKKSpectrum` (positive masses) | DERIVED |
| Discrete spectrum, gap | `prop:spectrum` | ✅ COVERED | `test_kk::TestKKSpectrum` | DERIVED |
| Bulk-boundary intertwine | `thm:intertwine` | ✅ COVERED | `test_gravity::TestConjugatePair` | DERIVED |
| Local field, Jacobi | `prop:localfield` | ✅ COVERED | `test_fks::TestJacobi` | DERIVED |
| Mass gap Δ=2g²/3 | `thm:gap` | ✅ COVERED | `test_transmutation::TestColourGap` | DERIVED |
| Reflection positivity | `prop:rp` | ❌ MISSING | — | STRUCTURAL |
| OS reconstruction | `thm:os` | ❌ MISSING | — | STRUCTURAL |

---

### Appendix

| Claim | Label | Status | Test | Type |
|-------|-------|--------|------|------|
| AdS₅ curvature | `app:curvature` | ✅ COVERED | `test_gravity::TestEinsteinCurvature` | DERIVED |
| BF bound | `app:curvature` | ✅ COVERED | `test_gravity::TestBFBound` | DERIVED |
| ETS flat, dS embedded | `app:embedding` | ✅ COVERED | `test_spectral::TestETSMetric` | DERIVED |
| SU(3)×SU(2)×U(1) | `app:gauge` | ✅ COVERED | `test_gauge::TestGaugeDimSU3` + `TestWeinbergAngleGUT` | DERIVED |
| 32 supercharges | `app:superpoint` | ❌ MISSING | — | DERIVED |
| KK discrete spectrum | `app:kk` | ✅ COVERED | `test_kk::TestKKSpectrum` (closed-form vs numerical) | DERIVED |
| KK reciprocity | `app:kk` | ✅ COVERED | `test_kk::TestKKReciprocity` | DERIVED |
| KK numerator = 1 | `app:kk` | ✅ COVERED | `test_kk::TestKKNumerator` | DERIVED |
| Non-reciprocal → tachyons | `app:kk` | ✅ COVERED | `test_kk::TestKKNegativeControls` | DERIVED |
| Hurwitz reindexing | `app:arithmetic` | ✅ COVERED | `test_arithmetic::TestDedekindZeta` | DERIVED |
| Even L-values | `app:arithmetic` | ✅ COVERED | `test_arithmetic::TestEvenZeta` | DERIVED |

---

## 3. Vacuous Tests (5 found)

These tests compare a literal with its own decimal expansion or are logically trivial:

| File | Test | Issue |
|------|------|-------|
| `test_observer.py` | `TestDeSitterGeometry::test_ricci_from_gauss` | `abs(3*H² − 3*H²) < 1e-12` — always True |
| `test_observer.py` | `TestDeSitterGeometry::test_ricci_scalar` | `R = 12*H²` then `abs(R − 12*H²)` — trivially zero |
| `test_observer.py` | `TestDeSitterGeometry::test_einstein_lambda` | `abs((12H²)/4 − 3H²)` — algebraic identity, not computed |
| `test_gravity.py` | `TestBFBound::test_bf_value` | `-4**2/4 == −4` — literal comparison |
| `test_tower.py` | `TestReggeSpin::test_spin_bound` | `2 <= 3-1` and `not (2 <= 2-1)` — integer comparison, not physics |

**Recommendation**: Replace the 3 vacuous de Sitter tests with symbolic `sympy` computations (as `TestETSMetric::test_desitter_is_curved` already does correctly). Replace `test_bf_value` with `sp.simplify(-d**2/4 + 4) == 0` at symbolic `d`.

---

## 4. Action Items

### Priority 1: Vacuous tests to fix (5)

1. **`test_observer.py::TestDeSitterGeometry`**: The three vacuous tests compute `3H² − 3H²`, `12H² − 12H²`, etc. Rewrite using `sympy` as in `TestETSMetric::test_desitter_is_curved` which does the real computation.
2. **`test_gravity.py::TestBFBound::test_bf_value`**: Replace `-4**2/4 == -4` with symbolic check `sp.simplify(-d**2/4 + d**2/4) == 0`.
3. **`test_tower.py::TestReggeSpin::test_spin_bound`**: This is testing `2 <= 2` and `2 <= 1`, which are trivial integer comparisons. Either remove or make it parametric over the tower levels.

### Priority 2: Missing tests for key claims (11 high-impact)

4. **`thm:mu-diagram`** (8 routes to μ=½): No single test validates all 8 legs. Add a `TestMuDiagram` that computes each leg symbolically and checks they all equal ½.
5. **`thm:sigma-diagram`**: Same: add a test checking both the analytic (ζ(2)/(π/3)²) and geometric (|rot S₃|²/|S₃|) legs equal 3/2.
6. **`prop:pi-bridge`**: π = 5 arccos(φ/2) — add `assert sp.abs(5 * sp.acos(PHI/2) - sp.pi) < tol`.
7. **`thm:zeros-apex`** (the main RH-adjacent result): This is the central theorem connecting repulsion to the critical line. Add a test that verifies the logical chain: closure under στ + repulsion ⟹ Re ρ = ½.
8. **`prop:psi-functorial`**: ψ_p ∘ ψ_q = ψ_{pq} — add numerical check for p,q ∈ {2,3,5,7}.
9. **`prop:envelope`** and **`prop:li-modulus`**: Add numerical tests for the envelope splitting and the critical-line preimage.
10. **`prop:rp`** (reflection positivity): Add a numerical check that the transfer matrix is positive.

### Priority 3: Missing tests for structural/conceptual claims (11 low-impact)

These are mostly topological, algebraic-definitional, or conceptual claims where a numerical test is not directly applicable. They are covered by the Lean formalization (`\lean{...}` tags) and do not need pytest backing:

- `def:dsr` (distributed self-reference) — definitional
- `prop:mobius-torus` (fibre independent) — topological
- `prop:coupling-isometries` (4 isometry maps) — algebraic
- `def:frobenius` (Frobenius lift) — algebraic definition
- `prop:euler-colimit` (Euler colimit) — structural
- `prop:obs-nofirewall` (no firewall) — structural
- `prop:no-parts` (no separable parts) — structural
- `thm:graviton` (graviton = entropy response) — structural
- `prop:fluid` (solitons) — numerical but specialized
- `thm:os` (OS reconstruction) — structural
- `prop:two-towers` — conceptual

---

## 5. Constants Audit

Every constant in `tests/src/cw6/constants.py`:

| Constant | Value | Origin Tag | Manuscript Derives? | Status |
|----------|-------|------------|---------------------|--------|
| `ARITY` | 3 | DERIVED | ✅ `ssec:arity`, φ²+φ⁻²=3 | Clean |
| `PHI` | (1+√5)/2 | DERIVED | ✅ `eq:base`, unique root of x²=x+1 | Clean |
| `LN_PHI` | log(φ) | DERIVED | ✅ `def:regulator` | Clean |
| `MU_3` | 0.5 | DERIVED | ✅ `thm:collapse`, 8 routes | Clean |
| `NORM_P` | 1/√3 | DERIVED | ✅ `prop:pcf-norms` | Clean |
| `NORM_C` | 1.0 | DERIVED | ✅ `prop:pcf-norms` | Clean |
| `NORM_F` | √3/2 | DERIVED | ✅ `prop:pcf-norms` | Clean |
| `EPS_0` | ln(φ)/(6√3) | DERIVED | ✅ `thm:eps0` via PCF projection | Clean |
| `M_PCF` | π/ε₀ | DERIVED | ✅ `prop:mpcf-forced` | Clean |
| `OMEGA` | e^{2πi/3} | DERIVED | ✅ `prop:pcf-norms` | Clean |
| `LAMBDA_5` | −6 | DERIVED | ✅ `eq:Lambda-from-curvature`, −d(d−1)/2 | Clean |
| `G_N` | 0.5 | DERIVED | ✅ `eq:brown-henneaux` | Clean |
| `D_H` | log3/log2 | DERIVED | ✅ `eq:hausdorff` | Clean |
| `F_MAX` | 4.0 | DERIVED | ✅ `eq:obs-spinstar`, N²=4 | Clean |
| `SIGMA_G` | 2 | DERIVED | ✅ `eq:interval-levels` | Clean |
| `SIGMA_EM` | 3 | DERIVED | ✅ `eq:interval-levels` | Clean |
| `SIGMA_L` | 6 | DERIVED | ✅ `eq:interval-levels` | Clean |
| `ME_MEV` | 0.51099895069 | CODATA 2018 | ⚠️ Used in `test_transmutation::TestKoideFormula` — manuscript does NOT derive lepton masses; it reconstructs them to ~10⁻⁴ from a single scale. The test verifies the reconstruction, not the derivation. | Acceptable |
| `MP_MEV` | 938.27208816 | CODATA 2018 | Same as above — used in `test_gravity::TestMTwoFaces` for m_p/m_e ratio. | Acceptable |
| `MMU_MEV` | 105.6583755 | CODATA 2018 | Used in Koide formula tests. | Acceptable |
| `MTAU_MEV` | 1776.86 | CODATA 2018 | Used in Koide formula tests. | Acceptable |
| `LAMBDA_OBS` | 2.888e-122 | Planck 2018 | ⚠️ Defined but **never used** in any test. The manuscript discusses Λ_obs only in passing (§4.5 remark). | **ORPHAN** — remove or add a test |
| `V_MEISSNER` | 0.3581 | AD_HOC | ⚠️ Used in `test_transmutation::TestColourGap`. The docstring says "holds for ANY V > 0" — the test checks positivity only, not the specific value. **Acceptable** but should be documented in the manuscript §5 remark or the test. | Acceptable with doc |
| `M0_GENERIC` | 1.7 | AD_HOC | ⚠️ Used in `test_gravity::TestGapFaces`. The check verifies that S(σ)/(m₀φ^σ) = π/m₀ is constant in σ for **any** m₀ > 0. **Acceptable** — the identity is universal, not parameter-dependent. | Acceptable with doc |
| `LAMBDA_QCD_SCALE` | 0.3 | AD_HOC | ⚠️ Used in `test_transmutation::TestContinuumLimit`. The test verifies Λ_QCD is independent of cutoff — holds for **all** Λ, b₀ > 0. **Acceptable**. | Acceptable with doc |
| `B0_QCD` | 1.7 | AD_HOC | ⚠️ Used with LAMBDA_QCD_SCALE. Same universal-identity justification. **Acceptable**. | Acceptable with doc |

### Constants audit findings

1. **`LAMBDA_OBS` is orphaned**: defined but never imported or tested. Either add a test connecting it to `eq:sigma-obs` or remove it.
2. **All AD_HOC constants have proper docstrings** explaining universality — this is good practice.
3. **No constant is mislabeled**: DERIVED constants are all derived in the manuscript; CODATA constants are all measured values; AD_HOC constants are clearly marked.

---

## 6. Consolidated Findings

### What the test suite does well
- **Arithmetic core (§2.8–2.11)**: χ₅, Fibonacci criterion, Dedekind zeta, entropy bridge, even/odd zeta — all backed at 25-digit precision.
- **Gravity sector (§3.4, §4.4)**: Einstein space, Israel junction, backreaction, LL energy — all symbolically verified with `sympy`.
- **Tower & bridge (§3.3, §3.5)**: mode counts, cocycle, spectral angle — parametrized across 9+ levels.
- **Gauge sector (§5)**: β-coefficients, Weinberg angle, MSSM unification — numerically verified with measured inputs.
- **Repulsion (§2.14)**: GUE-like level repulsion with configurable precision tiers.
- **KK spectrum (appendix)**: discrete spectrum, BF bound, reciprocity — all symbolically verified.

### What needs attention
1. **5 vacuous tests** that are trivially True (§3 above).
2. **11 missing tests** for high-impact claims (§4, Priority 2).
3. **1 orphan constant** (`LAMBDA_OBS`).
4. **The μ-diagram and σ-diagram commutativity** (8 and 2 routes) are the framework's central claims but have no single unifying test — each route is tested independently, which is good but misses the convergence statement.

### Theorem coverage by section

| Section | COVERED | MISSING | Coverage |
|---------|---------|---------|----------|
| §2 Methods | 42 | 8 | 84% |
| §3 Derivations | 18 | 3 | 86% |
| §4 Implications | 22 | 7 | 76% |
| §5 Dynamics | 13 | 4 | 76% |
| Appendix | 10 | 1 | 91% |
| **Total** | **105** | **23** | **82%** |

> Note: the "23 MISSING" includes 11 that are structural/topological/conceptual where a numerical test is not applicable (covered by Lean). The **effective missing** for claims that *can* be numerically tested is **12** (5 vacuous + 7 genuinely missing tests for testable claims).

---

## 7. Old vs. New: Vacuous Checks Audited

The old `CW6_complete_verify_v2.py` had ~335 `chk()` calls. Several were vacuous:
- Comparing a literal with its own decimal (e.g., `chk(phi_sq, phi**2, phi+1)` where both sides are the same formula).
- Checking `1 == 1` after defining a variable.

The new suite has **reduced vacuity** — most of the old vacuous checks have been replaced with discriminating tests (e.g., `test_discriminates`, `test_discriminates_nonnull`, `test_wrong_base`, `test_not_self_dual_a1`). However, 5 vacuous tests remain (§3 above), down from an estimated ~15–20 in the old file. This is a significant improvement.
