# The Crystalline Worldsheet: A String Theoretical Framework based on $\mathbb{F}_1$ for the de Sitter observer problem

<!-- selfcite:begin id="badge" -->
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21343602.svg)](https://doi.org/10.5281/zenodo.21343602)
<!-- selfcite:end id="badge" -->

[![Project Page](https://img.shields.io/badge/Project%20Page-omega--pcf.com-blue)](https://omega-pcf.com/crystalline-worldsheet)

## Authors

**Jorge Armando González García**¹, **Víctor Manuel González García**¹, **Itzel Marion Dressler Pérez**², **Luz María García Ordóñez**¹

¹ *TTAMAYO PUNTO COM, S.A.P.I. de C.V., Research & Development Division, Mexico*
² *Independent Researcher*

---

## Abstract

Holography and the Riemann hypothesis are missing the same kind of object. The pair correlation of the zeros of $\zeta$ follows GUE statistics; so does the boundary side of low-dimensional holography, where the bulk of JT gravity is recovered only as an average over an ensemble of theories. An ensemble is what one writes for want of an individual—the Hermitian operator of Hilbert–Pólya in one case, a single microstate in the other—and an average is a fact about the description, not about what exists. Based on this reading, and on other known connections between the primes and black holes, and between the odd zeta values and string and particle amplitudes, we propose that the obstruction in de Sitter is *epistemological*—a circumstance of mathematical circularity—rather than *ontological*—a matter of vacuum selection.

At this intersection the obstruction takes one form: how to describe the object without referring to the object, which the $\mathbb{F}_1$ program seeks to circumvent in arithmetic and the Hilbert–Pólya problem poses for the operator. We trace it to the non-paradoxical self-reference of binary language, in the precise sense of the Lawvere fixed-point theorem and the Yanofsky diagonal $g(t)=\alpha(f(t,t))$, as one of the most studied cases of self-referential circularity; and we analyse the strategies for confronting this circularity and their relation to the $\mathbb{F}_1$ program for proving the Riemann hypothesis—particularly Yuri Manin's proposed use of the same noncommutative tori that M-theory uses, but to approach that program.

From our own use of this torus we construct a string cocone, from which we later derive previously proposed criteria for holography in de Sitter, as well as the operator we propose as the microstate.

**Keywords:** Holography; de Sitter; M-theory; string theory; field with one element ($\mathbb{F}_1$); $\lambda$-rings; golden ratio; moduli spaces; formal verification.

<!-- selfcite:begin id="citation" -->
## Citation

González García, J. A., González García, V. M., García Ordóñez, L. M., & Dressler Pérez, I. M. (2026). *The Crystalline Worldsheet: A String Theoretical Framework based on 𝔽₁ for the de Sitter observer problem*. Preprint. DOI: [10.5281/zenodo.21343602](https://doi.org/10.5281/zenodo.21343602).

```bibtex
@article{CW6,
  author  = {González García, J. A. and González García, V. M. and García Ordóñez, L. M. and Dressler Pérez, I. M.},
  title   = {The Crystalline Worldsheet: A String Theoretical Framework based on 𝔽₁ for the de Sitter observer problem},
  journal = {Preprint},
  year    = {2026},
  doi     = {10.5281/zenodo.21343602},
  url     = {https://doi.org/10.5281/zenodo.21343602}
}
```
<!-- selfcite:end id="citation" -->

## Repository Structure

This repository contains the LaTeX source files for the manuscript and the computational verification suite.

### Manuscript (`src/`)

- **`main.tex`**: Master document (preamble + `\input{}` chain).
- **`src/chapters/`**:
  - `01-introduction-abstract.tex`: Abstract.
  - `01-introduction.tex`: §1 — the de Sitter observer problem, self-reference as its common cause, mathematical and physical antecedents, the framework, the physical program.
  - `02-methods.tex`: §2 — pentagonal identity, PCF construction, the base ring on the torus, the spectrum and the convergent diagram, formal verification status.
  - `03-derivations.tex`: §3 — the fundamental object, the meta-invariant, the tower and the amplitudes, AdS/CFT level by level, the M-theory web, the bridge and the demonstrative spine.
  - `04-implications.tex`: §4+§5 — the non-local field, the particle as observer, the tower of information and curved spacetime, dynamics and operators, Yang–Mills, the closure of the demonstrative line.
  - `05-discussion.tex`: §6 — problem, proposal, resolution, what it yields (vacuum selection, self-modelling observer, non-local reality before observation), closure as self-portrait.
  - `06-conclusions.tex`: §7 — final synthesis.
  - `appendix.tex`: Explicit derivations (AdS₅ curvature and an independent check, the ETS metric, SU(3)×SU(2)×U(1), the M-theory web, the superpoint ladder, Einstein's equations, Kaluza–Klein, arithmetic machinery).
  - `acknowledgments.tex`: Acknowledgements and generative AI disclosure.
  - `disclosure.tex`: Funding and conflict of interest.

### Verification Suite

- **`tests/`**: the numerical verification suite behind `pnpm run verify:py` (pytest) — <!-- counts:begin id="readme-suite" -->571<!-- counts:end id="readme-suite" --> tests collected, <!-- counts:begin id="readme-verify-py" -->543<!-- counts:end id="readme-verify-py" --> of them run by `verify:py` (the `slow`-marked tests deselected). It backs the manuscript's numerical witnesses: every `\tier[...]{N}` and `\witness{N}{...}` key must name a real `\label` that at least one test refers to, with no key repeated — the contract the witness census enforces (<!-- counts:begin id="readme-census" -->4<!-- counts:end id="readme-census" --> tests), so a retag or an unbacked claim fails the suite.
- **`lean/CW6_complete_v2.lean`**: single-file Lean 4 / Mathlib backing for the manuscript's proof witnesses — <!-- counts:begin id="readme-lean-theorems" -->591<!-- counts:end id="readme-lean-theorems" --> theorem/lemma declarations, <!-- counts:begin id="readme-lean-axioms" -->0<!-- counts:end id="readme-lean-axioms" --> axioms, <!-- counts:begin id="readme-lean-sorry" -->0<!-- counts:end id="readme-lean-sorry" --> `sorry` (comments stripped; built by `pnpm run verify:lean`). The manuscript itself carries <!-- counts:begin id="readme-lean-tags" -->0<!-- counts:end id="readme-lean-tags" --> `\Lean{…}` name tags, so it links to this file through its proof witnesses (`\witness{P}{...}`), which the Lean build resolves. Namespaces: `PaperS2`, `PaperM6`, `PaperS3a`, `PaperS3b`, `PCF.CW5`, `CWfig`, `PCFEntropyDOF`, `SpectralFlowPCF`, `GravitySectorPCF`, `CW5Additions`, `CW5FaceLinks`, `PCFColimit`, `FourCocone`, `ConductorAttribution`, `AnchorExterior`, `TwoTowersOneMicrostate`.
- **`lean/CW6_alignment_ledger.json`**: Alignment ledger (paper ↔ Lean ↔ numeric) in span-lea format.
- **`scripts/schemas/CW6_propgraph.dot`**: Proposition dependency graph (DOT format).
- **`scripts/figures/CW3_all_figures.py`**: Generates the six publication figures (`fig1_alphas_uniqueness.pdf`, `fig2_ER_bridge_identity.pdf`, `fig3_N_modes.pdf`, `fig4_top_down.pdf`, `fig5_three_panel.pdf`, `fig6_cylinder_torus.pdf`).

## Verification Execution

This project uses a rigorous dual-verification approach. Run from the project root:

```bash
pnpm run verify       # numerical + Lean + type-check
# counts:begin id="readme-verify-py-cmd"
pnpm run verify:py    # only numerical (543 tests; `slow` deselected)
# counts:end id="readme-verify-py-cmd"
pnpm run verify:lean  # only Lean (lake build CW6_complete_v2)
```

For comprehensive environment setup — Node.js/pnpm, Python/uv, Lean 4 — please refer to **[Installation & Requirements](docs/installation.md)**.

## Build and Compilation

```bash
pnpm build            # produces build/document-v<version>.pdf
pnpm build:full       # figures + build
```

> [!IMPORTANT]
> - **Metadata Flow:** `citation.csl.json` → `src/bibliography.bib` → `CITATION.cff` → `.zenodo.json` during build.
> - **Figures:** `pnpm run generate:figures` populates `images/` before `pdflatex` runs.
> - **Verification:** `build` produces the PDF; proof verification is `pnpm run validate`.

## License

See [LICENSE](LICENSE) for details (CC-BY-4.0).
