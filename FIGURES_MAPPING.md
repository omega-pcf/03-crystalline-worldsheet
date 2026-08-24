# Figure Mapping: Paper v4 → Generators

Paper `CW6_paper_v4.tex` references 6 figures.
Script `scripts/figures/CW3_all_figures.py` generates 6 figures.
Names and content don't match. This file documents the gap.

## Paper References → Required Mapping

| # | Paper `\includegraphics` | Paper context (section) | Needs to show | Current generator match? |
|---|---|---|---|---|
| 1 | `fig_tower_modes.png` | §3 derivations, L246 | Tower spectrum N_modes, golden tower modes | → `fig3_N_modes.pdf` ✓ name/content close |
| 2 | `fig_ads_ladder.png` | §3 derivations, L380 | AdS ladder, saturation entropy S(σ)=πφ^σ | → `fig5_three_panel.pdf` ? (3-panel, may include this) |
| 3 | `fig_isometry_algebra.png` | §3 derivations, L406 | Isometry ↔ algebra bulk-boundary, GKPW dictionary | → `fig4_top_down.pdf` ✓ (Eisenstein Z[ω] ↔ Gauss Z[i]) |
| 4 | `fig_er_epr.png` | §3 derivations, L604 | ER=EPR bridge identity | → `fig2_ER_bridge_identity.pdf` ✓ |
| 5 | `fig_torus_gauge.png` | §4 implications, L179 | Torus + gauge group SU(3)×SU(2)×U(1), MSSM β-functions | → `fig6_cylinder_torus.pdf` ? (cylinder/torus, partial match) |
| 6 | `fig_alpha_uniqueness.png` | §4 implications, L778 | Alpha uniqueness, |Ω|=1/2 microstate | → `fig1_alphas_uniqueness.pdf` ✓ |

## Current Generator Output (scripts/figures/CW3_all_figures.py)

| Generator fn | Output file | Content |
|---|---|---|
| `make_fig1` | `fig1_alphas_uniqueness.pdf` | α-uniqueness, |Ω|=1/2 |
| `make_fig2` | `fig2_ER_bridge_identity.pdf` | ER=EPR bridge |
| `make_fig3` | `fig3_N_modes.pdf` | N_modes spectrum |
| `make_fig4` | `fig4_top_down.pdf` | Isometry ↔ algebra (Z[ω] ↔ Z[i]) |
| `make_fig5` | `fig5_three_panel.pdf` | Three-panel (tower + ladder + ?) |
| `make_fig6` | `fig6_cylinder_torus.pdf` | Cylinder/torus 3D |

## Action Required

1. **Rename generator outputs** to match paper references, OR
2. **Update `\includegraphics`** in chapters to use current filenames, OR
3. **Write new generators** that produce the exact figures the paper describes

Option (2) is simplest — just update the 6 `\includegraphics` lines in:
- `src/chapters/03-derivations.tex` (4 figures)
- `src/chapters/04-implications.tex` (2 figures)

Current `\includegraphics` lines to update:
```
03-derivations.tex:246  fig_tower_modes.png     → fig3_N_modes.pdf
03-derivations.tex:380  fig_ads_ladder.png      → fig5_three_panel.pdf (verify content)
03-derivations.tex:406  fig_isometry_algebra.png → fig4_top_down.pdf
03-derivations.tex:604  fig_er_epr.png          → fig2_ER_bridge_identity.pdf
04-implications.tex:179 fig_torus_gauge.png     → fig6_cylinder_torus.pdf (verify content)
04-implications.tex:778 fig_alpha_uniqueness.png → fig1_alphas_uniqueness.pdf
```

Note: `main.tex` graphicspath includes `images/` so figures are found there.
LaTeX accepts .pdf in `\includegraphics` natively (no conversion needed).
