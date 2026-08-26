"""
CW3_gue_figures.py — GUE/level-repulsion figures for The Crystalline Worldsheet.

Fig 7: Histogram of unfolded spacings (GUE vs Poisson)
Fig 8: The GUE pair-correlation kernel K(u) = 1 - (sin πu / πu)²

All zeros computed via mpmath.zetazero — no external tables, no fallback.
Titles live in LaTeX captions, not in the figure PDFs.
"""
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

# ── Shared style ───────────────────────────────────────────────────────
RC = {
    'font.family': 'serif',
    'font.serif': ['DejaVu Serif'],
    'mathtext.fontset': 'stix',
    'font.size': 12,
    'axes.labelsize': 13,
    'axes.linewidth': 0.8,
    'lines.linewidth': 1.2,
}
plt.rcParams.update(RC)

# ── Colours ────────────────────────────────────────────────────────────
C_GUE     = '#1a4a8a'
C_POISSON = '#cc4400'
C_EMP     = '#444444'
C_MIN     = '#cc0000'
C_KERNEL  = '#004488'
C_FILL    = '#d0e0f0'

# ── Maths ──────────────────────────────────────────────────────────────
def wigner_gue(u):
    return (32.0 / np.pi**2) * u**2 * np.exp(-4.0 * u**2 / np.pi)

def poisson_dist(u):
    return np.exp(-u)

def sine_kernel(u):
    u = np.asarray(u, dtype=float)
    with np.errstate(divide='ignore', invalid='ignore'):
        ratio = np.where(np.abs(u) < 1e-15, 1.0, np.sin(np.pi * u) / (np.pi * u))
    return 1.0 - ratio**2


def _compute_spacings():
    """Compute 237 unfolded spacings from mpmath (γ₁ to γ₂₃₈)."""
    from mpmath import mp, zetazero, log as mlog, pi as mpi
    mp.dps = 20
    gammas = [float(mp.im(zetazero(n))) for n in range(1, 239)]
    g = np.array(gammas)
    raw = np.diff(g)
    density = np.log(g[:-1] / (2 * np.pi)) / (2 * np.pi)
    return raw * density, g


# ════════════════════════════════════════════════════════════════════════
#  FIGURE 7 — Histogram of unfolded spacings
# ════════════════════════════════════════════════════════════════════════

def make_fig7():
    spacings, gammas = _compute_spacings()
    n = len(spacings)
    dmin = spacings.min()

    fig = plt.figure(figsize=(16, 7), facecolor='white')
    from matplotlib.gridspec import GridSpec
    gs = GridSpec(1, 2, width_ratios=[2, 1], wspace=0.30)
    ax_full = fig.add_subplot(gs[0])
    ax_zoom = fig.add_subplot(gs[1])

    # ── (a) Full histogram ─────────────────────────────────────────────
    bins = np.linspace(0, 3.0, 35)
    ax_full.hist(spacings, bins=bins, density=True,
                 color=C_EMP, alpha=0.55, edgecolor='white', lw=0.5, zorder=3)

    u = np.linspace(0.001, 3.0, 500)
    ax_full.plot(u, wigner_gue(u), color=C_GUE, lw=2.2, zorder=5,
                 label=r'GUE (Wigner surmise)')
    ax_full.plot(u, poisson_dist(u), color=C_POISSON, lw=2.0, ls='--',
                 label=r'Poisson')
    ax_full.axvline(dmin, color=C_MIN, lw=1.5, ls=':', zorder=6)
    ax_full.plot([], [], color=C_MIN, lw=1.5, ls=':',
                 label=rf'$\delta_{{\min}}={dmin:.4f}$')

    ax_full.set_xlabel(r'Unfolded spacing $u$')
    ax_full.set_ylabel('Density')
    ax_full.legend(loc='upper right', fontsize=10.5, framealpha=0.9)
    ax_full.set_xlim(-0.05, 3.0)
    ax_full.set_ylim(0, 1.15)
    ax_full.text(0.02, 0.97, '(a)', transform=ax_full.transAxes,
                 fontsize=14, fontweight='bold', va='top')

    # ── (b) Zoom on repulsion ──────────────────────────────────────────
    bins_z = np.linspace(0, 0.8, 30)
    ax_zoom.hist(spacings, bins=bins_z, density=True,
                 color=C_EMP, alpha=0.55, edgecolor='white', lw=0.5, zorder=3)
    uz = np.linspace(0.001, 0.8, 300)
    ax_zoom.plot(uz, wigner_gue(uz), color=C_GUE, lw=2.2, zorder=5)
    ax_zoom.plot(uz, poisson_dist(uz), color=C_POISSON, lw=2.0, ls='--', zorder=5)
    ax_zoom.axvline(dmin, color=C_MIN, lw=1.5, ls=':', zorder=6)
    ax_zoom.fill_between(uz, 0, wigner_gue(uz), where=(uz < dmin),
                         color=C_GUE, alpha=0.08, zorder=2,
                         label=rf'$u < \delta_{{\min}}$')

    ax_zoom.set_xlabel(r'Unfolded spacing $u$')
    ax_zoom.set_ylabel('Density')
    ax_zoom.legend(loc='upper right', fontsize=9.5, framealpha=0.9)
    ax_zoom.set_xlim(-0.02, 0.8)
    ax_zoom.set_ylim(0, 1.6)
    ax_zoom.text(0.02, 0.97, '(b)', transform=ax_zoom.transAxes,
                 fontsize=14, fontweight='bold', va='top')

    plt.savefig('fig7_spacing_histogram.pdf', dpi=150, bbox_inches='tight',
                facecolor='white')
    plt.close()
    print(f"  Fig7 saved ({n} spacings, min={dmin:.4f}, mean={spacings.mean():.4f})")


# ════════════════════════════════════════════════════════════════════════
#  FIGURE 8 — GUE pair-correlation kernel
# ════════════════════════════════════════════════════════════════════════

def make_fig8():
    fig, ax = plt.subplots(figsize=(10, 6.5), facecolor='white')

    u = np.linspace(-0.01, 5.0, 1000)
    K = sine_kernel(u)

    ax.fill_between(u, 0, K, where=(K >= 0), color=C_FILL, alpha=0.4, zorder=2)
    ax.plot(u, K, color=C_KERNEL, lw=2.5, zorder=5,
            label=r'$K(u)=1-(\sin\pi u/\pi u)^2$')
    ax.axhline(1.0, color='#aaaaaa', lw=0.8, ls=':', zorder=3,
               label=r'Decorrelation ($K\to 1$)')
    ax.axhline(0.0, color='#333333', lw=0.6, zorder=3)

    # K(0) = 0 — repulsion (red)
    ax.plot(0, 0, 'o', color=C_MIN, ms=10, zorder=7, mec='white', mew=1.2)
    ax.plot([], [], 'o', color=C_MIN, ms=8, label=r'$K(0)=0$ (repulsion)')

    # Zeros at integers (blue)
    for k in [1, 2, 3, 4]:
        ax.plot(k, 0, 'o', color=C_GUE, ms=7, zorder=6, mec='white', mew=0.8)
    ax.plot([], [], 'o', color=C_GUE, ms=6,
            label=r'$K(n)=0$, $n\in\mathbb{Z}\setminus\{0\}$')

    ax.set_xlabel(r'$u$ (unfolded spacing)')
    ax.set_ylabel(r'$K(u)$')
    ax.set_xlim(-0.15, 5.2)
    ax.set_ylim(-0.10, 1.20)
    # ticks kept for readability

    # Legend outside axes, right side — no overlap with any data
    ax.legend(loc='center left', fontsize=9.5, framealpha=0.95,
              bbox_to_anchor=(1.02, 0.5))

    plt.tight_layout()
    plt.savefig('fig8_sine_kernel.pdf', dpi=150, bbox_inches='tight',
                facecolor='white')
    plt.close()
    print("  Fig8 saved")


if __name__ == '__main__':
    print("Generating GUE figures...")
    make_fig7()
    make_fig8()
    print("Done.")
