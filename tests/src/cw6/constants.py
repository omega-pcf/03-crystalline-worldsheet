"""
CW6 Structural Constants
========================
Every constant carries its ORIGIN tag:

    DERIVED    — computed from axioms (phi, eps0, Mpcf, omega, ...)
    CODATA     — measured physical value (lepton masses, Lambda_obs, ...)
    AD_HOC     — parameter chosen for the check, not derived from the paper
                 (e.g., _V = 0.3581, _m0g = 1.7)

When a constant is AD_HOC, the check MUST document why the specific value
does not affect the conclusion (e.g., "holds for ALL m0 > 0").

References are to the labels printed in the manuscript (main.tex + src/chapters/*.tex).
"""
from __future__ import annotations

import numpy as np
from numpy.typing import ArrayLike

# ── §2 Core moduli (DERIVED) ──────────────────────────────────────────────

ARITY: int = 3                                       # eq:arity, ssec:arity
"""Arity n = floor(pi) = colour = number of generations."""

PHI: float = (1 + np.sqrt(5)) / 2                    # eq:base
"""Golden ratio: unique positive root of x^2 = x + 1."""

LN_PHI: float = np.log(PHI)                         # eq:bridge
"""Natural log of phi.  phi^{lambda_log} = 2 where lambda_log = ln2/ln phi."""

MU_3: float = 0.5                                    # prop:pcf-norms, thm:mu-diagram
"""mu_3 = |P||C||F| = 1/2.  The PCF modulus."""

NORM_P: float = 1 / np.sqrt(3)                       # prop:pcf-norms
"""|P| = 1/sqrt(3)."""

NORM_C: float = 1.0                                  # prop:pcf-norms
"""|C| = 1."""

NORM_F: float = np.sqrt(3) / 2                       # prop:pcf-norms
"""|F| = sqrt(3)/2."""

EPS_0: float = LN_PHI / (6 * np.sqrt(3))            # certainty_product
"""Epsilon_0 = ln(phi) / (6 sqrt 3).  The certainty constant."""

M_PCF: float = 6 * np.sqrt(3) * np.pi / np.log(PHI)  # eq:Mpcf (67.846)
"""M_PCF = 6 sqrt(3) pi / ln(phi) = pi / eps_0 (eq:Mpcf, certainty_product).
Defined by the closed form of eq:Mpcf so that eps_0 * M_PCF = pi is a
computed identity between two independently written constants, not a
tautology of the definition."""

OMEGA: complex = np.exp(2j * np.pi / 3)             # prop:eisenstein-cube
"""Primitive cube root of unity: omega^3 = 1, 1+omega+omega^2 = 0."""

# ── Precision views of the same three constants (single origin) ──────────
# The suite works at three precisions (float64 numpy, mpmath, sympy).  The
# definitions above are the origin; the views below are generated from the
# same manuscript formulas (eq:base, eq:bridge, eq:eps0, eq:Mpcf) so that no
# test module re-derives PHI / LN_PHI / EPS_0 / M_PCF on its own.

from mpmath import mp as _mp, mpf as _mpf, sqrt as _mpsqrt, log as _mplog, pi as _mpi
import sympy as _sp

_old_dps = _mp.dps
_mp.dps = 50                                   # create the views at 50 digits
PHI_MP: _mpf = (1 + _mpsqrt(5)) / 2
LN_PHI_MP: _mpf = _mplog(PHI_MP)
EPS_0_MP: _mpf = LN_PHI_MP / (6 * _mpsqrt(3))
M_PCF_MP: _mpf = 6 * _mpsqrt(3) * _mpi / LN_PHI_MP
_mp.dps = _old_dps

PHI_SYM = (1 + _sp.sqrt(5)) / 2                 # sympy, exact
LN_PHI_SYM = _sp.log(PHI_SYM)
EPS_0_SYM = LN_PHI_SYM / (6 * _sp.sqrt(3))
M_PCF_SYM = 6 * _sp.sqrt(3) * _sp.pi / LN_PHI_SYM


def bridge_T_MP(s1, s2):
    """eq:bridge in mpmath: T(s1, s2) = (1 + eps_0 phi^{s1}) / (1 + eps_0 phi^{s2})."""
    return (1 + EPS_0_MP * PHI_MP**s1) / (1 + EPS_0_MP * PHI_MP**s2)


# ── §4 Gravity (DERIVED) ─────────────────────────────────────────────────

LAMBDA_5: float = -4 * (4 - 1) / 2                    # lambda5_from_curvature
"""Lambda_5 = -d(d-1)/2 = -6  (AdS5 cosmological constant, d=4)."""

G_N: float = MU_3                                     # eq:israel, eq:brown-henneaux
"""Newton's constant G_N = mu_3 = 1/2."""

# ── §4 Observer spine (DERIVED) ──────────────────────────────────────────

D_H: float = np.log(3) / np.log(2)                   # eq:obs-interface
"""Hausdorff dimension of the 3-contraction attractor: 2^{d_H} = 3."""

F_MAX: float = 4.0                                    # eq:obs-spinstar
"""F_max = N^2 = 4  (N = 2 from eq:obs-spinstar)."""

SIGMA_G: int = ARITY - 1                              # eq:interval-levels
SIGMA_EM: int = ARITY                                 # eq:interval-levels
SIGMA_L: int = 2 * ARITY                              # eq:interval-levels
"""Level triple (sigma_G, sigma_EM, sigma_L) = (2, 3, 6)."""


# ── Tower modes (DERIVED) ─────────────────────────────────────────────────

def nmodes(sigma: float) -> int:
    """N_modes(sigma) = floor(pi * phi^sigma).  tower_mode_count."""
    return int(np.floor(np.pi * PHI**sigma))


NMODES_SEQUENCE: list[int] = [nmodes(s) for s in range(7)]
"""N_modes(0..6) = [3, 5, 8, 13, 21, 34, 56]."""

NMODES_CUMULATIVE: list[int] = [
    sum(NMODES_SEQUENCE[: k + 1]) for k in range(7)
]
"""Cumulative sum: [3, 8, 16, 29, 50, 84, 140]."""


# ── Bridge cocycle (DERIVED) ─────────────────────────────────────────────

def bridge_T(s1: float, s2: float) -> float:
    """T(s1, s2) = (1 + eps_0 phi^{s1}) / (1 + eps_0 phi^{s2}).  eq:bridge."""
    return (1 + EPS_0 * PHI**s1) / (1 + EPS_0 * PHI**s2)


# ── CODATA 2018 (MEASURED) ───────────────────────────────────────────────

ME_MEV: float = 0.51099895069                        # CODATA 2018
MP_MEV: float = 938.27208816                          # CODATA 2018
MMU_MEV: float = 105.6583755                          # CODATA 2018  (105.658 MeV)
MTAU_MEV: float = 1776.86                             # CODATA 2018  (1776.86 MeV)
LAMBDA_OBS: float = 2.888e-122                        # Planck 2018 (Lambda * l_P^2)
"""Cosmological constant in Planck units (05-discussion:175 prints it as
Lambda_obs l_P^2 = 2.888e-122).  eq:sigma-obs reads
sigma_obs = ln(6/Lambda_obs) / ln(phi) = 585.3 for this value; the backing is
test_observer.py::TestSigmaObs.test_sigma_obs."""

# ── AD_HOC (documented per check) ────────────────────────────────────────

V_MEISSNER: float = 0.3581                            # AD_HOC: Meissner dual potential
"""Used in eq:colour-gap checks.  Value from the dual superconductor model.
Holds for ANY V > 0 — the check tests positivity, not the specific value."""

M0_GENERIC: float = 1.7                               # AD_HOC: generic operator mass
"""Used in prop:gap-faces.  The ratio S(σ)/(m0 φ^σ) = π/m0 is constant in σ
for ANY m0 > 0.  This value is one instance."""

LAMBDA_QCD_SCALE: float = 0.3                         # AD_HOC: QCD scale
"""Used in Lambda_QCD continuum-limit checks.  The identity holds for ALL
positive Lambda, b0 — this value is one instance."""

B0_QCD: float = 1.7                                   # AD_HOC: one-loop beta
"""Used in Lambda_QCD continuum-limit checks.  See LAMBDA_QCD_SCALE."""
