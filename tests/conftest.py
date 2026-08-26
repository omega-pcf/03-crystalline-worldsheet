"""
CW6 pytest configuration
========================
Fixtures shared across all test modules.  Constants come from cw6.constants;
this file provides pytest fixtures that wrap them for easy injection.
"""
from __future__ import annotations

import pytest
import numpy as np
from fractions import Fraction


# ── Custom CLI options ───────────────────────────────────────────────────

def pytest_addoption(parser):
    parser.addoption(
        "--repulsion-full",
        action="store_true",
        default=False,
        help="Run repulsion tests at full precision (25 dps, 238 zeros, ~8 min)",
    )


# ── Numpy precision ──────────────────────────────────────────────────────

@pytest.fixture
def np_1e12():
    """Default tolerance for float64 numpy checks."""
    return 1e-12


@pytest.fixture
def np_1e9():
    """Looser tolerance for checks involving division or accumulation."""
    return 1e-9


# ── mpmath precision tiers ───────────────────────────────────────────────

@pytest.fixture
def mp25():
    """mpmath at 25-digit precision (standard backing precision)."""
    from mpmath import mp
    mp.dps = 25
    yield mp
    mp.dps = 15  # reset


@pytest.fixture
def mp40():
    """mpmath at 40-digit precision (§2 reordered section)."""
    from mpmath import mp
    old = mp.dps
    mp.dps = 40
    yield mp
    mp.dps = old


# ── Tolerance helpers ────────────────────────────────────────────────────

@pytest.fixture
def tol(mp25):
    """Derived tolerance: 10^{-(dps-6)} for exact algebraic identities."""
    from mpmath import mpf
    return mpf(10)**(-(mp25.dps - 6))


@pytest.fixture
def tol_eig(mp25):
    """Derived tolerance for iterative diagonalization: 10^{-(dps//2)}."""
    from mpmath import mpf
    return mpf(10)**(-(mp25.dps // 2))


# ── Random state fixtures ────────────────────────────────────────────────

@pytest.fixture
def rng_jacobson():
    """Deterministic RNG for Jacobson null-vector checks (seed=7)."""
    return np.random.RandomState(7)


@pytest.fixture
def rng_projector():
    """Deterministic RNG for projector checks (seed=1)."""
    return np.random.RandomState(1)


@pytest.fixture
def rng_frame():
    """Deterministic RNG for frame-invariance checks (seed=5)."""
    return np.random.RandomState(5)


@pytest.fixture
def rng_rp():
    """Deterministic RNG for RP measure checks (seed=23)."""
    import random
    rng = random.Random(23)
    return rng


# ── Fractions fixture ────────────────────────────────────────────────────

@pytest.fixture
def half():
    """Fraction(1, 2) for exact rational arithmetic."""
    return Fraction(1, 2)


# ── Measured values (not derived) ───────────────────────────────────────

@pytest.fixture
def lepton_masses():
    """Lepton masses in MeV from CODATA 2018."""
    from cw6.constants import ME_MEV, MMU_MEV, MTAU_MEV
    return ME_MEV, MMU_MEV, MTAU_MEV


# ── Section markers ──────────────────────────────────────────────────────

# These are applied via @pytest.mark.<name> in test files.
# Defined here so pytest discovers them.
