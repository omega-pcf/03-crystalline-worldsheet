"""
§1–§2  Core Identities
======================
Golden ratio, PCF norms, Eisenstein cube root, Gamma(1/2), cosine identity.
All constants DERIVED — no measured values.
"""
import numpy as np
import pytest
from math import gamma as gamma_fn

from cw6.constants import (
    PHI, LN_PHI, EPS_0, M_PCF, OMEGA, ARITY,
    NORM_P, NORM_C, NORM_F, MU_3,
)


class TestDimensionLadder:
    """§1: R --i^2=-1--> C --phi^2=phi+1--> E^3"""

    def test_imaginary_unit(self):
        """i^2 = -1  (definition of the complex step)."""
        assert abs(1j**2 + 1) < 1e-12

    def test_phi_identity(self):
        """phi^2 = phi + 1  (definition of the golden ratio)."""
        assert abs(PHI**2 - (PHI + 1)) < 1e-12


class TestPCFNorms:
    """prop:pcf-norms: |P| = 1/sqrt(3), |C| = 1, |F| = sqrt(3)/2."""

    @pytest.mark.parametrize("name,actual,expected", [
        ("norm_P", NORM_P, 1 / np.sqrt(3)),
        ("norm_C", NORM_C, 1.0),
        ("norm_F", NORM_F, np.sqrt(3) / 2),
    ])
    def test_individual_norms(self, name, actual, expected):
        assert abs(actual - expected) < 1e-12, f"{name}: {actual} != {expected}"

    def test_product_is_mu(self):
        """|P||C||F| = 1/2 = mu_3 = |Omega|."""
        assert abs(NORM_P * NORM_C * NORM_F - MU_3) < 1e-12


class TestCertainty:
    """eq:certainty: eps_0 * M_PCF = pi."""

    def test_certainty_product(self):
        assert abs(EPS_0 * M_PCF - np.pi) < 1e-10

    def test_certainty_inverse(self):
        """1 / (eps_0 / pi) = M_PCF."""
        assert abs(np.pi / EPS_0 - M_PCF) < 1e-10


class TestGammaHalf:
    """Gamma(1/2) = sqrt(pi) by TWO routes."""

    def test_gamma_function_route(self):
        """Via the Gamma function directly."""
        assert abs(gamma_fn(0.5) - np.sqrt(np.pi)) < 1e-12

    def test_gaussian_integral_route(self):
        """Via the Gaussian integral: Gamma(1/2)^2 = pi."""
        assert abs(gamma_fn(0.5)**2 - np.pi) < 1e-12


class TestEisensteinCube:
    """prop:eisenstein-cube: omega^3 = 1, 1 + omega + omega^2 = 0."""

    def test_omega_cubed(self):
        assert abs(OMEGA**3 - 1) < 1e-12

    def test_zero_sum(self):
        assert abs(1 + OMEGA + OMEGA**2) < 1e-12


class TestCosinePi5:
    """cos(pi/5) = phi/2."""

    def test_cosine_value(self):
        assert abs(np.cos(np.pi / 5) - PHI / 2) < 1e-12


class TestPiBridge:
    """prop:pi-bridge: pi = 5 arccos(phi/2).
    
    Connects the circle (trigonometry) to the golden ratio (algebra).
    """

    def test_cosine_identity(self):
        """cos(pi/5) = phi/2 — the bridge equation."""
        assert abs(np.cos(np.pi / 5) - PHI / 2) < 1e-12

    def test_arccos_inverse(self):
        """arccos(phi/2) = pi/5 — the inverse route."""
        assert abs(np.arccos(PHI / 2) - np.pi / 5) < 1e-12

    def test_five_arccos(self):
        """5 * arccos(phi/2) = pi — the bridge in its full form."""
        assert abs(5 * np.arccos(PHI / 2) - np.pi) < 1e-12
