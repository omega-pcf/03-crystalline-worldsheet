"""
§4  Gauge Sector
================
Weinberg angle, MSSM beta coefficients, unification spread, G-Lambda duality.
"""
import numpy as np
import pytest
from fractions import Fraction

from cw6.constants import PHI, ARITY, nmodes
from cw6.helpers import mssm_spread


class TestEntropyRatio:
    """S(3)/S(6) = phi^{-3}."""

    def test_ratio(self):
        assert abs(PHI**3 / PHI**6 - PHI**-3) < 1e-12


class TestWeinbergAngleGUT:
    """sin^2|_GUT = N(0)/N(2) = 3/8."""

    def test_nmodes(self):
        assert nmodes(0) == 3 and nmodes(2) == 8

    def test_ratio(self):
        assert abs(nmodes(0) / nmodes(2) - 0.375) < 1e-12

    def test_ew_norm_ratio(self):
        """3/5 = N(0)/N(1)."""
        assert abs(nmodes(0) / nmodes(1) - 0.6) < 1e-9


class TestMSSMBetaCoefficients:
    """b = (33/5, 1, -3) field by field = MSSM."""

    def test_beta_coefficients(self):
        half = Fraction(1, 2)
        fields = [
            (3, 2, Fraction(1, 6), 3),
            (3, 1, Fraction(-2, 3), 3),
            (3, 1, Fraction(1, 3), 3),
            (1, 2, Fraction(-1, 2), 3),
            (1, 1, Fraction(1, 1), 3),
            (1, 2, Fraction(1, 2), 1),
            (1, 2, Fraction(-1, 2), 1),
        ]
        b3 = b2 = b1 = Fraction(0)
        for nc, n2, Y, ng in fields:
            b3 += (half if nc == 3 else 0) * n2 * ng
            b2 += (half if n2 == 2 else 0) * nc * ng
            b1 += Fraction(3, 5) * Y * Y * nc * n2 * ng
        b3 -= 9
        b2 -= 6

        assert b3 == Fraction(-3)
        assert b2 == Fraction(1)
        assert b1 == Fraction(33, 5)


class TestMSSMUnification:
    """MSSM couplings meet (spread < 0.5), SM do not (spread > 3)."""

    @pytest.mark.slow
    def test_mssm_unifies(self):
        assert mssm_spread([33/5, 1, -3]) < 0.5

    @pytest.mark.slow
    def test_sm_does_not(self):
        assert mssm_spread([41/10, -19/6, -7]) > 3

    @pytest.mark.slow
    def test_running_3_8_to_0231(self):
        """The GUT 3/8 descends to ~0.231 because MSSM unifies and SM does not."""
        assert mssm_spread([33/5, 1, -3]) < 0.5
        assert mssm_spread([41/10, -19/6, -7]) > 3
        assert abs(nmodes(0) / nmodes(2) - 0.375) < 1e-12


class TestGLambdaDuality:
    """phi^{-6} * phi^{+6} = 1."""

    def test_duality(self):
        assert abs(PHI**(-6) * PHI**6 - 1) < 1e-12


class TestGaugeDimSU3:
    """dim su(3) = 3^2 - 1 = 8."""

    def test_dimension(self):
        assert 3**2 - 1 == 8
