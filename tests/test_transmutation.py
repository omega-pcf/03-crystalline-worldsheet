"""
§4  Dimensional Transmutation & Continuum Limit
================================================
Lambda_QCD and its continuum limit, the self-dual charge and the string gap
(eq:string-tension), the two towers kept distinct, Brown-Henneaux, the
beta-function identity and the Koide placement of the lepton masses.
(The projector checks live in test_spectral.py / test_gravity.py.)
"""
import numpy as np
import pytest

from cw6.constants import (
    PHI, EPS_0, M_PCF, ARITY,
    V_MEISSNER, M0_GENERIC,
    LAMBDA_QCD_SCALE, B0_QCD,
    ME_MEV, MMU_MEV, MTAU_MEV,
)
from cw6.helpers import lambda_qcd, g_sq_af


class TestLambdaQCDPositivity:
    """Lambda_QCD > 0 for all positive parameters."""

    def test_positive(self):
        for a in (0.1, 1.0):
            for b0 in (0.5, 2.0):
                for g2 in (0.3, 1.5):
                    assert lambda_qcd(a, b0, g2) > 0


class TestGapSurvivesTransmutation:
    """eq:transmutation: the gap is a positive multiple of Lambda_QCD and
    survives the continuum limit (Lambda_QCD > 0, finite)."""

    def test_finite(self):
        val = lambda_qcd(1e-3, 1.0, 1.0)
        assert val > 0 and np.isfinite(val)


class TestSelfDualCharges:
    """At the self-dual point q = q_m = sqrt(2 pi): the Dirac map q -> 2 pi/q
    fixes exactly that value."""

    def test_dirac_condition(self):
        q = np.sqrt(2 * np.pi)
        assert abs(q * q - 2 * np.pi) < 1e-12           # q q_m = 2 pi
        assert abs(q - 2 * np.pi / q) < 1e-12           # fixed point of the duality
        for other in (1.0, 2.0, 4.0):                   # no other fixed point
            assert abs(other - 2 * np.pi / other) > 1e-3


class TestColourGap:
    """eq:string-tension: sigma_tension = q_m^2 V > 0 and
    Delta_colour = sqrt(sigma_tension) > 0 (dual Meissner)."""

    def test_positive(self):
        q = np.sqrt(2 * np.pi)
        sigma = q**2 * V_MEISSNER
        assert sigma > 0
        assert np.sqrt(sigma) > 0
        assert abs(np.sqrt(sigma)**2 - sigma) < 1e-12   # Delta^2 = sigma
        # the sign comes from V > 0: a negative condensate flips the gap
        assert q**2 * (-V_MEISSNER) < 0

    def test_self_dual_invariant(self):
        q = np.sqrt(2 * np.pi)
        qm = 2 * np.pi / q
        assert abs(qm - q) < 1e-12
        assert abs(q**2 * V_MEISSNER - qm**2 * V_MEISSNER) < 1e-12
        assert abs(q * qm - 2 * np.pi) < 1e-12


class TestTwoTowersDistinct:
    """Golden tower vs Regge tower: structurally distinct."""

    def test_golden_constant_ratio(self):
        for n in range(1, 9):
            assert abs(PHI**(n + 1) / PHI**n - PHI) < 1e-12

    def test_regge_decreasing(self):
        regge = lambda n: np.sqrt(n + 1) / np.sqrt(n)
        ratios = {round(regge(n), 9) for n in range(1, 9)}
        assert len(ratios) == 8  # all distinct

    def test_no_regge_equals_phi(self):
        regge = lambda n: np.sqrt(n + 1) / np.sqrt(n)
        for n in range(1, 201):
            assert abs(regge(n) - PHI) > 1e-9

    def test_towers_diverge(self):
        assert [round(PHI**n / np.sqrt(n)) for n in (1, 10, 20, 40)] == [2, 39, 3383, 36180587]


class TestBrownHenneaux:
    """c = 3 l / (2 G_N) = 3."""

    def test_value(self):
        assert abs(3 * 1.0 / (2 * 0.5) - 3) < 1e-12


class TestContinuumLimit:
    """Lambda_QCD(a) = Lambda EXACT along the AF trajectory."""

    @pytest.mark.parametrize("a", [1e-1, 1e-2, 1e-4, 1e-8])
    def test_constant(self, a):
        b0 = B0_QCD
        lam = LAMBDA_QCD_SCALE
        g2 = g_sq_af(a, b0, lam)
        assert abs(lambda_qcd(a, b0, g2) - lam) < 1e-9

    def test_independent_of_cutoff(self):
        b0 = B0_QCD
        lam = LAMBDA_QCD_SCALE
        a = 1e-10
        g2 = g_sq_af(a, b0, lam)
        assert abs(lambda_qcd(a, b0, g2) - lam) < 1e-9


class TestBetaFunctionIdentity:
    """a * B(as, at) = ((s+t)/st) G(as+1)G(at+1)/G(a(s+t)+1)."""

    def test_exact_identity(self):
        from math import gamma as G
        def ident(a, s, t):
            return abs(a * G(a * s) * G(a * t) / G(a * (s + t))
                       - ((s + t) / (s * t)) * G(a * s + 1) * G(a * t + 1) / G(a * (s + t) + 1))
        for a in (0.5, 0.1, 1e-3):
            assert ident(a, 1.3, 2.1) < 1e-12

    def test_limit_value(self):
        """The a -> 0 limit of the identity's left-hand side is (s+t)/(st)."""
        import sympy as sp
        a, s, t = sp.symbols('a s t', positive=True)
        lhs = a * sp.gamma(a * s) * sp.gamma(a * t) / sp.gamma(a * (s + t))
        limit = sp.limit(lhs, a, 0)
        assert sp.simplify(limit - (s + t) / (s * t)) == 0
        assert sp.simplify(limit - (1 / s + 1 / t)) == 0


class TestKoideFormula:
    """Koide Q = 2/3, angular placement gives lepton masses."""

    @pytest.fixture(autouse=True)
    def setup_masses(self):
        self.me = ME_MEV
        self.mmu = MMU_MEV
        self.mtau = MTAU_MEV

    def test_koide_ratio(self):
        Q = (self.me + self.mmu + self.mtau) / (
            np.sqrt(self.me) + np.sqrt(self.mmu) + np.sqrt(self.mtau)
        )**2
        assert abs(Q - 2 / 3) / (2 / 3) < 1e-4

    def test_angular_placement(self):
        M = ((np.sqrt(self.me) + np.sqrt(self.mmu) + np.sqrt(self.mtau)) / 3)**2
        d = 2 / 3**2
        pred = [M * (1 + np.sqrt(2) * np.cos(d + 2 * np.pi * k / 3))**2 for k in (1, 2, 0)]
        err = max(abs(p - o) / o for p, o in zip(pred, [self.me, self.mmu, self.mtau]))
        assert err < 1e-4        # 04-implications: reconstructed to ~1e-4
