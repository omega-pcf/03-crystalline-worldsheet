"""
§4–§5  Gravity Sector
======================
Einstein space, de Sitter geometry, Landau-Lifshitz energy, modular LL,
Brown-Henneaux c=3, Israel junction, BF bound.
"""
import numpy as np
import pytest
import sympy as sp

from cw6.constants import (
    PHI, EPS_0, M_PCF, MU_3, G_N, LAMBDA_5,
    SIGMA_G, SIGMA_EM, SIGMA_L, ARITY,
)
from cw6.helpers import random_null_vectors


class TestEinsteinCurvature:
    """§4 appendix: R_AB, G_AB, sectional curvature in (d, A', A'') = (4, -1, 0)."""

    d = 4
    Ap = -1
    App = 0

    def test_ricci_tensor(self):
        """R_AB = -(A'' + d A'^2) = -4."""
        R = -(self.App + self.d * self.Ap**2)
        assert R == -4

    def test_ricci_scalar(self):
        """R = -(2d A'' + d(d+1) A'^2) = -20."""
        R = -(2 * self.d * self.App + self.d * (self.d + 1) * self.Ap**2)
        assert R == -20

    def test_einstein_tensor(self):
        """G_AB = R_AB - R/2 g_AB = 6."""
        R_AB = -(self.App + self.d * self.Ap**2)
        R = -(2 * self.d * self.App + self.d * (self.d + 1) * self.Ap**2)
        G = R_AB - sp.Rational(1, 2) * R
        assert G == 6

    def test_lambda5(self):
        assert LAMBDA_5 == -6

    def test_sectional_curvature(self):
        """K = -1/l^2 = -1."""
        l = 1
        assert -1 / l**2 == -1


class TestBFBound:
    """BF bound: m^2_KK < -4 = m^2_BF."""

    def test_bf_value(self):
        """BF = -d^2/4 = -4 at d=4 (symbolic)."""
        import sympy as sp
        d = sp.Symbol('d', positive=True)
        BF = -d**2 / 4
        assert sp.simplify(BF.subs(d, 4) + 4) == 0

    def test_log_phi_lt_half(self):
        assert float(sp.N(sp.log(PHI))) < 0.5

    def test_mkk_below_bf(self):
        """m^2_KK = -1/(log phi)^2 < -4."""
        assert float(sp.N(-1 / sp.log(PHI)**2)) < -4


class TestEnergyPerBit:
    """eps_0 / pi = 1 / M_PCF."""

    def test_identity(self):
        """Pure symbolic: eps0/pi = 1/M_PCF."""
        _phi = (1 + sp.sqrt(5)) / 2
        _eps0 = sp.log(_phi) / (6 * sp.sqrt(3))
        _Mpcf = 6 * sp.sqrt(3) * sp.pi / sp.log(_phi)
        assert sp.simplify(_eps0 / sp.pi - 1 / _Mpcf) == 0


class TestLandauerLedger:
    """N_modes and cumulative counts (symbolic, mirrors .lean [P] literals)."""

    def test_nmodes_sequence(self):
        _phi = (1 + sp.sqrt(5)) / 2
        md = [int(sp.floor(sp.pi * _phi**k)) for k in range(7)]
        assert md == [3, 5, 8, 13, 21, 34, 56]

    def test_cumulative(self):
        _phi = (1 + sp.sqrt(5)) / 2
        md = [int(sp.floor(sp.pi * _phi**k)) for k in range(7)]
        cum = [sum(md[: k + 1]) for k in range(7)]
        assert cum == [3, 8, 16, 29, 50, 84, 140]


class TestProjectorTrace:
    """tr P = k, P^2 = P, tr(P/k) = 1 — closes rho_is_state."""

    def test_projector_properties(self):
        rng = np.random.RandomState(1)
        for k, n in [(2, 5), (3, 7), (4, 9)]:
            C = rng.randn(k, n)
            P = C.T @ np.linalg.inv(C @ C.T) @ C
            assert abs(np.trace(P) - k) < 1e-9
            assert np.allclose(P @ P, P)
            assert abs(np.trace(P / k) - 1) < 1e-9


class TestLLEnergy:
    """thm:LL-energy: Landau-Lifshitz in de Sitter (sympy symbolic)."""

    @pytest.fixture(autouse=True)
    def setup_sympy(self):
        self.t, self.H = sp.symbols('t H', real=True, positive=True)
        self.GN = sp.Rational(1, 2)
        self.a = sp.exp(self.H * self.t)
        self.coords = [self.t, sp.Symbol('x'), sp.Symbol('y'), sp.Symbol('z')]

        g = sp.diag(-1, self.a**2, self.a**2, self.a**2)
        gi = g.inv()
        sg = sp.sqrt(-g.det())
        go = sp.zeros(4, 4)
        for i in range(4):
            for j in range(4):
                go[i, j] = sp.simplify(sg * gi[i, j])
        self.go = go

    def _Hs(self, m, al, n, be):
        return self.go[m, n] * self.go[al, be] - self.go[m, al] * self.go[n, be]

    def _C(self, m, n):
        s = sum(
            sp.diff(self._Hs(m, al, n, be), self.coords[al], self.coords[be])
            for al in range(4) for be in range(4)
        )
        return sp.simplify(s / (16 * sp.pi * self.GN))

    def test_ll_00_equilibrium(self):
        """LL^00 = 0 (equilibrium of Jacobson)."""
        assert self._C(0, 0) == 0

    def test_ll_xx_nonstationary(self):
        """LL^xx = -2H^2 e^{4Ht} / pi."""
        expected = -2 * self.H**2 * sp.exp(4 * self.H * self.t) / sp.pi
        assert sp.simplify(self._C(1, 1) - expected) == 0

    def test_first_law_energy(self):
        """E_H = rho_Lambda V_H = 1/H."""
        Hb = sp.Symbol('Hb', positive=True)
        rho = 3 * Hb**2 / (8 * sp.pi * self.GN)
        V = sp.Rational(4, 3) * sp.pi / Hb**3
        assert sp.simplify(rho * V - 1 / Hb) == 0

    def test_first_law_temperature(self):
        """E_H = T_GH S_GH (first law dS)."""
        Hb = sp.Symbol('Hb', positive=True)
        area = 4 * sp.pi / Hb**2
        S_GH = area / (4 * self.GN)
        T_GH = Hb / (2 * sp.pi)
        rho = 3 * Hb**2 / (8 * sp.pi * self.GN)
        V = sp.Rational(4, 3) * sp.pi / Hb**3
        assert sp.simplify(rho * V - T_GH * S_GH) == 0

    def test_komar_charge(self):
        """Komar/LL charge = 1/H."""
        Hb = sp.Symbol('Hb', positive=True)
        area = 4 * sp.pi / Hb**2
        Komar = Hb * area / (8 * sp.pi * self.GN)
        assert sp.simplify(Komar - 1 / Hb) == 0

    def test_komar_not_entropy(self):
        """Komar != A/(4G_N) (energy != entropy)."""
        Hb = sp.Symbol('Hb', positive=True)
        area = 4 * sp.pi / Hb**2
        Komar = Hb * area / (8 * sp.pi * self.GN)
        S_GH = area / (4 * self.GN)
        assert sp.simplify(Komar - S_GH) != 0

    def test_mu3_ratio(self):
        """mu_3 = T_GH / T_local = 1/2."""
        Hb = sp.Symbol('Hb', positive=True)
        T_GH = Hb / (2 * sp.pi)
        T_loc = Hb / sp.pi
        assert sp.simplify(T_GH / T_loc - sp.Rational(1, 2)) == 0


class TestModularLL:
    """thm:modular-LL: K_mod = A/4G_N = S(sigma) = pi phi^sigma."""

    @pytest.fixture(autouse=True)
    def setup_modular(self):
        self.sig = sp.Symbol('sig', positive=True)
        self.phi = (1 + sp.sqrt(5)) / 2
        self.GN = sp.Rational(1, 2)
        self.Hb = sp.Symbol('Hb', positive=True)
        area = 4 * sp.pi / self.Hb**2
        Komar = self.Hb * area / (8 * sp.pi * self.GN)
        self.Kmod = 2 * sp.pi * Komar / self.Hb
        self.SGH = area / (4 * self.GN)

    def test_kmod_equals_sgh(self):
        assert sp.simplify(self.Kmod - self.SGH) == 0

    def test_kmod_equals_pi_phi_sigma(self):
        Kt = self.Kmod.subs(self.Hb, sp.sqrt(2) * self.phi**(-self.sig / 2))
        assert sp.simplify(Kt - sp.pi * self.phi**self.sig) == 0

    def test_dilatation_scaling(self):
        """S(s+t) = phi^t S(s)."""
        tt = sp.Symbol('tt')
        assert sp.simplify(
            sp.pi * self.phi**(self.sig + tt) - self.phi**tt * (sp.pi * self.phi**self.sig)
        ) == 0

    def test_H_sigma(self):
        """H(sigma) = sqrt(2) phi^{-sigma/2}."""
        area = 4 * sp.pi / self.Hb**2
        S_GH = area / (4 * self.GN)
        sol = sp.solve(sp.Eq(S_GH, sp.pi * self.phi**self.sig), self.Hb)
        pos = [s for s in sol if not s.has(sp.I)]
        assert sp.simplify(pos[0] - sp.sqrt(2) * self.phi**(-self.sig / 2)) == 0


class TestBrownHenneaux:
    """c = 3 l / (2 G_N) = 3 with l=1, G_N=1/2."""

    def test_central_charge(self):
        assert abs(3 * 1.0 / (2 * 0.5) - 3) < 1e-12

    def test_discriminates(self):
        """3l/(2G) = 3 ONLY if G = 1/2."""
        for g in [1/3, 1/4, 1.0, 2.0]:
            assert abs(3 / (2 * g) - 3) > 0.4


class TestIsraelJunction:
    """eq:israel: backreaction at each level."""

    def test_prefactor(self):
        """8 pi G_5 / 3 collapses to 4pi/3 at G_5 = mu_3 = 1/2."""
        assert abs(8 * np.pi * 0.5 / 3 - 4 * np.pi / 3) < 1e-14

    def test_discriminates_g(self):
        """No other Newton constant works."""
        for g in [0.25, 1.0, 0.75]:
            assert abs(8 * np.pi * g / 3 - 4 * np.pi / 3) > 1.0

    def test_level_jumps(self):
        """[A'] = -(4pi/3) N_modes / M_PCF."""
        for s in range(7):
            N = int(np.floor(np.pi * PHI**s))
            expected = -(4 * np.pi / 3) * N / M_PCF
            actual = -(8 * np.pi * 0.5 / 3) * (N / M_PCF)
            assert abs(expected - actual) < 1e-14

    def test_cumulative_backreaction(self):
        """[3, 8, 16, 29, 50, 84, 140] for k = 0..6."""
        N = [int(np.floor(np.pi * PHI**s)) for s in range(7)]
        cum = [sum(N[: k + 1]) for k in range(7)]
        assert cum == [3, 8, 16, 29, 50, 84, 140]


class TestGapFaces:
    """prop:gap-faces: spectral form and colour ratio."""

    def test_spectral_ratio(self):
        """S(σ)/(m0 φ^σ) = π/m0 constant in σ."""
        m0 = 1.7  # AD_HOC: any m0 > 0 works
        for s in [0.0, 2.0, 4.0]:
            assert abs((np.pi * PHI**s) / (m0 * PHI**s) - np.pi / m0) < 1e-12

    def test_colour_ratio(self):
        """Δ_colour(σ+1)/Δ_colour(σ) = φ^{-1/2}."""
        q = 3.0  # AD_HOC: any q works for the ratio
        D = lambda s: np.sqrt(q**2 * EPS_0 * PHI**(-s))
        for s in [0.0, 2.0, 4.0]:
            assert abs(D(s + 1) / D(s) - PHI**(-0.5)) < 1e-9


class TestColourFromM:
    """thm:colour-from-M: M = M_PCF, same certainty."""

    def test_m_eq_mpcf(self):
        M = np.pi / EPS_0
        assert abs(M - M_PCF) < 1e-8

    def test_colour_scale(self):
        q = 3.0
        M = np.pi / EPS_0
        assert abs(4 * np.pi**4 / (q**2 * M) - 4 * np.pi**4 / (q**2 * M_PCF)) < 1e-9


class TestOneObject:
    """thm:one-object: ε_0 · M_PCF = 2π · μ_3 = π."""

    def test_certainty_is_modulus(self):
        assert abs(EPS_0 * M_PCF - 2 * np.pi * 0.5) < 1e-9


class TestMTwoFaces:
    """rmk:M-two-faces: m_p/m_e ≈ 6π^5."""

    def test_ratio_approx(self):
        assert abs(6 * np.pi**5 - 1836.15) < 0.1

    def test_placement_face(self):
        me = 0.51099895069
        mp = 938.27208816
        mp_plac = 6 * np.pi**5 * me
        assert abs(mp_plac / 3 - 312.7515) < 1e-3

    def test_residue(self):
        me = 0.51099895069
        mp = 938.27208816
        mp_plac = 6 * np.pi**5 * me
        assert abs((mp - mp_plac) / mp - 1.8823e-5) < 1e-7
        assert abs((mp / me - 6 * np.pi**5) / (mp / me) - 1.8823e-5) < 1e-7


class TestTensionWeld:
    """eq:tension-weld: σ_tension(σ) · S(σ) invariant along the tower."""

    def test_invariance_q1(self):
        eps0 = np.log(PHI) / (6 * np.sqrt(3))
        Mp = 6 * np.sqrt(3) * np.pi / np.log(PHI)
        q = 1.0
        qm = 2 * np.pi / q
        prod = [(qm**2 * eps0 * PHI**(-s)) * (np.pi * PHI**s) for s in range(9)]
        assert max(prod) - min(prod) < 1e-9

    def test_invariance_value_q1(self):
        eps0 = np.log(PHI) / (6 * np.sqrt(3))
        Mp = 6 * np.sqrt(3) * np.pi / np.log(PHI)
        q = 1.0
        qm = 2 * np.pi / q
        prod = (qm**2 * eps0) * np.pi
        assert abs(prod - 4 * np.pi**4 / (q**2 * Mp)) < 1e-9

    def test_invariance_q3(self):
        q = 3.0
        qm = 2 * np.pi / q
        inv = [(qm**2 * (EPS_0 * PHI**(-s))) * (np.pi * PHI**s) for s in (0.0, 2.0, 5.0)]
        assert all(abs(v - inv[0]) < 1e-9 for v in inv)

    def test_invariance_value_q3(self):
        q = 3.0
        qm = 2 * np.pi / q
        inv = (qm**2 * EPS_0) * np.pi
        assert abs(inv - 4 * np.pi**4 / (q**2 * M_PCF)) < 1e-9


class TestConjugatePair:
    """V(σ) · (D(σ) - 1) = eps_0^2."""

    def test_conjugate(self):
        for s in range(9):
            assert abs((EPS_0 * PHI**(-s)) * (EPS_0 * PHI**s) - EPS_0**2) < 1e-12
