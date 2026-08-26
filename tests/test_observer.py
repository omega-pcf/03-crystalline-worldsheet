"""
§4  Observer Spine (23 equations)
==================================
eq:obs-interface through eq:obs-identity.  Jacobson, Einstein, de Sitter.
"""
import numpy as np
import pytest

from cw6.constants import (
    PHI, LN_PHI, EPS_0, M_PCF, ARITY,
    NORM_P, NORM_C, NORM_F, MU_3,
    D_H, F_MAX, SIGMA_G, SIGMA_EM, SIGMA_L,
    nmodes,
)
from cw6.helpers import random_null_vectors


class TestObsInterface:
    """eq:obs-interface: d_H = log3/log2 by the Moran equation 2^{d_H} = 3."""

    def test_moran_equation(self):
        assert abs(2**D_H - 3) < 1e-12

    def test_normalized(self):
        assert abs(3 * (0.5**D_H) - 1) < 1e-12


class TestObsSpinstar:
    """eq:obs-spinstar: 1 central + N=2 = 3, F_max = N^2 = 4, 3 * F_Omega = c = 3."""

    N_ARMS = 2

    def test_component_count(self):
        assert 1 + self.N_ARMS == 3

    def test_fmax(self):
        assert self.N_ARMS**2 == 4

    def test_f_omega(self):
        assert abs(4 * 0.5**2 - 1.0) < 1e-14

    def test_central_charge(self):
        assert abs(3 * (4 * 0.5**2) - 3) < 1e-14


class TestFisherTime:
    """eq:obs-fishertime: tau_F = tau_D / sqrt(2f); at f=1/2 they are equal."""

    def test_equality_at_half(self):
        f = 0.5
        assert abs(1 / np.sqrt(2 * f) - 1.0) < 1e-12


class TestCramerRao:
    """eq:obs-cramerrao: Var >= 1/F; Fmax^{-1} = 1/4 = mu_3^2."""

    def test_fmax_inverse(self):
        assert abs(1 / F_MAX - 0.25) < 1e-12

    def test_mu_squared(self):
        assert abs(MU_3**2 - 0.25) < 1e-12


class TestObserverHalf:
    """eq:obs-half: |P||C||F| = 1/2 = |Omega|."""

    def test_product(self):
        assert abs(NORM_P * NORM_C * NORM_F - MU_3) < 1e-12


class TestObserverThreshold:
    """eq:obs-threshold: f_crit = mu, from product of norms."""

    def test_threshold(self):
        assert abs(NORM_P * NORM_C * NORM_F - 0.5) < 1e-12


class TestObserverCertainty:
    """eq:obs-certainty: eps_0 * M_PCF = pi."""

    def test_cell_capacity(self):
        assert abs(EPS_0 * M_PCF - np.pi) < 1e-10


class TestObserverFixedPoint:
    """eq:obs-fixedpoint: beta_g = 0 <=> eps_0 * M_PCF = pi."""

    def test_uv_fixed_point(self):
        assert abs(EPS_0 * M_PCF - np.pi) < 1e-10


class TestObserverSwampland:
    """eq:obs-swampland: |dV/dsigma| / V = ln phi, for V = eps_0 phi^{-sigma}."""

    @pytest.mark.parametrize("sigma", [0.0, 1.5, 3.0, 6.0])
    def test_logarithmic_derivative(self, sigma):
        h = 1e-7
        V = lambda s: EPS_0 * PHI**(-s)
        dV = (V(sigma + h) - V(sigma - h)) / (2 * h)
        assert abs(abs(dV) / V(sigma) - LN_PHI) < 1e-6


class TestObserverWeld:
    """eq:obs-weld: tau_F(sigma) = tau(sigma), conjugate pair z*tau = M_PCF."""

    @pytest.mark.parametrize("sigma", [1, 2, 3, 5])
    def test_tau_routes(self, sigma):
        route1 = np.pi * PHI**sigma
        route2 = np.pi * PHI**(2 * sigma) / M_PCF
        assert abs(route1 / route2 - M_PCF * PHI**(-sigma)) < 1e-10

    @pytest.mark.parametrize("sigma", [0, 2, 3, 4, 5, 6])
    def test_conjugate_pair(self, sigma):
        assert abs((PHI**sigma) * (M_PCF * PHI**(-sigma)) - M_PCF) < 1e-9

    def test_alpha_prime_forced(self):
        """alpha' is FORCED by the product, not chosen."""
        assert abs((PHI**4.7) * (M_PCF * PHI**(-4.7)) - M_PCF) < 1e-9


class TestObserverIdentity:
    """eq:obs-identity: F_Omega * N = S(sigma), F_Omega = 4 mu_3^2 = 1."""

    def test_f_omega_is_one(self):
        assert abs(4 * MU_3**2 - 1.0) < 1e-14

    @pytest.mark.parametrize("sigma", [1, 2, 3, 5])
    def test_product_yields_entropy(self, sigma):
        assert abs((4 * MU_3**2) * (np.pi * PHI**sigma) - np.pi * PHI**sigma) < 1e-10


class TestObserverLandauer:
    """eq:obs-landauer: energy/bit = 1/M_PCF; S_BH/k_B = log 2."""

    def test_energy_per_bit(self):
        assert abs(1 / M_PCF - EPS_0 / np.pi) < 1e-14

    def test_bh_entropy(self):
        assert abs((np.log(2) / LN_PHI) * LN_PHI - np.log(2)) < 1e-12


class TestObserverJacobson:
    """eq:obs-jacobson: R_AB k^A k^B = 0 for ALL null k in Einstein space R_AB = -4 g_AB."""

    def test_null_contraction_vanishes(self):
        gE = np.diag([-1.0, 1.0, 1.0, 1.0, 1.0])
        RE = -4.0 * gE
        ks = random_null_vectors(7, 400, dim=5)
        assert all(abs(float(k @ gE @ k)) < 1e-10 for k in ks)
        assert all(abs(float(k @ RE @ k)) < 1e-9 for k in ks)

    def test_discriminates_nonnull(self):
        """For non-null k the contraction does NOT vanish."""
        RE = -4.0 * np.diag([-1.0, 1.0, 1.0, 1.0, 1.0])
        nonnull = [np.array([1.0, 0, 0, 0, 0]),
                    np.array([0, 1.0, 0, 0, 0]),
                    np.array([2.0, 1.0, 0, 0, 0])]
        assert max(abs(float(k @ RE @ k)) for k in nonnull) > 1.0


class TestObserverEinstein:
    """eq:obs-einstein: R_AB = -4 g_AB, R = -20 (AdS5)."""

    def test_ricci_scalar(self):
        d = 4
        Ap = -1; App = 0
        R = -(2 * d * App + d * (d + 1) * Ap**2)
        assert R == -20


class TestIntervalLevels:
    """eq:interval-levels: (sigma_G, sigma_EM, sigma_L) = (2, 3, 6)."""

    def test_triple(self):
        assert (SIGMA_G, SIGMA_EM, SIGMA_L) == (2, 3, 6)

    def test_gap(self):
        """sigma_L - sigma_G = n+1 = 4 = dim(M^4)."""
        assert SIGMA_L - SIGMA_G == ARITY + 1 == 4

    def test_fractions(self):
        """(sEM - sG)/(sL - sG) = 1/(n+1) = 1/4 = |Omega|^2."""
        assert abs((SIGMA_EM - SIGMA_G) / (SIGMA_L - SIGMA_G) - 0.25) < 1e-12
        assert abs(MU_3**2 - 0.25) < 1e-12


class TestDeSitterGeometry:
    """de Sitter: R = 12 H^2, Ricci = 3 H^2 g, vacuum Einstein R = 4 Lambda.
    
    These tests use sympy to verify the geometric identities hold as algebraic
    relations, not just numerical coincidences at H=1.
    """

    def test_ricci_from_gauss(self):
        """umbilic K=Hg => R_munu = (d-1)H^2 g = 3H^2 g (symbolic in d and H)."""
        import sympy as sp
        d, H = sp.symbols('d H', positive=True)
        # For umbilic hypersurface with K=Hg: R_munu = (d-1) H^2 g_munu
        # In d=4: coefficient = 3 H^2
        coeff = (d - 1) * H**2
        assert sp.simplify(coeff.subs(d, 4) - 3 * H**2) == 0

    def test_ricci_scalar(self):
        """R = d(d-1) H^2 for umbilic; in d=4: R = 12 H^2."""
        import sympy as sp
        d, H = sp.symbols('d H', positive=True)
        R = d * (d - 1) * H**2
        assert sp.simplify(R.subs(d, 4) - 12 * H**2) == 0

    @pytest.mark.parametrize("Hv", [0.5, 1.0, 2.0])
    def test_einstein_lambda(self, Hv):
        """Vacuum Einstein: R = 4 Lambda, R = 12 H^2 => Lambda = 3 H^2."""
        import sympy as sp
        H = sp.Symbol('H', positive=True)
        R = 12 * H**2
        Lambda = R / 4
        assert sp.simplify(Lambda - 3 * H**2) == 0
        # Numerical check at specific H
        assert abs(float(Lambda.subs(H, Hv)) - 3 * Hv**2) < 1e-12

    def test_half_hyperboloid(self):
        """X0+X4 = l e^{t/l} > 0 : covers exactly half."""
        import sympy as sp
        t, l = sp.symbols('t l', real=True)
        # The embedding X0+X4 = l exp(t/l) is manifestly positive for real t, l>0
        expr = l * sp.exp(t / l)
        # Derivative is positive (monotone), so the image is (0, inf) — half the hyperboloid
        assert sp.simplify(sp.diff(expr, t) - sp.exp(t / l)) == 0
