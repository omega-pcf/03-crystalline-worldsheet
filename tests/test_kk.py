"""
§4  Kaluza-Klein Spectrum
=========================
Discrete KK operator, BF bound, reciprocity, arity uniqueness.
"""
import pytest
from mpmath import (
    mp, mpf, mpc, pi, exp, sqrt, log, sin as mpsin,
    matrix as mpmat, eig as mpeig,
)

mp.dps = 25

PHI = (1 + sqrt(5)) / 2
LN_PHI = log(PHI)


# ── Operator construction ────────────────────────────────────────────────

def kk_operator(up, down, N=7, sc=None):
    """Tridiagonal of N levels: diagonal -2, jumps `up` and `down`, scale sc."""
    if sc is None:
        sc = 1 / LN_PHI**2
    L = mpmat(N, N)
    for s in range(N):
        L[s, s] = -2 * sc
        if s > 0:
            L[s, s-1] = up * sc
        if s < N - 1:
            L[s, s+1] = down * sc
    return L


def kk_spectrum(up, down, N=7):
    """Sorted real eigenvalues of the KK operator."""
    return sorted(e.real for e in mpeig(kk_operator(up, down, N), left=False, right=False))


# ── Tests ────────────────────────────────────────────────────────────────

class TestKKReciprocity:
    """The two jumps are reciprocal: phi^2 * phi^{-2} = 1."""

    def test_reciprocal(self):
        phi_curr = (1 + sqrt(mpf(5))) / 2
        assert abs(phi_curr**2 * phi_curr**(-2) - 1) < mpf('1e-20')

    def test_geometric_mean(self):
        phi_curr = (1 + sqrt(mpf(5))) / 2
        assert abs(sqrt(phi_curr**2 * phi_curr**(-2)) - 1) < mpf('1e-20')


class TestKKSpectrum:
    """Discrete spectrum = -4 sin^2(k pi / 4(n+1)) / ln^2 phi."""

    N_AR = 3
    NLEV = 2 * N_AR + 1  # 7

    def test_numerical_equals_closed(self):
        lam_num = kk_spectrum(PHI**2, PHI**(-2), self.NLEV)
        lam_cf = sorted(
            -4 * mpsin(k * pi / (4 * (self.N_AR + 1)))**2 / LN_PHI**2
            for k in range(1, self.NLEV + 1)
        )
        tol = mpf(10)**(-(mp.dps // 2))  # iterative diagonalization tolerance
        assert max(abs(a - b) for a, b in zip(lam_num, lam_cf)) < tol

    def test_mass_squared_positive(self):
        """m^2_k = -lambda_k > 0 for the 7 modes."""
        lam = kk_spectrum(PHI**2, PHI**(-2), self.NLEV)
        m2 = sorted(4 * mpsin(k * pi / (4 * (self.N_AR + 1)))**2 / LN_PHI**2
                    for k in range(1, self.NLEV + 1))
        assert all(v < 0 for v in lam)
        assert all(v > 0 for v in m2)
        assert abs(m2[0] - 4 * mpsin(pi / 16)**2 / LN_PHI**2) < mpf('1e-30')

    def test_interior_row_sum(self):
        """Interior row sum = 1/ln^2 phi (the numerator is 1)."""
        assert abs(PHI**2 + PHI**(-2) - 2 - 1) < mpf('1e-20')


class TestKKNumerator:
    """eq:kk-numerator: the numerator is (n-2) with n = phi^2 + phi^{-2} = 3."""

    def test_numerator_value(self):
        import sympy as sp
        phi = (1 + sp.sqrt(5)) / 2
        n = phi**2 + phi**(-2)
        assert sp.simplify(n - 3) == 0
        assert sp.simplify(n - 2 - 1) == 0

    def test_base_of_arity(self):
        """b_n = sqrt((n+sqrt(n^2-4))/2), and at n=3 is EXACTLY phi."""
        def b_n(n):
            return sqrt((mpf(n) + sqrt(mpf(n)**2 - 4)) / 2)
        # Compute phi at current precision (not at import time)
        phi_curr = (1 + sqrt(mpf(5))) / 2
        assert abs(b_n(3) - phi_curr) < mpf('1e-20')
        for n in range(3, 9):
            assert abs(b_n(n)**2 + b_n(n)**(-2) - n) < mpf('1e-20')


class TestKKNegativeControls:
    """Non-reciprocal jumps give modes with m^2 < 0."""

    def test_nonreciprocal_gives_tachyons(self):
        for u, d in [(PHI**2, PHI**(-1)), (PHI**3, PHI**(-1)), (mpf(4), mpf(1))]:
            assert max(kk_spectrum(u, d, 7)) > 0  # at least one positive eigenvalue

    def test_wrong_base_gives_wrong_numerator(self):
        """Base 2 gives 9/4, base 3 gives 64/9 — only phi gives 1."""
        assert abs(mpf(2)**2 + mpf(2)**(-2) - 2 - mpf(9)/4) < mpf('1e-30')
        assert abs(mpf(3)**2 + mpf(3)**(-2) - 2 - mpf(64)/9) < mpf('1e-30')
        assert abs(mpf(2)**2 + mpf(2)**(-2) - 2 - 1) > mpf('1')


class TestKKBFViolation:
    """Every arity violates BF; n=3 is the LEAST violator."""

    def test_all_violate(self):
        for n in range(3, 9):
            assert -(mpf(n) - 2) / log(PHI)**2 < -4

    def test_least_violator(self):
        """n=3 gives the smallest (closest to 0) violation."""
        vals = [-(mpf(n) - 2) / log(PHI)**2 for n in range(3, 9)]
        assert max(vals) == -(mpf(3) - 2) / log(PHI)**2
