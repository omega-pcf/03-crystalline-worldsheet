"""
§3  Tower Modes & Bridge Cocycle
=================================
Tower mode counts and their golden growth (eq:tower-modes, cor:golden-growth,
thm:fib-min), bridge cocycle composition/inverse (eq:bridge), KK golden
identity, and the Regge residue behind eq:veneziano (degree n-1, spin <= n-1).
"""
import numpy as np
import pytest

from cw6.constants import PHI, EPS_0, M_PCF, ARITY, nmodes, bridge_T


class TestTowerModes:
    """eq:tower-modes: N_modes(sigma) = floor(pi phi^sigma)."""

    NMODES_SEQ = [3, 5, 8, 13, 21, 34, 56]

    @pytest.mark.parametrize("sigma,expected", list(enumerate(NMODES_SEQ)))
    def test_individual(self, sigma, expected):
        assert nmodes(sigma) == expected

    def test_six_not_fib(self):
        """thm:fib-min: N_modes(6) = 56 while the Fibonacci value is 55.

        03-derivations: the pi-scaled staircase equals the Fibonacci values for
        sigma <= 5 and departs at sigma = 6, where 56 != 55.
        """
        def fib(k):
            a, b = 0, 1
            for _ in range(k):
                a, b = b, a + b
            return a
        assert nmodes(6) == 56
        assert fib(10) == 55
        assert nmodes(6) != fib(10)
        assert [nmodes(s) for s in range(6)] == [fib(s + 4) for s in range(6)]

    def test_ratio_is_phi(self):
        """cor:golden-growth: the tower grows by phi per level.

        Checked on the mode counts of eq:tower-modes themselves (the
        manuscript's N_modes), not on the un-floored formula: each step of the
        staircase is phi within the rounding the floor introduces.
        """
        ratios = [nmodes(s + 1) / nmodes(s) for s in range(6)]
        assert max(abs(r - PHI) for r in ratios) < 0.05

    def test_cumulative(self):
        """Cumulative mode counts: [3, 8, 16, 29, 50, 84, 140]."""
        cum = [sum(self.NMODES_SEQ[: k + 1]) for k in range(7)]
        assert cum == [3, 8, 16, 29, 50, 84, 140]


class TestBridgeCocycle:
    """eq:bridge: T(a,b)T(b,c) = T(a,c), T(a,b)T(b,a) = 1."""

    @pytest.mark.parametrize("a,b,c", [(1, 4, 7), (0, 3, 6), (2, 5, 8)])
    def test_composition(self, a, b, c):
        assert abs(bridge_T(a, b) * bridge_T(b, c) - bridge_T(a, c)) < 1e-12

    @pytest.mark.parametrize("a,b", [(2, 5), (1, 3), (0, 6)])
    def test_inverse(self, a, b):
        assert abs(bridge_T(a, b) * bridge_T(b, a) - 1) < 1e-12


class TestKKGoldenIdentity:
    """KK identity: phi^2 + phi^{-2} - 2 = 1."""

    def test_identity(self):
        assert abs(PHI**2 + PHI**-2 - 2 - 1) < 1e-12


class TestReggeSpin:
    """03-derivations (eq:veneziano): the residues of the Veneziano amplitude at
    alpha' s = n are Regge polynomials of degree n-1 (carrying spin <= n-1),
    nonzero at every level.

    The residue is computed numerically, by contour integration of the
    amplitude the manuscript prints,
        A4 = Gamma(-alpha's) Gamma(-alpha'u) / Gamma(1 - alpha'(s+u)),
    with s + t + u = 0, i.e. A(x, tau) = Gamma(-x) Gamma(x+tau)/Gamma(1+tau)
    at x = alpha's and tau = alpha't.  The degree of a polynomial is read off
    from finite differences of its values, so nothing about the answer is
    assumed.
    """

    MPS_DPS = 25

    @staticmethod
    def _residue(n, tau):
        from mpmath import mp, mpf, gamma, quad, pi, exp
        old = mp.dps
        mp.dps = TestReggeSpin.MPS_DPS
        r = mpf('0.1')                       # no other pole within the contour
        A = lambda x: gamma(-x) * gamma(x + tau) / gamma(1 + tau)
        f = lambda th: A(n + r * exp(1j * th)) * r * exp(1j * th)
        val = quad(f, [0, 2 * pi]) / (2 * pi)
        mp.dps = old
        return val

    @classmethod
    def _values(cls, n, count):
        from mpmath import mpf
        return [cls._residue(n, mpf(k)) for k in range(count)]

    @classmethod
    def _difference(cls, vals, order):
        v = list(vals)
        for _ in range(order):
            v = [v[i + 1] - v[i] for i in range(len(v) - 1)]
        return v

    @pytest.mark.parametrize("n", [1, 2, 3, 4, 5])
    def test_residue_degree_is_n_minus_1(self, n):
        """degree = n-1: the n-th difference vanishes, the (n-1)-th does not."""
        from mpmath import mpf
        vals = self._values(n, n + 2)                 # n+2 sample points
        n_th = self._difference(vals, n)
        scale = max(abs(v) for v in vals)
        assert max(abs(v) for v in n_th) < mpf('1e-12') * scale
        nm1_th = self._difference(vals, n - 1)
        assert min(abs(v) for v in nm1_th) > mpf('1e-6')

    @pytest.mark.parametrize("n", [1, 2, 3, 4, 5])
    def test_residue_nonzero_at_every_level(self, n):
        """Nonzero at every level: every integer level is populated."""
        from mpmath import mpf
        assert abs(self._residue(n, mpf(7))) > mpf('1e-6')

    def test_j2_requires_n3(self):
        """Consequence of spin <= n-1: J=2 needs n >= 3, not n = 2."""
        from mpmath import mpf
        vals2 = self._values(2, 4)
        vals3 = self._values(3, 5)
        # level 2: second difference must vanish -> degree <= 1 (spin 0,1)
        assert max(abs(v) for v in self._difference(vals2, 2)) < mpf('1e-12') * max(abs(v) for v in vals2)
        # level 3: second difference must NOT vanish -> degree = 2 (spin 0,1,2)
        assert min(abs(v) for v in self._difference(vals3, 2)) > mpf('1e-6')
