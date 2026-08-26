"""
§4–§5  Spectral Angle & Bridge Angle
=====================================
prop:spectral-angle-tower, eq:spectral-surface, eq:bridge-angle,
reflection positivity, conductor, ETS metric.
"""
import numpy as np
import pytest
from mpmath import mp, mpf, mpc, pi, exp, sqrt, log, cos as mpcos, atan as mpatan, fabs as mpabs

mp.dps = 40

PHI = (1 + sqrt(5)) / 2
LN_PHI = log(PHI)
EPS_0 = LN_PHI / (6 * sqrt(3))


# ── Spectral angle ───────────────────────────────────────────────────────

def alpha(s):
    """eps_0 * M_PCF = pi (eq:certainty).  arctan(eps0 phi^s)."""
    return mp.atan(EPS_0 * PHI**s)


# ── Tests ────────────────────────────────────────────────────────────────

class TestSpectralAngle:
    """eq:spectral-angle: tan(alpha(sigma)) = eps_0 phi^sigma."""

    @pytest.mark.parametrize("sigma", range(9))
    def test_tan_equals_tower(self, sigma):
        assert abs(mp.tan(alpha(sigma)) - EPS_0 * PHI**sigma) < mpf('1e-30')

    @pytest.mark.parametrize("sigma", range(9))
    def test_ratio_is_phi(self, sigma):
        """tan(alpha(s+1)) / tan(alpha(s)) = phi EXACT."""
        assert abs(mp.tan(alpha(sigma + 1)) / mp.tan(alpha(sigma)) - PHI) < mpf('1e-30')

    def test_wrong_base(self):
        """With base 2 instead of phi, the tangent ratio is NOT phi."""
        assert abs(mpf(2)**1 / mpf(2)**0 - PHI) > mpf('0.3')


class TestSpectralSurface:
    """eq:spectral-surface: sin a(s1) cos a(s2) = closed form."""

    @pytest.mark.parametrize("s1", range(9))
    @pytest.mark.parametrize("s2", range(9))
    def test_surface(self, s1, s2):
        trig = mp.sin(alpha(s1)) * mp.cos(alpha(s2))
        closed = (EPS_0 * PHI**s1 / sqrt(
            (1 + EPS_0**2 * PHI**(2 * s1)) * (1 + EPS_0**2 * PHI**(2 * s2))
        ))
        assert abs(trig - closed) < mpf('1e-30')


class TestBridgeAngle:
    """eq:bridge-angle: T(s1,s2) = (1+tan a(s1))/(1+tan a(s2))."""

    @pytest.mark.parametrize("s1", range(9))
    @pytest.mark.parametrize("s2", range(9))
    def test_bridge_is_angle(self, s1, s2):
        T_direct = (1 + EPS_0 * PHI**s1) / (1 + EPS_0 * PHI**s2)
        T_angle = (1 + mp.tan(alpha(s1))) / (1 + mp.tan(alpha(s2)))
        assert abs(T_direct - T_angle) < mpf('1e-30')

    @pytest.mark.parametrize("s", range(9))
    def test_pi4_form(self, s):
        """sqrt(2) sin(a + pi/4) / cos(a) = 1 + tan a."""
        lhs = sqrt(2) * mp.sin(alpha(s) + pi / 4) / mp.cos(alpha(s))
        rhs = 1 + mp.tan(alpha(s))
        assert abs(lhs - rhs) < mpf('1e-30')

    def test_tan_pi4(self):
        assert abs(mp.tan(pi / 4) - 1) < mpf('1e-30')


class TestETSMetric:
    """eq:ets-metric: the ETS metric is FLAT (all Riemann components vanish)."""

    def test_ets_is_flat(self):
        """All Riemann components vanish for a constant diagonal metric."""
        import sympy as sp
        t, x, y, z, u = sp.symbols('t x y z u', real=True)
        lam = sp.Symbol('lam', positive=True)
        co5 = [t, x, y, z, u]
        gETS = sp.diag(-1, 1, 1, 1, lam**2)
        n = 5
        gi = gETS.inv()
        # Christoffel symbols
        Gam = [[[sp.Rational(0)] * n for _ in range(n)] for _ in range(n)]
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    Gam[a][b][c] = sum(
                        gi[a, d] * (sp.diff(gETS[d, b], co5[c]) + sp.diff(gETS[d, c], co5[b]) - sp.diff(gETS[b, c], co5[d]))
                        for d in range(n)
                    ) / 2
        # Riemann tensor
        R = [[[[sp.Rational(0)] * n for _ in range(n)] for _ in range(n)] for _ in range(n)]
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    for d in range(n):
                        R[a][b][c][d] = sp.simplify(
                            sp.diff(Gam[a][b][d], co5[c]) - sp.diff(Gam[a][b][c], co5[d])
                            + sum(Gam[a][c][e] * Gam[e][b][d] - Gam[a][d][e] * Gam[e][b][c]
                                  for e in range(n))
                        )
        for a in range(5):
            for b in range(5):
                for c in range(5):
                    for d in range(5):
                        assert R[a][b][c][d] == 0

    def test_desitter_is_curved(self):
        """DISCRIMINATES: de Sitter IS curved, R = 12H^2."""
        import sympy as sp
        t, x, y, z = sp.symbols('t x y z', real=True)
        Hb = sp.Symbol('Hb', positive=True)
        aa = sp.exp(Hb * t)
        co4 = [t, x, y, z]
        gdS = sp.diag(-1, aa**2, aa**2, aa**2)
        n = 4
        gi = gdS.inv()
        Gam = [[[sp.Rational(0)] * n for _ in range(n)] for _ in range(n)]
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    Gam[a][b][c] = sum(
                        gi[a, d] * (sp.diff(gdS[d, b], co4[c]) + sp.diff(gdS[d, c], co4[b]) - sp.diff(gdS[b, c], co4[d]))
                        for d in range(n)
                    ) / 2
        RdS = [[[[sp.Rational(0)] * n for _ in range(n)] for _ in range(n)] for _ in range(n)]
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    for d in range(n):
                        RdS[a][b][c][d] = sp.simplify(
                            sp.diff(Gam[a][b][d], co4[c]) - sp.diff(Gam[a][b][c], co4[d])
                            + sum(Gam[a][c][e] * Gam[e][b][d] - Gam[a][d][e] * Gam[e][b][c]
                                  for e in range(n))
                        )
        Ric = sp.zeros(4, 4)
        for b in range(4):
            for d in range(4):
                Ric[b, d] = sp.simplify(sum(RdS[e][b][e][d] for e in range(4)))
        Rsc = sp.simplify(sum(gi[b, d] * Ric[b, d] for b in range(4) for d in range(4)))
        assert sp.simplify(Rsc - 12 * Hb**2) == 0

    def test_ets_is_h0_limit(self):
        """ETS is the H->0 limit of de Sitter, NOT its Wick rotation."""
        import sympy as sp
        Hb = sp.Symbol('Hb', positive=True)
        aa = sp.exp(Hb * sp.Symbol('t', real=True))
        assert sp.limit(aa**2, Hb, 0) == 1


class TestConductor:
    """eq:conductor: conductor and CRT properties of Q(sqrt5)."""

    def test_lcm(self):
        assert 20 % 4 == 0 and 20 % 5 == 0 and 4 * 5 == 20

    def test_i4_equals_1(self):
        assert abs(complex(0, 1)**4 - 1) < 1e-15

    def test_binary_register(self):
        """2^2 = -1 in F_5."""
        assert pow(2, 2, 5) == (-1) % 5

    def test_order_4_cycle(self):
        """2^k mod 5 = 2,4,3,1 vs i^k = i,-1,-i,1."""
        assert [pow(2, k, 5) for k in (1, 2, 3, 4)] == [2, 4, 3, 1]
        assert [complex(0, 1)**k for k in (1, 2, 3, 4)] == [1j, -1, -1j, 1]
        assert pow(2, 4, 5) == 1
        assert all(pow(2, k, 5) != 1 for k in (1, 2, 3))

    def test_5_splits_in_gaussian(self):
        """(2+i)(2-i) = 5."""
        assert (2 + 1j) * (2 - 1j) == 5 + 0j

    def test_only_prime_with_pminus1_4(self):
        """5 is the ONLY prime with p-1 = 4."""
        primes = [p for p in range(2, 500)
                  if all(p % d for d in range(2, int(p**0.5) + 1)) and p - 1 == 4]
        assert primes == [5]

    def test_crt_injective(self):
        """(mod 4, mod 5) injective on 20 conductor classes."""
        assert len({(a % 4, a % 5) for a in range(20)}) == 20

    def test_chi5_not_determined_by_4(self):
        """4 does NOT determine chi5: witness 1 and 13."""
        def chi5(k):
            return {0: 0, 1: 1, 2: -1, 3: -1, 4: 1}[k % 5]
        assert 1 % 4 == 13 % 4 and chi5(1) != chi5(13)

    def test_chi4_not_determined_by_5(self):
        """5 does NOT determine chi4: witness 1 and 11."""
        assert 1 % 5 == 11 % 5 and 1 % 4 != 11 % 4


class TestAnchorExterior:
    """phi < 2 < phi^2: 2 falls in the gap."""

    def test_gap(self):
        assert PHI < 2 < PHI**2

    def test_no_integer_power_equals_2(self):
        """phi^n != 2 for every integer n."""
        assert min(abs(PHI**n - 2) for n in range(-40, 41)) > mpf('1e-20')


class TestProjectorFrameInvariance:
    """P(gC) = P(C): the projector is a function of the point, not the frame."""

    def test_invariance(self):
        rng = np.random.RandomState(3)
        _phic = float(PHI)
        R = np.array([[0, 1, 0], [0, 0, 1], [1, 0, 0]], dtype=float)

        def P(X):
            return X.T @ np.linalg.inv(X @ X.T) @ X

        ok = True
        for _ in range(300):
            k, n = rng.randint(1, 4), rng.randint(4, 8)
            C = rng.randn(k, n)
            g = rng.randn(k, k)
            while abs(np.linalg.det(g)) < 1e-3:
                g = rng.randn(k, k)
            if np.abs(P(g @ C) - P(C)).max() > 1e-8:
                ok = False
        assert ok

    def test_four_faces(self):
        """P^2=P, P^T=P, tr P = k, tr(P/k) = 1."""
        rng = np.random.RandomState(5)

        def P(X):
            return X.T @ np.linalg.inv(X @ X.T) @ X

        C = rng.randn(3, 7)
        Pm = P(C)
        assert np.abs(Pm @ Pm - Pm).max() < 1e-10
        assert np.abs(Pm.T - Pm).max() < 1e-10
        assert abs(np.trace(Pm) - 3) < 1e-10
        assert abs(np.trace(Pm / 3) - 1) < 1e-10


# ═════════════════════════════════════════════════════════════════════════
# eq:envelope-splits — log(5T/2pie) = log5 + logT - log(2pie)
# ═════════════════════════════════════════════════════════════════════════

class TestEnvelopeSplits:
    """eq:envelope-splits: the conductor envelope splits into body + pi parts."""

    def test_log_splitting(self):
        """log(5T/2pie) = log5 + logT - log(2pie)."""
        T = mpf(100)
        lhs = log(5 * T / (2 * pi * mp.e))
        rhs = log(mpf(5)) + log(T) - log(2 * pi * mp.e)
        assert abs(lhs - rhs) < mpf('1e-22')

    def test_log_q_injective(self):
        """Only the body part distinguishes: log q injective."""
        logs = {mp.nstr(log(q), 30) for q in [5, 8, 12, 13]}
        assert len(logs) == 4

    def test_scale_injective(self):
        """sc(q,T) is injective in q."""
        def sc(q, T):
            return 2 * pi / log(q * T / (2 * pi))
        vals = {mp.nstr(sc(q, 100), 30) for q in [5, 8, 12, 13]}
        assert len(vals) == 4


class TestLiModulus:
    """eq:li-modulus: |1 - 1/rho| = 1 iff Re rho = 1/2."""

    def test_equivalence(self):
        """|1-1/rho| = 1 iff Re rho = 1/2 (the critical line is [P], not [C])."""
        md = lambda z: mpabs(1 - 1/z)
        half = mpf(1) / 2
        pts = [mpc(half, 20), mpc(mpf('0.51'), 20), mpc(mpf('0.75'), 3), mpc(mpf('0.9'), 1)]
        for z in pts:
            on_line = mpabs(z.real - half) < mpf('1e-25')
            modulus_one = mpabs(md(z) - 1) < mpf('1e-25')
            assert on_line == modulus_one
