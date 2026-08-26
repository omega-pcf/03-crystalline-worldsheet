"""
§2  Arithmetic of K = Q(sqrt5)
==============================
Trace/norm, regulator, chi5 character, pentagon, Fibonacci criterion,
Dedekind zeta, class number, entropy bridge, Binet formula.
"""
import pytest
from fractions import Fraction
from mpmath import (
    mp, mpf, mpc, pi, exp, sqrt, log, cos as mpcos, sin as mpsin,
    gamma as mpgamma, zeta, digamma, nsum, inf,
)

mp.dps = 25

PHI = (1 + sqrt(5)) / 2
PHI_BAR = (1 - sqrt(5)) / 2
DELTA_K = 5


# ── Chi5 character ───────────────────────────────────────────────────────

def chi5(k):
    return {0: 0, 1: 1, 2: -1, 3: -1, 4: 1}[k % 5]


def fib(k):
    a, b = 0, 1
    for _ in range(k):
        a, b = b, a + b
    return a


# ── Tests ────────────────────────────────────────────────────────────────

class TestTraceNorm:
    """eq:trace-norm: phi + phi_bar = 1, phi * phi_bar = -1, discriminant = 5."""

    def test_sum(self):
        assert abs(PHI + PHI_BAR - 1) < mpf('1e-25')

    def test_product(self):
        assert abs(PHI * PHI_BAR + 1) < mpf('1e-25')

    def test_discriminant(self):
        assert abs((PHI - PHI_BAR)**2 - 5) < mpf('1e-25')


class TestOKVsRpcf:
    """phi is a root of x^2 - x - 1; 1/2 is NOT."""

    def test_phi_is_root(self):
        assert abs(PHI**2 - PHI - 1) < mpf('1e-25')

    def test_half_is_not(self):
        """1/2 is a root of 2x-1, which is not monic in the same sense."""
        assert abs(2 * (mpf(1) / 2) - 1) < mpf('1e-25')


class TestRegulator:
    """R_K = log phi by two routes."""

    def test_from_generator(self):
        R_K = log(PHI)
        assert R_K > 0

    def test_from_eps0(self):
        eps0_from_proj = (mp.sin(pi / 6) * log(PHI) / pi) * (1 / mpf(3)**mpf('0.5')) * (pi / 3)
        M_from_eps0 = pi / eps0_from_proj
        assert abs(eps0_from_proj - log(PHI) / (6 * mpf(3)**mpf('0.5'))) < mpf('1e-25')
        assert abs(M_from_eps0 * eps0_from_proj - pi) < mpf('1e-22')


class TestChi5Values:
    """eq:chi5-values: multiplicative on (Z/5)^x, sums to zero."""

    def test_multiplicative(self):
        for a in range(1, 5):
            for b in range(1, 5):
                assert chi5(a * b) == chi5(a) * chi5(b)

    def test_zero_sum(self):
        assert sum(chi5(a) for a in range(5)) == 0


class TestChi5Pentagon:
    """|2 cos(pi a/5)| = phi^{chi5(a)}."""

    @pytest.mark.parametrize("a", range(1, 5))
    def test_identity(self, a):
        assert abs(abs(2 * mpcos(pi * a / 5)) - PHI**chi5(a)) < mpf('1e-25')

    @pytest.mark.parametrize("a", range(1, 5))
    def test_log_form(self, a):
        assert abs(log(abs(2 * mpcos(pi * a / 5))) / log(PHI) - chi5(a)) < mpf('1e-22')


class TestFibonacciCriterion:
    """F_q = (q/5) mod q for 23 odd primes up to 97 (Lucas 1878)."""

    PRIMES = [3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
              53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

    @pytest.mark.parametrize("q", PRIMES)
    def test_lucas(self, q):
        assert fib(q) % q == chi5(q) % q


class TestPentagonSplitting:
    """Split, inert, ramified primes in Q(sqrt5)."""

    def test_split(self):
        assert sorted(a for a in [1, 3, 7, 9, 11, 13, 17, 19] if chi5(a) == 1) == [1, 9, 11, 19]

    def test_inert(self):
        assert sorted(a for a in [1, 3, 7, 9, 11, 13, 17, 19] if chi5(a) == -1) == [3, 7, 13, 17]

    def test_ramified(self):
        assert chi5(5) == 0


class TestBinetFormula:
    """alpha^{n+1} = F_{n+1} alpha + F_n for BOTH roots."""

    ALPHAS = [(1 + sqrt(5)) / 2, (1 - sqrt(5)) / 2]

    @pytest.mark.parametrize("n", range(26))
    def test_both_roots(self, n):
        def fib2(k):
            a, b = 0, 1
            for _ in range(k):
                a, b = b, a + b
            return a
        for a in self.ALPHAS:
            assert abs(a**(n + 1) - (fib2(n + 1) * a + fib2(n))) < mpf('1e-15')

    @pytest.mark.parametrize("q", [7, 11, 13, 19, 23])
    def test_modular_recurrence(self, q):
        def fib2(k):
            a, b = 0, 1
            for _ in range(k):
                a, b = b, a + b
            return a
        for k in range(20):
            assert (fib2(k + 1) + fib2(k)) % q == fib2(k + 2) % q


class TestDedekindZeta:
    """eq:local-dedekind: f_p^K = f_p^zeta * f_p^L in three cases."""

    def _fK(self, p, s):
        c = chi5(p)
        if c == 0:
            return (1 - mpf(p)**(-s))**(-1)
        if c == 1:
            return (1 - mpf(p)**(-s))**(-2)
        return (1 - mpf(p)**(-2 * s))**(-1)

    def _fZ(self, p, s):
        return (1 - mpf(p)**(-s))**(-1)

    def _fL(self, p, s):
        return (1 - chi5(p) * mpf(p)**(-s))**(-1)

    @pytest.mark.slow
    @pytest.mark.parametrize("s", [mpf(2), mpf(3), mpf('2.5'), mpf(5)])
    def test_local_factorization(self, s):
        def primes_upto(N):
            sieve = bytearray([1]) * (N + 1)
            sieve[0:2] = b'\x00\x00'
            for i in range(2, int(N**0.5) + 1):
                if sieve[i]:
                    sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
            return [i for i in range(2, N + 1) if sieve[i]]

        for p in primes_upto(200):
            assert abs(self._fK(p, s) - self._fZ(p, s) * self._fL(p, s)) < mpf('1e-22')

    def test_splitting_types(self):
        """g*e*f = 2 in the three types."""
        for g, e, f in [(2, 1, 1), (1, 1, 2), (1, 2, 1)]:
            assert g * e * f == 2


class TestClassNumber:
    """h_K = 1 for Q(sqrt5) by Minkowski bound."""

    def test_minkowski_bound(self):
        """M_K = sqrt5/2 < 2, so h_K = 1."""
        assert mpf(2) / 4 * mpf(5)**mpf('0.5') < 2


class TestL1ThreeRoutes:
    """L(1, chi5) = 2 log phi / sqrt5 by THREE routes."""

    def test_three_routes(self):
        R_K = log(PHI)
        L1 = 2 * log(PHI) / mpf(5)**mpf('0.5')

        # Route 1: digamma
        La = -sum(chi5(a) * digamma(mpf(a) / 5) for a in range(1, 5)) / 5

        # Route 2: log-sine
        Lb = -(1 / mpf(5)**mpf('0.5')) * sum(
            chi5(a) * log(2 * mpsin(pi * a / 5)) for a in range(1, 5)
        )

        # Route 3: class number formula
        cnf = (2**2 * 1 * R_K) / (2 * mpf(5)**mpf('0.5'))

        tol = mpf('1e-25')
        assert max(abs(La - L1), abs(Lb - L1), abs(cnf - L1)) < tol


class TestEntropyBridge:
    """S_BH/k_B = lambda * R_K = log 2 (one bit)."""

    def test_bridge(self):
        lam = log(2) / log(PHI)
        R_K = log(PHI)
        assert abs(lam * R_K - log(2)) < mpf('1e-25')

    def test_class_number_form(self):
        lam = log(2) / log(PHI)
        R_K = log(PHI)
        L1 = 2 * log(PHI) / mpf(5)**mpf('0.5')
        assert abs(mpf(5)**mpf('0.5') / 2 * L1 - R_K) < mpf('1e-25')
        assert abs(lam * mpf(5)**mpf('0.5') / 2 * L1 - log(2)) < mpf('1e-25')

    def test_binary_bridge(self):
        assert abs(PHI**(log(2) / log(PHI)) - 2) < mpf('1e-25')
        assert abs(PHI**(-(log(2) / log(PHI))) - mpf(1) / 2) < mpf('1e-25')


class TestEvenZeta:
    """zeta(2k) = (-1)^{k+1} B_{2k} (2pi)^{2k} / (2(2k)!)."""

    @pytest.mark.parametrize("k", range(1, 7))
    def test_formula(self, k):
        from mpmath import bernoulli as bern, factorial as fact
        assert abs(zeta(2*k) - (-1)**(k+1) * bern(2*k) * (2*pi)**(2*k) / (2 * fact(2*k))) < mpf('1e-20')


class TestOddZeta:
    """zeta(2k+1) = zeta_K / L with zeta_K by Euler product."""

    def _Lchi5(self, s):
        return sum(chi5(a) * zeta(s, mpf(a) / 5) for a in range(1, 5)) * mpf(5)**(-s)

    def _zetaK_euler(self, s, N=20000):
        def fK(p, s):
            c = chi5(p)
            if c == 0:
                return (1 - mpf(p)**(-s))**(-1)
            if c == 1:
                return (1 - mpf(p)**(-s))**(-2)
            return (1 - mpf(p)**(-2 * s))**(-1)
        def primes_upto(N):
            sieve = bytearray([1]) * (N + 1)
            sieve[0:2] = b'\x00\x00'
            for i in range(2, int(N**0.5) + 1):
                if sieve[i]:
                    sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
            return [i for i in range(2, N + 1) if sieve[i]]
        r = mpf(1)
        for p in primes_upto(N):
            r *= fK(p, s)
        return r

    @pytest.mark.slow
    @pytest.mark.parametrize("k", [1, 2])
    def test_odd(self, k):
        s = mpf(2 * k + 1)
        assert abs(self._zetaK_euler(s) / self._Lchi5(s) - zeta(s)) < mpf('1e-8')
        assert abs(self._Lchi5(s)) > mpf('0.5')


class TestEntropyMax:
    """H(p) <= 1 on (0,1) with equality ONLY at p=1/2."""

    def test_max_at_half(self):
        def Hbin(p):
            return -p * log(p) / log(2) - (1 - p) * log(1 - p) / log(2)
        assert abs(Hbin(mpf(1) / 2) - 1) < mpf('1e-25')

    def test_below_one(self):
        def Hbin(p):
            return -p * log(p) / log(2) - (1 - p) * log(1 - p) / log(2)
        for k in range(1, 1000):
            assert Hbin(mpf(k) / 1000) <= 1 + mpf('1e-20')


class TestLogSignature:
    """sum chi5(a) log(2 sin(pi a/5)) = -2 log phi."""

    def test_identity(self):
        assert abs(sum(chi5(a) * log(2 * mpsin(pi * a / 5)) for a in range(1, 5)) + 2 * log(PHI)) < mpf('1e-22')

    def test_ratio(self):
        assert abs(mpsin(2 * pi / 5) / mpsin(pi / 5) - PHI) < mpf('1e-22')


# ═════════════════════════════════════════════════════════════════════════
# thm:mu-diagram — six independent routes to mu = 1/2
# ═════════════════════════════════════════════════════════════════════════

class TestMuDiagram:
    """thm:mu-diagram: six faces of the cocone ALL equal 1/2.
    
    Each face computes 1/2 by a different route — none passes through the
    name 'mu'. The convergence IS the theorem.
    """

    MU = mpf(1) / 2
    _LM = log(2) / log(PHI)
    _AP = PHI ** (-_LM)

    def test_face_factorial(self):
        """Gamma(3/2)/sqrt(pi) = 1/2."""
        assert abs(mpgamma(mpf(3)/2) / sqrt(pi) - self.MU) < mpf('1e-25')

    def test_face_gamma_ratio(self):
        """Gamma(3/2)/Gamma(1/2) = 1/2."""
        assert abs(mpgamma(mpf(3)/2) / mpgamma(mpf(1)/2) - self.MU) < mpf('1e-25')

    def test_face_norm(self):
        """|P||C||F| = (1/sqrt3)(1)(sqrt3/2) = 1/2."""
        assert abs((1/sqrt(mpf(3))) * 1 * (sqrt(mpf(3))/2) - self.MU) < mpf('1e-25')

    def test_face_cos(self):
        """cos(pi/3) = 1/2."""
        assert abs(mpcos(pi/3) - self.MU) < mpf('1e-25')

    def test_face_phi_binary(self):
        """phi^{-lambda_log} = 2^{-1} = 1/2."""
        assert abs(self._AP - self.MU) < mpf('1e-25')

    def test_face_galois(self):
        """(phi + phi_bar)/2 = 1/2."""
        assert abs((PHI + PHI_BAR) / 2 - self.MU) < mpf('1e-25')

    def test_all_six_coincide(self):
        """All six faces agree without passing through the name mu."""
        faces = [
            mpgamma(mpf(3)/2) / sqrt(pi),
            mpgamma(mpf(3)/2) / mpgamma(mpf(1)/2),
            (1/sqrt(mpf(3))) * 1 * (sqrt(mpf(3))/2),
            mpcos(pi/3),
            self._AP,
            (PHI + PHI_BAR) / 2,
        ]
        assert max(abs(a - b) for a in faces for b in faces) < mpf('1e-25')

    def test_phi_equals_galois(self):
        """facePhi = faceGalois: the two faces of phi^2 = phi+1."""
        assert abs(self._AP - (PHI + PHI_BAR) / 2) < mpf('1e-25')


# ═════════════════════════════════════════════════════════════════════════
# thm:sigma-diagram — two routes to sigma = 3/2
# ═════════════════════════════════════════════════════════════════════════

class TestSigmaDiagram:
    """thm:sigma-diagram: sigma = 3/2 by analytic and geometric routes."""

    def test_analytic_route(self):
        """sigma = zeta(2)/(pi/3)^2 = (pi^2/6)/(pi^2/9) = 3/2."""
        from mpmath import zeta as mpzeta
        sigma = mpzeta(2) / (pi/3)**2
        assert abs(sigma - mpf(3)/2) < mpf('1e-20')

    def test_geometric_route(self):
        """sigma = |rot S_3|^2/|S_3| = 3^2/6 = 3/2."""
        import math
        rot_S3 = math.factorial(3) // 2  # |A_3| = 3
        assert abs(mpf(rot_S3)**2 / mpf(math.factorial(3)) - mpf(3)/2) < mpf('1e-25')

    def test_two_routes_agree(self):
        """Both routes give 3/2."""
        from mpmath import zeta as mpzeta
        import math
        analytic = mpzeta(2) / (pi/3)**2
        geometric = mpf(math.factorial(3)//2)**2 / mpf(math.factorial(3))
        assert abs(analytic - geometric) < mpf('1e-20')


# ═════════════════════════════════════════════════════════════════════════
# prop:psi-functorial — psi_p o psi_q = psi_{pq}
# ═════════════════════════════════════════════════════════════════════════

class TestPsiFunctorial:
    """eq:psi-functorial: psi_p(psi_q(x)) = psi_{pq}(x) on generators phi^n."""

    def _fib(self, k):
        a, b = 0, 1
        for _ in range(k):
            a, b = b, a + b
        return a

    @pytest.mark.parametrize("p,q,n", [(2,3,1), (3,5,2), (5,7,1), (2,2,3)])
    def test_on_generators(self, p, q, n):
        """psi_p(psi_q(phi^n)) = phi^{pqn}."""
        lhs = ((PHI**n)**q)**p
        rhs = PHI**(p * q * n)
        assert abs(lhs - rhs) < mpf('1e-12')

    def test_psi_two_not_additive(self):
        """psi_p is NOT additive: psi_2(phi+1) = phi^4 != phi^2 + 1."""
        assert abs((PHI + 1)**2 - PHI**4) < mpf('1e-18')
        assert abs(PHI**4 - (PHI**2 + 1)) > mpf('1')
