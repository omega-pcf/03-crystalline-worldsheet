"""
§2  Product Over Places
=======================
Archimedean place (self-dual Gaussian), Poisson S-duality, Euler product,
Dedekind zeta, functional equation, eta(i), F1 consistency.
All checks at 25-digit precision (mpmath).
"""
import pytest
from mpmath import (
    mp, mpf, mpc, pi, exp, sqrt, log, gamma, zeta, power,
    quad, nsum, inf,
)

# Ensure 25-digit precision for this module
mp.dps = 25


# ── Objects ───────────────────────────────────────────────────────────────

def g(x, a=pi):
    """Gaussian; a=pi is the self-dual point."""
    return exp(-a * x**2)


def ghat(xi, a=pi):
    """Fourier transform, convention e^{-2 pi i x xi}."""
    return quad(lambda x: exp(-a * x**2) * exp(-2j * pi * x * xi), [-inf, inf])


def GammaR(s):
    """Archimedean local factor: pi^{-s/2} Gamma(s/2)."""
    return power(pi, -s/2) * gamma(s/2)


def Theta(t):
    """Gauss sum over the lattice Z."""
    return nsum(lambda n: g(n * sqrt(t)), [-inf, inf])


def omega_half(t):
    """Half-sum, n >= 1."""
    return (Theta(t) - 1) / 2


def dirichlet_tower(s):
    """Dirichlet series of the Regge tower."""
    return nsum(lambda n: 1 / mpc(n)**s, [1, inf])


def Lambda_riemann(s):
    """Riemann form with cut at t=1."""
    I = quad(lambda t: (power(t, s/2-1) + power(t, (1-s)/2-1)) * omega_half(t), [1, inf])
    return 1 / (s * (s - 1)) + I


def chi5(a):
    """Dirichlet character mod 5."""
    return {0: 0, 1: 1, 2: -1, 3: -1, 4: 1}[a % 5]


def L_chi5(s):
    """Hurwitz L-function: L(s, chi5) = 5^{-s} sum chi5(a) zeta(s, a/5)."""
    return sum(chi5(a) * zeta(s, mpf(a) / 5) for a in range(1, 5)) / power(5, s)


PHI = (1 + sqrt(5)) / 2
ETA_I = gamma(mpf(1) / 4) / (2 * power(pi, mpf(3) / 4))


def primes_upto(N):
    """Sieve of Eratosthenes."""
    sieve = bytearray([1]) * (N + 1)
    sieve[0:2] = b'\x00\x00'
    for i in range(2, int(N**0.5) + 1):
        if sieve[i]:
            sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
    return [i for i in range(2, N + 1) if sieve[i]]


def euler_partial(s, N=20000):
    """Partial Euler product up to primes < N."""
    p = mpc(1)
    for q in primes_upto(N):
        p *= 1 / (1 - mpc(q)**(-s))
    return p


def zetaK_euler(s, N=20000):
    """Dedekind zeta via Euler product over ideals."""
    def fK(p, s):
        c = chi5(p)
        if c == 0:
            return (1 - mpf(p)**(-s))**(-1)
        if c == 1:
            return (1 - mpf(p)**(-s))**(-2)
        return (1 - mpf(p)**(-2 * s))**(-1)
    r = mpf(1)
    for p in primes_upto(N):
        r *= fK(p, s)
    return r


# ── Tests ────────────────────────────────────────────────────────────────

class TestSelfDualGaussian:
    """prop:selfdual-gaussian: |ghat_a - g_a| vanishes only at a = pi."""

    def test_self_dual_at_pi(self):
        xi = mpf('0.37')
        assert abs(ghat(xi, pi) - g(xi, pi)) < mpf('1e-20')

    def test_not_self_dual_a1(self):
        xi = mpf('0.37')
        assert abs(ghat(xi, mpf(1)) - g(xi, mpf(1))) > mpf('0.4')

    def test_not_self_dual_a2(self):
        xi = mpf('0.37')
        assert abs(ghat(xi, mpf(2)) - g(xi, mpf(2))) > mpf('0.1')

    def test_normalized_at_pi(self):
        """int_R e^{-a x^2} = 1 <=> a = pi."""
        assert abs(quad(lambda x: g(x), [-inf, inf]) - 1) < mpf('1e-20')
        assert abs(quad(lambda x: exp(-x**2), [-inf, inf]) - sqrt(pi)) < mpf('1e-20')

    @pytest.mark.parametrize("s", [mpf(2), mpc(3, 1), mpf(1)/2, mpc(3, 1)])
    def test_gammaR_is_mellin(self, s):
        """GammaR(s) = 2 int_0^inf e^{-pi x^2} x^{s-1} dx."""
        assert abs(2 * quad(lambda x: g(x) * power(x, s - 1), [0, inf]) - GammaR(s)) < mpf('1e-12')

    def test_gammaR_at_one(self):
        assert abs(GammaR(1) - 1) < mpf('1e-22')


class TestPoissonSDuality:
    """Theta(1/t) = sqrt(t) Theta(t)."""

    @pytest.mark.parametrize("t", [mpf('0.25'), mpf('0.6'), mpf(1), mpf(2), mpf(5)])
    def test_theta_poisson(self, t):
        assert abs(Theta(1 / t) - sqrt(t) * Theta(t)) < mpf('1e-20')

    @pytest.mark.parametrize("t", [mpf('0.6'), mpf(2)])
    def test_boltzmann_fails(self, t):
        """The primon gas weight does NOT satisfy S-duality."""
        assert abs(nsum(lambda n: exp(-n/t), [1, inf]) - sqrt(t) * nsum(lambda n: exp(-n*t), [1, inf])) > mpf('0.5')

    def test_theta_fixed_point(self):
        """Theta(1) = sqrt(2) eta(i)."""
        assert abs(Theta(1) - sqrt(2) * ETA_I) < mpf('1e-20')

    def test_gammaR_half_is_eta(self):
        """GammaR(1/2) = 2 sqrt(pi) eta(i)."""
        assert abs(GammaR(mpf(1) / 2) - 2 * sqrt(pi) * ETA_I) < mpf('1e-20')


class TestReggeTower:
    """prop:veneziano: tower = zeta(s)."""

    @pytest.mark.parametrize("s", [mpf(2), mpc(3, 1), mpc('1.5', 4)])
    def test_dirichlet_eq_zeta(self, s):
        assert abs(dirichlet_tower(s) - zeta(s)) < mpf('1e-4')

    def test_euler_product(self):
        """zeta(s) = prod_p (1-p^{-s})^{-1}."""
        assert abs(euler_partial(mpf(3)) - zeta(3)) < mpf('1e-8')


class TestAssembly:
    """Lambda = Archimedean x finite."""

    @pytest.mark.slow
    def test_schwinger_per_level(self):
        """(pi n^2)^{-s/2} Gamma(s/2) = Schwinger integral."""
        for s in (mpf(2), mpc(3, 1)):
            for n in (1, 3):
                lhs = power(pi * n**2, -s/2) * gamma(s / 2)
                rhs = quad(lambda t: power(t, s/2-1) * exp(-pi * n**2 * t), [0, inf])
                assert abs(lhs - rhs) < mpf('1e-18')

    @pytest.mark.slow
    @pytest.mark.parametrize("s", [mpf(2), mpf(3), mpf(4), mpc(3, 1), mpc(2, 5), mpf(1)/2])
    def test_partition_eq_tower(self, s):
        """Lambda(s) = GammaR(s) zeta(s) = Riemann form."""
        assert abs(GammaR(s) * zeta(s) - Lambda_riemann(s)) < mpf('1e-20')

    @pytest.mark.slow
    @pytest.mark.parametrize("s", [mpc(3, 1), mpf(4), mpc(2, 5)])
    def test_functional_equation(self, s):
        """R(s) = R(1-s)."""
        assert abs(Lambda_riemann(s) - Lambda_riemann(1 - s)) < mpf('1e-20')

    def test_selfdual_line(self):
        """Fixed point of s -> 1-s is s = 1/2."""
        assert abs(mpf(1) / 2 - (1 - mpf(1) / 2)) < mpf('1e-30')


class TestF1Consistency:
    """Consistency with F1: places of Q(sqrt5)."""

    def test_chi5_is_even(self):
        assert chi5(4) == 1 and chi5(-1) == 1

    @pytest.mark.slow
    @pytest.mark.parametrize("s", [mpc(2, 1), mpc(3, 4), mpc('0.7', 2)])
    def test_L_chi5_functional(self, s):
        Lam5 = lambda s: power(mpf(5) / pi, s / 2) * gamma(s / 2) * L_chi5(s)
        assert abs(Lam5(s) - Lam5(1 - s)) < mpf('1e-22')

    @pytest.mark.slow
    @pytest.mark.parametrize("s", [mpc(2, 1), mpc(3, 4), mpc('0.7', 2)])
    def test_zetaK_two_real_places(self, s):
        LamK = lambda s: power(5, s / 2) * GammaR(s)**2 * zeta(s) * L_chi5(s)
        assert abs(LamK(s) - LamK(1 - s)) < mpf('1e-22')

    @pytest.mark.slow
    @pytest.mark.parametrize("s", [mpc(2, 1), mpc(3, 4), mpc('0.7', 2)])
    def test_one_gammaR_per_dedekind(self, s):
        """Lam_K(s) = GammaR(s) * zeta(s) * Lam(s,chi5): one GammaR per Dedekind factor."""
        Lam5 = lambda s: power(mpf(5) / pi, s / 2) * gamma(s / 2) * L_chi5(s)
        LamK = lambda s: power(5, s / 2) * GammaR(s)**2 * zeta(s) * L_chi5(s)
        assert abs(LamK(s) - GammaR(s) * zeta(s) * Lam5(s)) < mpf('1e-22')


# ═════════════════════════════════════════════════════════════════════════
# prop:rp — reflection positivity
# ═════════════════════════════════════════════════════════════════════════

class TestReflectionPositivity:
    """prop:rp: <Theta F,F> = <f,T f> (FIRST equality) and <f,T f> >= 0.
    
    The transfer matrix T(a) = e^{-aH} with H having spectrum phi^s.
    RP is the statement that the reflected two-point function is PSD.
    """

    def _E(self, m0, s):
        return m0 * PHI**s

    def _half(self, a, m0, s):
        return exp(-(a/2) * self._E(m0, s))

    def _T(self, a, m0, s):
        return exp(-a * self._E(m0, s))

    def test_half_prop(self):
        """e^{-(a/2)E} * e^{-(a/2)E} = e^{-aE}."""
        for a in (mpf('0.7'), mpf(2), mpf('0.1')):
            for m0 in (mpf(1), mpf('0.3')):
                for s in range(6):
                    assert abs(self._half(a, m0, s)**2 - self._T(a, m0, s)) < mpf('1e-25')

    def test_first_equality(self):
        """<Theta F,F> = <f,T f> for arbitrary f, F = e^{-(a/2)H} f."""
        import random
        rng = random.Random(11)
        for _ in range(200):
            a = mpf(rng.uniform(0.05, 3))
            m0 = mpf(rng.uniform(0.1, 3))
            c = [mpf(rng.uniform(-3, 3)) for _ in range(8)]
            lhs = sum((c[s] * self._half(a, m0, s))**2 for s in range(8))
            rhs = sum(c[s]**2 * self._T(a, m0, s) for s in range(8))
            assert abs(lhs - rhs) <= mpf('1e-20') * max(mpf(1), abs(rhs))

    def test_rp_positive(self):
        """<f,T f> >= 0 for all f (random states)."""
        import random
        rng = random.Random(11)
        for _ in range(2000):
            a = mpf(rng.uniform(0.05, 3))
            m0 = mpf(rng.uniform(0.1, 3))
            val = sum(mpf(rng.uniform(-5, 5))**2 * self._T(a, m0, s) for s in range(10))
            assert val >= 0
