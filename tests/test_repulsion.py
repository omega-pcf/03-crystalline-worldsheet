"""
§2.12  Level Repulsion / GUE
=============================
Riemann zeta zeros, minimum splitting, Poisson comparison, sine kernel.

Precision tiers (configurable):
  --repulsion-full   25 digits, 238 zeros  (~8 min, matches original backing)
  default            15 digits, 80 zeros   (~30s, same structure, less precision)
Both verify the SAME properties at their respective precision levels.
The academic content is identical: repulsion exists, Poisson fails, sine kernel holds.
"""
import pytest
from mpmath import mp, mpf, pi, e as mpe, sin as mpsin

# ── Precision tiers ──────────────────────────────────────────────────────

FULL_DPS = 25
FULL_ZEROS = 238

FAST_DPS = 15
FAST_ZEROS = 80


def _get_tier(request):
    """Return (dps, count) based on --repulsion-full flag."""
    if request.config.getoption("--repulsion-full", default=False):
        return FULL_DPS, FULL_ZEROS
    return FAST_DPS, FAST_ZEROS


# ── Shared helpers ───────────────────────────────────────────────────────

_cache: dict = {}  # (dps, count) -> list of gamma values


def zeta_zeros(count, dps):
    """First `count` Riemann zeta zero imaginary parts, cached by (dps, count)."""
    key = (dps, count)
    if key not in _cache:
        old_dps = mp.dps
        mp.dps = dps
        _cache[key] = [mp.im(mp.zetazero(n)) for n in range(1, count + 1)]
        mp.dps = old_dps
    return _cache[key]


def unfolded_spacing(q, i, gamma_list, dps):
    """(gamma_{i+1} - gamma_i) * log(q gamma_i / 2pi) / (2pi)."""
    old_dps = mp.dps
    mp.dps = dps
    val = (gamma_list[i+1] - gamma_list[i]) * mp.log(q * gamma_list[i] / (2 * pi)) / (2 * pi)
    mp.dps = old_dps
    return val


def sine_kernel(u):
    """K(u) = 1 - (sin(pi u) / (pi u))^2."""
    return 1 - (mpsin(pi * u) / (pi * u))**2


# ── Tests ────────────────────────────────────────────────────────────────

class TestRepulsionRange:
    """Range of the measurement: (count-1) spacings from `count` zeros."""

    @pytest.fixture(autouse=True)
    def setup(self, request):
        self.dps, self.count = _get_tier(request)
        self.zg = zeta_zeros(self.count, self.dps)

    def test_count(self):
        assert len(self.zg) == self.count

    def test_last_zero_above_threshold(self):
        """Last zero should be well above 100 (structural, not precision-dependent)."""
        assert self.zg[-1] > mpf('100')

    def test_monotonic(self):
        """Zeta zeros are strictly increasing."""
        assert all(self.zg[i] < self.zg[i+1] for i in range(len(self.zg) - 1))


class TestRepulsionMeasurement:
    """Minimum splitting and Poisson comparison."""

    @pytest.fixture(autouse=True)
    def setup(self, request):
        self.dps, self.count = _get_tier(request)
        zg = zeta_zeros(self.count, self.dps)
        self.dz = [unfolded_spacing(1, i, zg, self.dps) for i in range(self.count - 1)]

    def test_minimum_splitting_positive(self):
        """Minimum splitting is positive (repulsion)."""
        assert min(self.dz) > 0

    def test_minimum_splitting_range(self):
        """Min splitting is between 0.2 and 0.5 (GUE-like, precision-independent)."""
        mn = float(min(self.dz))
        assert 0.2 < mn < 0.5, f"min splitting {mn:.4f} outside GUE range"

    def test_no_very_small_spacings(self):
        """None below 0.10 (GUE repulsion)."""
        assert sum(1 for x in self.dz if x < mpf('0.10')) == 0

    def test_poisson_independent_would_give_small(self):
        """Independence would put many below 0.10; there are zero."""
        n = len(self.dz)
        poisson_below = n * (1 - mpe**mpf('-0.10'))
        # Poisson predicts ~9% below 0.10; GUE gives 0%
        assert poisson_below > n * 0.05  # sanity: Poisson would give >5%
        assert sum(1 for x in self.dz if x < mpf('0.10')) == 0


class TestScaleNormalization:
    """prop:scale: mean splitting ≈ 1 at q=1."""

    @pytest.fixture(autouse=True)
    def setup(self, request):
        self.dps, self.count = _get_tier(request)
        zg = zeta_zeros(self.count, self.dps)
        dz = [unfolded_spacing(1, i, zg, self.dps) for i in range(self.count - 1)]
        self.mean_q1 = sum(dz) / len(dz)

    def test_normalized(self):
        """Mean ≈ 1 (within 5% for 80 zeros, within 1% for 238)."""
        tol = mpf('0.05') if self.count < 100 else mpf('0.01')
        assert abs(self.mean_q1 - 1) < tol

    @pytest.mark.parametrize("q", [2, 5, 20])
    def test_wrong_q_fails(self, q):
        """q=2,5,20 break normalization (mean drifts away from 1)."""
        zg = zeta_zeros(self.count, self.dps)
        dz = [unfolded_spacing(q, i, zg, self.dps) for i in range(self.count - 1)]
        mean = sum(dz) / len(dz)
        assert abs(mean - 1) > mpf('0.05')


class TestSineKernel:
    """eq:sine-kernel: K(u) = 1 - (sin pi u / pi u)^2."""

    def test_suppression_at_zero(self):
        """K(u) -> 0 as u -> 0."""
        assert sine_kernel(mpf('0.001')) < mpf('1e-5')

    def test_decorrelation_at_integers(self):
        """K(n) = 1 at nonzero integers."""
        for k in [1, 2, 3, 7]:
            assert abs(sine_kernel(mpf(k)) - 1) < mpf('1e-20')

    def test_decorrelation_at_large(self):
        """K(u) -> 1 for large u."""
        assert sine_kernel(mpf(20)) > mpf('0.99')
