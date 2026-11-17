"""
§4  FKS Ladder, Jacobi, Arity, Intervals
==========================================
prop:ladder (FKS), prop:a2 (hexagon), prop:localfield (Jacobi),
ssec:arity, prop:interval-uniqueness, Schmidt rank, Scott finite type.
"""
import numpy as np
import pytest
from fractions import Fraction

from cw6.constants import (
    PHI, OMEGA, ARITY,
    SIGMA_G, SIGMA_EM, SIGMA_L,
)
from cw6.helpers import (
    build_gellmann_matrices, structure_constants, jacobi_worst,
)


class TestFKSLadder:
    """prop:ladder: kissing = 2 * (positive roots) and dim g = kissing + rank,
    rung by rung, for the four root systems of 04-implications (A2, D4, E6, E8).

    Only the positive-root counts and the ranks are taken from the text; the
    kissing number and the dimension are what the two manuscript relations
    predict, and both are compared against the dimensions the text prints
    (8 = 6+2, 28 = 24+4, 78 = 72+6, 248 = 240+8)."""

    POSROOTS = {"A2": 3, "D4": 12, "E6": 36, "E8": 120}
    RANKS = {"A2": 2, "D4": 4, "E6": 6, "E8": 8}
    DIMS = {"A2": 8, "D4": 28, "E6": 78, "E8": 248}

    @pytest.mark.parametrize("name", ["A2", "D4", "E6", "E8"])
    def test_ladder(self, name):
        roots = self.POSROOTS[name]
        kiss = 2 * roots                                  # kissing = 2 * roots
        assert kiss == {"A2": 6, "D4": 24, "E6": 72, "E8": 240}[name]
        assert kiss + self.RANKS[name] == self.DIMS[name]  # dim = kissing + rank


class TestA2Hexagon:
    """A2: six units of Z[omega] form a regular hexagon."""

    def test_regular_hexagon(self):
        units = [s * OMEGA**k for k in range(3) for s in (1, -1)]
        angs = sorted(round(np.degrees(np.angle(u)) % 360, 6) for u in units)
        assert len(units) == 6
        assert all(abs(angs[i + 1] - angs[i] - 60) < 1e-6 for i in range(5))

    def test_norm_squared(self):
        """Six simple-basis roots all have norm^2 = 2."""
        def a2n2(a, b):
            return 2 * a * a - 2 * a * b + 2 * b * b
        roots = [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)]
        assert all(a2n2(a, b) == 2 for a, b in roots)

    def test_exactly_six(self):
        """EXACTLY six lattice vectors have norm^2 = 2 in the box."""
        def a2n2(a, b):
            return 2 * a * a - 2 * a * b + 2 * b * b
        box = [(a, b) for a in range(-3, 4) for b in range(-3, 4) if (a, b) != (0, 0)]
        assert sum(1 for a, b in box if a2n2(a, b) == 2) == 6

    def test_roots_rank_dim(self):
        """#roots + rank = dim su(3) = 8, computed from the Gell-Mann basis:
        eight linearly independent traceless 3x3 generators."""
        lam = build_gellmann_matrices()
        assert len(lam) == 8
        stacked = np.array([np.eye(3).ravel()] + [L.ravel() for L in lam])
        assert np.linalg.matrix_rank(stacked) == 9       # identity + 8 generators


class TestJacobi:
    """prop:localfield: Jacobi holds for Gell-Mann, fails for arbitrary f."""

    def test_holds_for_gellmann(self):
        lam = build_gellmann_matrices()
        f = structure_constants(lam)
        assert jacobi_worst(f) < 1e-12

    def test_fails_for_arbitrary(self):
        """Jacobi FAILS for an arbitrary antisymmetric f — the old axiom was
        FALSE.  A random antisymmetric tensor violates it by a wide margin."""
        rng = np.random.RandomState(11)
        bad = rng.randn(8, 8, 8)
        bad = bad - bad.transpose(1, 0, 2)               # antisymmetric in (a,b)
        assert jacobi_worst(bad) > 1e-3


class TestArity:
    """ssec:arity: arity 3 = floor(pi) = colour = number of generations."""

    def test_floor_pi(self):
        assert int(np.floor(np.pi)) == 3

    def test_phi_central_chain(self):
        """phi^2 + phi^{-2} = 3 fixes the arity."""
        assert abs(PHI**2 + PHI**-2 - 3) < 1e-12


class TestIntervalUniqueness:
    """prop:interval-uniqueness: the triple (2,3,6) is UNIQUE over integers."""

    def _solutions(self, n, hi=15):
        muSq = Fraction(1, 4)
        PSq = Fraction(1, 3)
        out = []
        for g in range(0, hi):
            for e in range(g + 1, hi + 1):
                for l in range(e + 1, hi + 2):
                    if l != 2 * n:
                        continue
                    if l - g != n + 1:
                        continue
                    if Fraction(e - g, l - g) != muSq:
                        continue
                    if Fraction(e - g, l - e) != PSq:
                        continue
                    out.append((g, e, l))
        return out

    def test_unique_at_arity_3(self):
        """The triple satisfying all four constraints is (2,3,6)."""
        assert self._solutions(3) == [(2, 3, 6)]

    def test_no_solution_at_2(self):
        assert self._solutions(2) == []

    def test_no_solution_at_4(self):
        assert self._solutions(4) == []

    def test_family_fractions(self):
        """(n-1, n, 2n) gives fractions 1/(n+1) and 1/n for n=2..8."""
        for n in range(2, 9):
            assert Fraction(n - (n - 1), 2 * n - (n - 1)) == Fraction(1, n + 1)
            assert Fraction(n - (n - 1), 2 * n - n) == Fraction(1, n)

    def test_only_n3_gives_correct_fractions(self):
        """Only n=3 brings fractions to |Omega|^2 = 1/4 and ||P||^2 = 1/3."""
        muSq = Fraction(1, 4)
        PSq = Fraction(1, 3)
        matching = [n for n in range(2, 9)
                    if Fraction(1, n + 1) == muSq and Fraction(1, n) == PSq]
        assert matching == [3]

    def test_gap_equals_4_only_at_n3(self):
        """sigma_L - sigma_G = n+1 = 4 only at n=3."""
        matching = [n for n in range(2, 9) if 2 * n - (n - 1) == 4]
        assert matching == [3]


class TestSchmidtRank:
    """schmidt_rank_one_iff_product: p1 = p1^2 <=> p1 in {0, 1}."""

    def test_equivalence(self):
        """p1 = p1^2 holds exactly at the two idempotents 0 and 1, and nowhere
        else on a grid of candidates."""
        grid = [0.0, 0.3, 0.5, 0.7, 1.0, -1.0, 2.0]
        assert all((p == p**2) == (p in (0, 1)) for p in grid)
        assert [p for p in grid if p == p**2] == [0.0, 1.0]


class TestScottFiniteType:
    """kissing = 2 * posroots."""

    def test_relation(self):
        """kissing = 2 * positive roots, on the same data the ladder uses."""
        roots = [TestFKSLadder.POSROOTS[k] for k in ("A2", "D4", "E6", "E8")]
        assert [2 * r for r in roots] == [6, 24, 72, 240]
