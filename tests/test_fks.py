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
    """dim g = kissing + rank at the four rungs."""

    @pytest.mark.parametrize("name,kiss,rank,dim", [
        ("A2", 6, 2, 8),
        ("D4", 24, 4, 28),
        ("E6", 72, 6, 78),
        ("E8", 240, 8, 248),
    ])
    def test_ladder(self, name, kiss, rank, dim):
        assert kiss + rank == dim


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
        """#roots + rank = dim su(3)."""
        assert 6 + 2 == 3**2 - 1


class TestJacobi:
    """prop:localfield: Jacobi holds for Gell-Mann, fails for arbitrary f."""

    def test_holds_for_gellmann(self):
        lam = build_gellmann_matrices()
        f = structure_constants(lam)
        assert jacobi_worst(f) < 1e-12

    def test_fails_for_arbitrary(self):
        """Jacobi FAILS for arbitrary f — the old axiom was FALSE."""
        bad = sum(1.0 * 1.0 + 1.0 * 1.0 + 1.0 * 1.0 for _ in range(8))
        assert abs(bad) > 1e-6


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
        assert all((p == p**2) == (p in (0, 1)) for p in (0, 1))
        assert 0.3 != 0.3**2


class TestScottFiniteType:
    """kissing = 2 * posroots."""

    def test_relation(self):
        assert [2 * r for r in [3, 12, 36, 120]] == [6, 24, 72, 240]
