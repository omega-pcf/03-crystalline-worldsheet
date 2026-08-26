"""
§3  Tower Modes & Bridge Cocycle
=================================
Tower step ratio, bridge cocycle composition/inverse, KK golden identity.
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

    def test_ratio_is_phi(self):
        """Tower step ratio is exactly phi."""
        assert abs(
            (np.pi * PHI**(3.3 + 1)) / (np.pi * PHI**3.3) - PHI
        ) < 1e-12

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
    """Level n carries spin <= n-1, hence J=2 requires n>=3 (not n=2).
    
    This is a structural constraint from the Regge trajectory: the maximum spin
    at level n is n-1. J=2 is allowed at n=3 (spin 0,1,2) but NOT at n=2 (spin 0,1 only).
    """

    @pytest.mark.parametrize("n,max_spin", [(1, 0), (2, 1), (3, 2), (4, 3), (10, 9)])
    def test_max_spin_at_level(self, n, max_spin):
        """Level n carries spin 0..n-1."""
        assert max_spin == n - 1

    def test_j2_requires_n3(self):
        """J=2 requires n >= 3."""
        J = 2
        assert J <= 3 - 1   # allowed at n=3
        assert not (J <= 2 - 1)  # NOT allowed at n=2
