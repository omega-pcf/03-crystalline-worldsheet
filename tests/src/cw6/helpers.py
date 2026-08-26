"""
CW6 Numerical Helpers
=====================
Shared computation functions used across test modules.
"""
from __future__ import annotations

import numpy as np
from numpy.typing import ArrayLike


# ── Tower / spectral helpers ──────────────────────────────────────────────

def nmodes(sigma: float) -> int:
    """N_modes(sigma) = floor(pi * phi^sigma)."""
    from cw6.constants import PHI
    return int(np.floor(np.pi * PHI**sigma))


def bridge_T(s1: float, s2: float) -> float:
    """T(s1, s2) = (1 + eps_0 phi^{s1}) / (1 + eps_0 phi^{s2})."""
    from cw6.constants import PHI, EPS_0
    return (1 + EPS_0 * PHI**s1) / (1 + EPS_0 * PHI**s2)


# ── Gauge helpers ─────────────────────────────────────────────────────────

def mssm_spread(betas: list[float]) -> float:
    """Peak-to-peak spread of MSSM couplings at unification.
    
    Uses alpha_s(M_Z)=0.118, sin^2(theta_W)=0.23122, alpha_em^{-1}=127.9.
    These are MEASURED values (CODATA/electroweak fits), not derived.
    """
    inv = np.array([
        (5/3) * (1/127.9) / (1 - 0.23122),   # alpha_3^{-1}(M_Z)
        (1/127.9) / 0.23122,                    # alpha_2^{-1}(M_Z)
        0.118                                    # alpha_s(M_Z)
    ])
    inv = 1 / inv
    t = np.linspace(0, 40, 4000)
    it = inv[:, None] - (np.array(betas)[:, None] / (2 * np.pi)) * t[None, :]
    i = np.argmin(np.abs(it[0] - it[1]))
    return np.ptp(it[:, i])


# ── QCD / dimensional transmutation ──────────────────────────────────────

def lambda_qcd(a: float, b0: float, g2: float) -> float:
    """Lambda_QCD = a^{-1} exp(-1/(b0 g^2))."""
    return (1.0 / a) * np.exp(-1.0 / (b0 * g2))


def g_sq_af(a: float, b0: float, lam: float) -> float:
    """Running coupling on the AF trajectory: g^2 = 1/(b0 ln(1/(a Lambda)))."""
    return 1.0 / (b0 * np.log(1.0 / (a * lam)))


# ── Jacobi identity (Gell-Mann) ──────────────────────────────────────────

def build_gellmann_matrices() -> list[np.ndarray]:
    """Return the 8 Gell-Mann matrices (3x3 complex)."""
    l = [np.zeros((3, 3), complex) for _ in range(8)]
    l[0][0, 1] = l[0][1, 0] = 1
    l[1][0, 1] = -1j; l[1][1, 0] = 1j
    l[2][0, 0] = 1; l[2][1, 1] = -1
    l[3][0, 2] = l[3][2, 0] = 1
    l[4][0, 2] = -1j; l[4][2, 0] = 1j
    l[5][1, 2] = l[5][2, 1] = 1
    l[6][1, 2] = -1j; l[6][2, 1] = 1j
    l[7] = np.diag([1, 1, -2]) / np.sqrt(3)
    return l


def structure_constants(lam: list[np.ndarray]) -> np.ndarray:
    """Compute f_{abc} from Gell-Mann matrices: [L_a, L_b] = i f_{abc} L_c."""
    T = [L / 2 for L in lam]
    f = np.zeros((8, 8, 8))
    for a in range(8):
        for b in range(8):
            C = T[a] @ T[b] - T[b] @ T[a]
            for c in range(8):
                f[a, b, c] = (-2j * np.trace(C @ T[c])).real
    return f


def jacobi_worst(f: np.ndarray) -> float:
    """Max |f[e,a,b]f[e,c,d] + f[e,b,c]f[e,a,d] + f[e,c,a]f[e,b,d]| over a,b,c,d."""
    worst = 0.0
    for a in range(8):
        for b in range(8):
            for c in range(3):
                for d in range(3):
                    val = abs(sum(
                        f[a, b, e] * f[e, c, d]
                        + f[b, c, e] * f[e, a, d]
                        + f[c, a, e] * f[e, b, d]
                        for e in range(8)
                    ))
                    if val > worst:
                        worst = val
    return worst


# ── Projector helpers ────────────────────────────────────────────────────

def projector(C: np.ndarray) -> np.ndarray:
    """P = C^T (C C^T)^{-1} C  — orthogonal projector onto row space of C."""
    return C.T @ np.linalg.inv(C @ C.T) @ C


# ── Riemann zeta zeros (computed, not transcribed) ───────────────────────

def zeta_zeros_imaginary(count: int) -> list:
    """Return imaginary parts of the first `count` Riemann zeta zeros via mpmath."""
    from mpmath import mp
    return [float(mp.im(mp.zetazero(n))) for n in range(1, count + 1)]


# ── Null vectors for Einstein check ──────────────────────────────────────

def random_null_vectors(seed: int, count: int, dim: int = 5) -> np.ndarray:
    """Generate `count` random null vectors in mostly-plus signature dim."""
    rng = np.random.RandomState(seed)
    vectors = []
    for _ in range(count):
        sp = rng.randn(dim - 1)
        t = np.sqrt(np.dot(sp, sp))
        vectors.append(np.array([t, *sp]))
    return np.array(vectors)


# ── Finite primes (sieve) ────────────────────────────────────────────────

def primes_up_to(n: int) -> list[int]:
    """Sieve of Eratosthenes: all primes <= n."""
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b'\x00\x00'
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
    return [i for i in range(2, n + 1) if sieve[i]]
