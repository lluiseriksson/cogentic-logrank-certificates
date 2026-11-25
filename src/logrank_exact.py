"""Pure-stdlib exact-Q linear algebra, third-moment SVD tensor, Bregman divergence,
quadratic slice, and monochromatic rank-split primitives for Paper 58
(Google Research Cogentic, Nov 25, 2026: "Breaking the Square-Root Barrier for the Log-Rank Conjecture").

ZERO floating-point arithmetic: exclusively Python `int` and `fractions.Fraction`.

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

MatQ = List[List[Fraction]]
VecQ = List[Fraction]

ZERO = Fraction(0, 1)
ONE = Fraction(1, 1)
TWO = Fraction(2, 1)
HALF = Fraction(1, 2)
QUARTER = Fraction(1, 4)


def format_rat(q: Fraction) -> str:
    """Format a Fraction canonically in lowest terms ('n' or 'n/d' with d >= 2)."""
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def dot_q(u: Sequence[Fraction], v: Sequence[Fraction]) -> Fraction:
    return sum((a * b for a, b in zip(u, v)), ZERO)


def weighted_inner_q(u: Sequence[Fraction], v: Sequence[Fraction], w: Sequence[Fraction]) -> Fraction:
    return sum((wi * ui * vi for ui, vi, wi in zip(u, v, w)), ZERO)


def rank_exact_q(matrix: Sequence[Sequence[Fraction]]) -> int:
    """Exact rank over Q via Gauss-Jordan row reduction (zero floats)."""
    if not matrix or not matrix[0]:
        return 0
    m = len(matrix)
    n = len(matrix[0])
    A: MatQ = [list(row) for row in matrix]
    rank = 0
    for col in range(n):
        pivot = None
        for r in range(rank, m):
            if A[r][col] != ZERO:
                pivot = r
                break
        if pivot is None:
            continue
        A[rank], A[pivot] = A[pivot], A[rank]
        piv_val = A[rank][col]
        for r in range(rank + 1, m):
            if A[r][col] != ZERO:
                factor = A[r][col] / piv_val
                for c in range(col, n):
                    A[r][c] -= factor * A[rank][c]
        rank += 1
        if rank == m:
            break
    return rank


def mat_mul_q(A: MatQ, B: MatQ) -> MatQ:
    m = len(A)
    k = len(B)
    n = len(B[0]) if k > 0 else 0
    out: MatQ = [[ZERO for _ in range(n)] for _ in range(m)]
    for i in range(m):
        for j in range(n):
            s = ZERO
            for t in range(k):
                s += A[i][t] * B[t][j]
            out[i][j] = s
    return out


def mat_sub_q(A: MatQ, B: MatQ) -> MatQ:
    return [[a - b for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def mat_trace_q(A: MatQ) -> Fraction:
    return sum((A[i][i] for i in range(len(A))), ZERO)


def mat_frob_sq_q(A: MatQ) -> Fraction:
    return sum((v * v for row in A for v in row), ZERO)


def is_symmetric_q(A: MatQ) -> bool:
    n = len(A)
    for i in range(n):
        if len(A[i]) != n:
            return False
        for j in range(i + 1, n):
            if A[i][j] != A[j][i]:
                return False
    return True


def is_psd_q(A: MatQ) -> bool:
    """Exact-Q test for symmetric positive semidefiniteness (A >= 0) via exact rational
    symmetric diagonal-pivoted congruence reduction (Sylvester law of inertia, zero floats)."""
    if not is_symmetric_q(A):
        return False
    n = len(A)
    M: MatQ = [list(row) for row in A]
    for k in range(n):
        for i in range(k, n):
            if M[i][i] < ZERO:
                return False
        piv = None
        for i in range(k, n):
            if M[i][i] > ZERO:
                piv = i
                break
        if piv is None:
            for i in range(k, n):
                for j in range(i + 1, n):
                    if M[i][j] != ZERO:
                        return False
            return True
        if piv != k:
            M[k], M[piv] = M[piv], M[k]
            for row in M:
                row[k], row[piv] = row[piv], row[k]
        d = M[k][k]
        for i in range(k + 1, n):
            lik = M[i][k]
            if lik != ZERO:
                for j in range(i, n):
                    val = M[i][j] - (lik * M[k][j]) / d
                    M[i][j] = val
                    M[j][i] = val
    return True


def doubly_center_q(A: MatQ, mu_X: VecQ, mu_Y: VecQ) -> Tuple[MatQ, Fraction]:
    """Exact mu-doubly-centered matrix A_{dc,mu}(x,y) = A(x,y) - E_Y[A(x,.)] - E_X[A(.,y)] + E_mu[A]."""
    m = len(A)
    n = len(A[0])
    row_means = [sum((mu_Y[j] * A[i][j] for j in range(n)), ZERO) for i in range(m)]
    col_means = [sum((mu_X[i] * A[i][j] for i in range(m)), ZERO) for j in range(n)]
    grand = sum((mu_X[i] * row_means[i] for i in range(m)), ZERO)
    Adc: MatQ = [
        [A[i][j] - row_means[i] - col_means[j] + grand for j in range(n)]
        for i in range(m)
    ]
    return Adc, grand


def hollow_quadratic_slices_q(Adc: MatQ, mu_X: VecQ, W: MatQ) -> List[MatQ]:
    """Compute exact hollow quadratic slice matrices L_ring^(w)_y for every y in Y:
    (L_y)_{a,b} = E_{x~mu_X}[A_dc(x,y) w_a(x) w_b(x)], hollow zeros diagonal a == b."""
    m = len(Adc)
    n = len(Adc[0])
    d = len(W[0])
    slices: List[MatQ] = []
    for y in range(n):
        Ly: MatQ = [[ZERO for _ in range(d)] for _ in range(d)]
        for a in range(d):
            for b in range(a + 1, d):
                val = sum((mu_X[x] * Adc[x][y] * W[x][a] * W[x][b] for x in range(m)), ZERO)
                Ly[a][b] = val
                Ly[b][a] = val
        slices.append(Ly)
    return slices


def third_moment_energy_q(
    sigma: Sequence[Fraction],
    B_vecs: Sequence[Sequence[Fraction]],
    mu_Y: Sequence[Fraction],
) -> Tuple[Fraction, List[List[List[Fraction]]]]:
    """Exact third-moment tensor T^Y_{k,i,j} = E_{mu_Y}[b_k b_i b_j] and exact
    weighted squared Frobenius energy sum_k ||M_hat^Y_k||_F^2 = sum_{k,i,j} sigma_i sigma_j (T^Y_{k,i,j})^2."""
    r = len(sigma)
    n = len(mu_Y)
    T: List[List[List[Fraction]]] = [[[ZERO for _ in range(r)] for _ in range(r)] for _ in range(r)]
    energy = ZERO
    for k in range(r):
        bk = B_vecs[k]
        for i in range(r):
            bi = B_vecs[i]
            for j in range(r):
                bj = B_vecs[j]
                val = sum((mu_Y[y] * bk[y] * bi[y] * bj[y] for y in range(n)), ZERO)
                T[k][i][j] = val
                energy += sigma[i] * sigma[j] * val * val
    return energy, T


def penalty_g_q(t: Fraction) -> Fraction:
    """Exact Eq. (1.7) variational penalty g(t) = 2(1 - t) - (1/4)(1 - t)^2."""
    u = ONE - t
    return TWO * u - QUARTER * u * u


def penalty_g_prime_q(t: Fraction) -> Fraction:
    """Exact derivative g'(t) = -(3 + t) / 2."""
    return -(Fraction(3, 1) + t) * HALF


def ceil_log_three_halves(L: int) -> int:
    """Exact integer ceiling ceil(log_{3/2}(L)) = min {k >= 0 : 2^k * L <= 3^k}."""
    if L <= 1:
        return 0
    k = 0
    p2 = 1
    p3 = 1
    while p2 * L > p3:
        k += 1
        p2 *= 2
        p3 *= 3
    return k


def rank_halving_orbit(k: int) -> List[int]:
    """Exact Prop. A.3 rank orbit k -> floor(3k/4) until <= 1."""
    orb = [k]
    cur = k
    while cur > 1:
        cur = (3 * cur) // 4
        orb.append(cur)
    return orb
