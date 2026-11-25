"""Pure-stdlib zero-floating-point exact-Q certificate auditor: LOGRANK-COGENTIC-CERT-1.0.
Audits all four algebraic, spectral-tensor, Bregman/slice, and Nisan-Wigderson recursion pillars of
Google Research Cogentic (Nov 25, 2026), "Breaking the Square-Root Barrier for the Log-Rank Conjecture":
  - Mode 1: boolean_sign_third_moment_cert (Sec. 1.2 & Eq. (1.6) Booleanity quadratic identity & third-moment energy vs. Rademacher barrier)
  - Mode 2: quadratic_slice_bregman_cert (Sec. 2.1-2.2 hollow quadratic slices, Eq. (2.2) matrix square-root Bregman, trace commutator)
  - Mode 3: monochromatic_rank_split_cert (Thm. 1.1 & Prop. A.3 monochromatic rectangle density, rank-split <= r+1, protocol balancing)
  - Mode 4: nw_recursion_and_penalty_cert (Eq. (1.7) concave penalty, Prop. A.3 geometric contraction & 750*C0 closure, Thm. 1.1 constants)

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Set, Tuple

from src.logrank_exact import (
    HALF,
    ONE,
    TWO,
    ZERO,
    MatQ,
    VecQ,
    ceil_log_three_halves,
    doubly_center_q,
    format_rat,
    hollow_quadratic_slices_q,
    is_psd_q,
    is_symmetric_q,
    mat_frob_sq_q,
    mat_mul_q,
    mat_sub_q,
    mat_trace_q,
    penalty_g_prime_q,
    penalty_g_q,
    rank_exact_q,
    rank_halving_orbit,
    third_moment_energy_q,
    weighted_inner_q,
)

SCHEMA_VERSION = "LOGRANK-COGENTIC-CERT-1.0"
MAX_DEPTH = 20
MAX_STR_LEN = 2000
MAX_INT_BITS = 4096


class CertificateError(ValueError):
    """Raised whenever a LOGRANK-COGENTIC-CERT-1.0 certificate fails any invariant."""


def _deny_ieee754(token: str) -> Any:
    raise CertificateError(f"IEEE-754 floating-point token forbidden: {token!r}")


def _reject_constant(token: str) -> Any:
    raise CertificateError(f"Non-finite JSON constant forbidden: {token!r}")


def _reject_duplicate_keys(pairs: List[Tuple[str, Any]]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise CertificateError(f"Duplicate JSON object key forbidden: {k!r}")
        out[k] = v
    return out


def _validate_ast(obj: Any, depth: int = 0) -> None:
    if depth > MAX_DEPTH:
        raise CertificateError(f"JSON nesting depth exceeds cap {MAX_DEPTH}")
    t = type(obj)
    if t is int:
        if obj.bit_length() > MAX_INT_BITS:
            raise CertificateError(f"Integer bit-length exceeds {MAX_INT_BITS}")
        return
    if t is bool:
        return
    if t is str:
        if len(obj) > MAX_STR_LEN:
            raise CertificateError(f"String length exceeds cap {MAX_STR_LEN}")
        return
    if t is list:
        for item in obj:
            _validate_ast(item, depth + 1)
        return
    if t is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise CertificateError("Dictionary key must be str")
            _validate_ast(v, depth + 1)
        return
    raise CertificateError(f"Forbidden AST type: {t.__name__}")


def _is_ascii_digits(s: str) -> bool:
    return bool(s) and s.isascii() and s.isdigit()


def _parse_int(val: Any, name: str) -> int:
    if type(val) is not int:
        raise CertificateError(f"{name} must be strict int, got {type(val).__name__}")
    return val


def _parse_bool(val: Any, name: str) -> bool:
    if type(val) is not bool:
        raise CertificateError(f"{name} must be strict bool, got {type(val).__name__}")
    return val


def _parse_rat(val: Any, name: str) -> Fraction:
    if type(val) is not str:
        raise CertificateError(f"{name} must be canonical rational str, got {type(val).__name__}")
    if len(val) == 0 or len(val) > MAX_STR_LEN:
        raise CertificateError(f"{name} rational string length invalid")
    if val[0] == "+":
        raise CertificateError(f"{name} leading '+' forbidden: {val!r}")
    if "/" in val:
        parts = val.split("/")
        if len(parts) != 2:
            raise CertificateError(f"{name} malformed fraction: {val!r}")
        ns, ds = parts
        neg = ns.startswith("-")
        num_digits = ns[1:] if neg else ns
        if not _is_ascii_digits(num_digits) or not _is_ascii_digits(ds):
            raise CertificateError(f"{name} non-ASCII-digit fraction: {val!r}")
        if (len(num_digits) > 1 and num_digits[0] == "0") or (len(ds) > 1 and ds[0] == "0"):
            raise CertificateError(f"{name} leading zero forbidden: {val!r}")
        num = -int(num_digits) if neg else int(num_digits)
        den = int(ds)
        if num == 0:
            raise CertificateError(f"{name} zero must be formatted as '0', got {val!r}")
        if den < 2:
            raise CertificateError(f"{name} denominator must be >= 2, got {val!r}")
        q = Fraction(num, den)
        if q.numerator != num or q.denominator != den:
            raise CertificateError(f"{name} unreduced fraction: {val!r}")
        return q
    neg = val.startswith("-")
    digits = val[1:] if neg else val
    if not _is_ascii_digits(digits):
        raise CertificateError(f"{name} non-ASCII-digit integer rational: {val!r}")
    if len(digits) > 1 and digits[0] == "0":
        raise CertificateError(f"{name} leading zero forbidden: {val!r}")
    if neg and digits == "0":
        raise CertificateError(f"{name} negative zero forbidden: {val!r}")
    num = -int(digits) if neg else int(digits)
    return Fraction(num, 1)


def _check_keys(cert: Dict[str, Any], req: Set[str], mode: str) -> None:
    keys = set(cert.keys())
    if keys != req:
        raise CertificateError(f"{mode} schema key mismatch: {sorted(keys ^ req)}")


def _parse_rat_vec(raw: Any, n: int, name: str) -> VecQ:
    if type(raw) is not list or len(raw) != n:
        raise CertificateError(f"{name} must be list of length {n}")
    return [_parse_rat(raw[i], f"{name}[{i}]") for i in range(n)]


def _parse_rat_mat(raw: Any, m: int, n: int, name: str) -> MatQ:
    if type(raw) is not list or len(raw) != m:
        raise CertificateError(f"{name} must have {m} rows")
    return [_parse_rat_vec(raw[i], n, f"{name}[{i}]") for i in range(m)]


def _parse_prob(raw: Any, n: int, name: str) -> VecQ:
    v = _parse_rat_vec(raw, n, name)
    if any(p <= ZERO for p in v):
        raise CertificateError(f"{name} must be strictly positive (full-support)")
    if sum(v, ZERO) != ONE:
        raise CertificateError(f"{name} must sum to 1, got {sum(v, ZERO)}")
    return v


# =============================================================================
# Mode 1: Sec. 1.2 & Eq. (1.6) Boolean Sign Matrix Third-Moment SVD vs. Rademacher
# =============================================================================


def _verify_mode1(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "cert_id", "is_rademacher_barrier",
        "m", "n", "matrix_S", "mu_X", "mu_Y",
        "s1", "u1", "v1", "sigma", "A_vecs", "B_vecs",
        "claimed_rank_S", "claimed_bias_mu0", "claimed_eq16_max_residual",
        "claimed_third_moment_energy", "claimed_projection_checks",
    }
    _check_keys(cert, req, "Mode 1")
    is_rad = _parse_bool(cert["is_rademacher_barrier"], "is_rademacher_barrier")
    m = _parse_int(cert["m"], "m")
    n = _parse_int(cert["n"], "n")
    if not (2 <= m <= 16 and 2 <= n <= 16):
        raise CertificateError("Mode 1 requires 2 <= m, n <= 16")

    S = _parse_rat_mat(cert["matrix_S"], m, n, "matrix_S")
    mu_X = _parse_prob(cert["mu_X"], m, "mu_X")
    mu_Y = _parse_prob(cert["mu_Y"], n, "mu_Y")

    if not is_rad:
        for x in range(m):
            for y in range(n):
                if S[x][y] not in (ONE, -ONE):
                    raise CertificateError(f"Boolean sign matrix entry S[{x}][{y}]={S[x][y]} not in {{-1, +1}}")

    s1 = _parse_rat(cert["s1"], "s1")
    if s1 <= ZERO:
        raise CertificateError("s1 must be strictly positive")
    u1 = _parse_rat_vec(cert["u1"], m, "u1")
    v1 = _parse_rat_vec(cert["v1"], n, "v1")

    raw_sig = cert["sigma"]
    if type(raw_sig) is not list or not (1 <= len(raw_sig) <= min(m, n)):
        raise CertificateError("sigma must be non-empty list of length <= min(m, n)")
    r_perp = len(raw_sig)
    sigma = [_parse_rat(raw_sig[k], f"sigma[{k}]") for k in range(r_perp)]
    if any(s <= ZERO for s in sigma):
        raise CertificateError("All singular values sigma_k must be > 0")
    if s1 < sigma[0]:
        raise CertificateError("Top singular value s1 must satisfy s1 >= sigma[0]")
    for k in range(r_perp - 1):
        if sigma[k] < sigma[k + 1]:
            raise CertificateError("Singular values sigma must be non-increasing")

    A_vecs = _parse_rat_mat(cert["A_vecs"], r_perp, m, "A_vecs")
    B_vecs = _parse_rat_mat(cert["B_vecs"], r_perp, n, "B_vecs")

    # Verify exact mu-orthonormality of [u1, a_1, ..., a_r] and [v1, b_1, ..., b_r]
    all_u = [u1] + A_vecs
    all_v = [v1] + B_vecs
    for i in range(len(all_u)):
        for j in range(i, len(all_u)):
            target = ONE if i == j else ZERO
            if weighted_inner_q(all_u[i], all_u[j], mu_X) != target:
                raise CertificateError(f"Left singular vectors fail mu_X orthonormality at ({i}, {j})")
            if weighted_inner_q(all_v[i], all_v[j], mu_Y) != target:
                raise CertificateError(f"Right singular vectors fail mu_Y orthonormality at ({i}, {j})")

    # Verify exact SVD reconstruction S(x,y) = s1 u1(x) v1(y) + A_perp(x,y)
    # and Eq. (1.6) residual: |-2 s1 u1 v1 A_perp - (A_perp^2 + s1^2 u1^2 v1^2 - 1)|
    A_perp: MatQ = [[ZERO for _ in range(n)] for _ in range(m)]
    max_eq16_res = ZERO
    bias = ZERO
    for x in range(m):
        for y in range(n):
            bias += mu_X[x] * mu_Y[y] * S[x][y]
            ap = sum((sigma[k] * A_vecs[k][x] * B_vecs[k][y] for k in range(r_perp)), ZERO)
            A_perp[x][y] = ap
            recon = s1 * u1[x] * v1[y] + ap
            if recon != S[x][y]:
                raise CertificateError(f"SVD reconstruction mismatch at ({x}, {y}): {recon} != {S[x][y]}")
            lhs = -TWO * s1 * u1[x] * v1[y] * ap
            rhs = ap * ap + (s1 * u1[x] * v1[y]) ** 2 - ONE
            res = abs(lhs - rhs)
            if res > max_eq16_res:
                max_eq16_res = res
    if not is_rad and max_eq16_res != ZERO:
        raise CertificateError(f"Boolean sign matrix violated Eq. (1.6): max_residual={max_eq16_res}")

    # Compute exact third-moment tensor T^Y_{k,i,j} and weighted energy sum_k ||M_hat^Y_k||_F^2
    e3, T_Y = third_moment_energy_q(sigma, B_vecs, mu_Y)
    if is_rad and e3 != ZERO:
        raise CertificateError(f"Rademacher barrier matrix must have zero third-moment energy, got {e3}")

    # Verify exact projection of Eq. (1.6) against every b_k in L^2(mu_Y) for Boolean matrices!
    proj_checks = 0
    if not is_rad:
        for k in range(r_perp):
            bk = B_vecs[k]
            ev_v1sq_bk = sum((mu_Y[y] * v1[y] * v1[y] * bk[y] for y in range(n)), ZERO)
            ev_bk = sum((mu_Y[y] * bk[y] for y in range(n)), ZERO)
            for x in range(m):
                lhs_proj = sum((mu_Y[y] * (-TWO * s1 * u1[x] * v1[y] * A_perp[x][y]) * bk[y] for y in range(n)), ZERO)
                quad_form = ZERO
                for i in range(r_perp):
                    for j in range(r_perp):
                        quad_form += sigma[i] * sigma[j] * T_Y[k][i][j] * A_vecs[i][x] * A_vecs[j][x]
                rhs_proj = quad_form + (s1 * u1[x]) ** 2 * ev_v1sq_bk - ev_bk
                if lhs_proj != rhs_proj:
                    raise CertificateError(f"Eq. (1.6) b_k projection mismatch at k={k}, x={x}")
                proj_checks += 1
    else:
        # For Rademacher barrier, verify unit row/column L^2 norms: E_{mu_Y}[S(x,.)^2] == 1 and E_{mu_X}[S(.,y)^2] == 1
        for x in range(m):
            if sum((mu_Y[y] * S[x][y] * S[x][y] for y in range(n)), ZERO) != ONE:
                raise CertificateError(f"Rademacher row {x} does not have unit L^2(mu_Y) norm")
        for y in range(n):
            if sum((mu_X[x] * S[x][y] * S[x][y] for x in range(m)), ZERO) != ONE:
                raise CertificateError(f"Rademacher col {y} does not have unit L^2(mu_X) norm")

    rk_S = rank_exact_q(S)
    if _parse_int(cert["claimed_rank_S"], "claimed_rank_S") != rk_S:
        raise CertificateError(f"claimed_rank_S mismatch: exact={rk_S}")
    if _parse_rat(cert["claimed_bias_mu0"], "claimed_bias_mu0") != bias:
        raise CertificateError(f"claimed_bias_mu0 mismatch: exact={bias}")
    if _parse_rat(cert["claimed_eq16_max_residual"], "claimed_eq16_max_residual") != max_eq16_res:
        raise CertificateError(f"claimed_eq16_max_residual mismatch: exact={max_eq16_res}")
    if _parse_rat(cert["claimed_third_moment_energy"], "claimed_third_moment_energy") != e3:
        raise CertificateError(f"claimed_third_moment_energy mismatch: exact={e3}")
    if _parse_int(cert["claimed_projection_checks"], "claimed_projection_checks") != proj_checks:
        raise CertificateError(f"claimed_projection_checks mismatch: exact={proj_checks}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "rank_S": rk_S,
        "bias_mu0": format_rat(bias),
        "third_moment_energy": format_rat(e3),
        "eq16_max_residual": format_rat(max_eq16_res),
    }


# =============================================================================
# Mode 2: Sec. 2.1-2.2 Hollow Quadratic Slices, Matrix Sqrt Bregman & Commutator
# =============================================================================


def _verify_mode2(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "cert_id",
        "m", "n", "d", "q",
        "matrix_A", "mu_X", "mu_Y", "bulk_map_W",
        "bregman_P", "bregman_R", "bregman_sigma_diag",
        "comm_H", "comm_L",
        "claimed_total_variance_tau", "claimed_hollow_energy",
        "claimed_bregman_div", "claimed_commutator_trace_gap",
    }
    _check_keys(cert, req, "Mode 2")
    m = _parse_int(cert["m"], "m")
    n = _parse_int(cert["n"], "n")
    d = _parse_int(cert["d"], "d")
    q = _parse_int(cert["q"], "q")
    if not (2 <= m <= 16 and 2 <= n <= 16 and 2 <= d <= 8 and 2 <= q <= 6):
        raise CertificateError("Mode 2 dimensions out of bounds")

    A = _parse_rat_mat(cert["matrix_A"], m, n, "matrix_A")
    mu_X = _parse_prob(cert["mu_X"], m, "mu_X")
    mu_Y = _parse_prob(cert["mu_Y"], n, "mu_Y")
    W = _parse_rat_mat(cert["bulk_map_W"], m, d, "bulk_map_W")

    Adc, _ = doubly_center_q(A, mu_X, mu_Y)
    tau_w = sum((mu_X[x] * sum((W[x][a] * W[x][a] for a in range(d)), ZERO) for x in range(m)), ZERO)
    slices = hollow_quadratic_slices_q(Adc, mu_X, W)
    hollow_energy = sum((mu_Y[y] * mat_frob_sq_q(slices[y]) for y in range(n)), ZERO)

    # Exact Eq. (2.2) Matrix Square-Root Bregman divergence D_sr(P || Sigma^2)
    P = _parse_rat_mat(cert["bregman_P"], q, q, "bregman_P")
    R = _parse_rat_mat(cert["bregman_R"], q, q, "bregman_R")
    sig_diag = _parse_rat_vec(cert["bregman_sigma_diag"], q, "bregman_sigma_diag")
    if any(s <= ZERO for s in sig_diag):
        raise CertificateError("bregman_sigma_diag entries must be strictly positive")
    if not is_symmetric_q(P) or not is_symmetric_q(R):
        raise CertificateError("bregman_P and bregman_R must be symmetric")
    if not is_psd_q(R):
        raise CertificateError("bregman_R must be positive semidefinite (R >= 0)")
    if mat_mul_q(R, R) != P:
        raise CertificateError("bregman_R is not an exact matrix square root of bregman_P (R^2 != P)")

    # Formula 1: tr(Sigma) - tr(R) + (1/2) tr(Sigma^{-1} (P - Sigma^2))
    tr_sig = sum(sig_diag, ZERO)
    tr_R = mat_trace_q(R)
    tr_lin = sum(((P[i][i] - sig_diag[i] * sig_diag[i]) / sig_diag[i] for i in range(q)), ZERO)
    bregman_lhs = tr_sig - tr_R + HALF * tr_lin

    # Formula 2 (Eq. 2.2): (1/2) ||Sigma^{-1/2} (R - Sigma)||_F^2 = (1/2) sum_{i,j} (R_{ij} - sig_i delta_{ij})^2 / sig_i
    bregman_rhs = ZERO
    for i in range(q):
        for j in range(q):
            diff = R[i][j] - (sig_diag[i] if i == j else ZERO)
            bregman_rhs += (diff * diff) / sig_diag[i]
    bregman_rhs *= HALF
    if bregman_lhs != bregman_rhs or bregman_lhs < ZERO:
        raise CertificateError(f"Eq. (2.2) Bregman identity mismatch: lhs={bregman_lhs}, rhs={bregman_rhs}")

    # Exact Sec. 2.1 trace commutator identity: tr(H^2 L^2 - H L H L) = (1/2) ||HL - LH||_F^2 >= 0
    H = _parse_rat_mat(cert["comm_H"], q, q, "comm_H")
    L = _parse_rat_mat(cert["comm_L"], q, q, "comm_L")
    if not is_symmetric_q(H) or not is_symmetric_q(L):
        raise CertificateError("comm_H and comm_L must be symmetric")
    H2 = mat_mul_q(H, H)
    L2 = mat_mul_q(L, L)
    HL = mat_mul_q(H, L)
    LH = mat_mul_q(L, H)
    gap_lhs = mat_trace_q(mat_mul_q(H2, L2)) - mat_trace_q(mat_mul_q(HL, HL))
    gap_rhs = HALF * mat_frob_sq_q(mat_sub_q(HL, LH))
    if gap_lhs != gap_rhs or gap_lhs < ZERO:
        raise CertificateError(f"Trace commutator identity failed: lhs={gap_lhs}, rhs={gap_rhs}")

    if _parse_rat(cert["claimed_total_variance_tau"], "claimed_total_variance_tau") != tau_w:
        raise CertificateError(f"claimed_total_variance_tau mismatch: exact={tau_w}")
    if _parse_rat(cert["claimed_hollow_energy"], "claimed_hollow_energy") != hollow_energy:
        raise CertificateError(f"claimed_hollow_energy mismatch: exact={hollow_energy}")
    if _parse_rat(cert["claimed_bregman_div"], "claimed_bregman_div") != bregman_lhs:
        raise CertificateError(f"claimed_bregman_div mismatch: exact={bregman_lhs}")
    if _parse_rat(cert["claimed_commutator_trace_gap"], "claimed_commutator_trace_gap") != gap_lhs:
        raise CertificateError(f"claimed_commutator_trace_gap mismatch: exact={gap_lhs}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "tau_w": format_rat(tau_w),
        "hollow_energy": format_rat(hollow_energy),
        "bregman_div": format_rat(bregman_lhs),
        "commutator_gap": format_rat(gap_lhs),
    }


# =============================================================================
# Mode 3: Thm. 1.1 & Prop. A.3 Monochromatic Rectangle, Rank-Split & Balancing
# =============================================================================


def _verify_mode3(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "cert_id",
        "m", "n", "matrix_M",
        "rect_rows_A", "rect_cols_B", "mono_value",
        "protocol_leaves_L",
        "claimed_rank_M", "claimed_rank_ABc", "claimed_rank_AcB",
        "claimed_rect_density", "claimed_balanced_depth_ub",
    }
    _check_keys(cert, req, "Mode 3")
    m = _parse_int(cert["m"], "m")
    n = _parse_int(cert["n"], "n")
    if not (2 <= m <= 32 and 2 <= n <= 32):
        raise CertificateError("Mode 3 requires 2 <= m, n <= 32")

    raw_M = cert["matrix_M"]
    if type(raw_M) is not list or len(raw_M) != m:
        raise CertificateError("matrix_M row count mismatch")
    M: MatQ = []
    for i in range(m):
        row = raw_M[i]
        if type(row) is not list or len(row) != n:
            raise CertificateError(f"matrix_M[{i}] column count mismatch")
        qrow: VecQ = []
        for j in range(n):
            v = _parse_int(row[j], f"matrix_M[{i}][{j}]")
            if v not in (0, 1):
                raise CertificateError(f"matrix_M[{i}][{j}] must be 0 or 1")
            qrow.append(Fraction(v, 1))
        M.append(qrow)

    mono_val = _parse_int(cert["mono_value"], "mono_value")
    if mono_val not in (0, 1):
        raise CertificateError("mono_value must be 0 or 1")

    raw_A = cert["rect_rows_A"]
    raw_B = cert["rect_cols_B"]
    if type(raw_A) is not list or type(raw_B) is not list or not raw_A or not raw_B:
        raise CertificateError("rect_rows_A and rect_cols_B must be non-empty lists")
    rows_A = [_parse_int(r, "rect_rows_A") for r in raw_A]
    cols_B = [_parse_int(c, "rect_cols_B") for c in raw_B]
    if rows_A != sorted(set(rows_A)) or any(not (0 <= r < m) for r in rows_A):
        raise CertificateError("rect_rows_A must be strictly increasing valid row indices")
    if cols_B != sorted(set(cols_B)) or any(not (0 <= c < n) for c in cols_B):
        raise CertificateError("rect_cols_B must be strictly increasing valid col indices")

    # Verify exact monochromaticity on A x B
    target_q = Fraction(mono_val, 1)
    for r in rows_A:
        for c in cols_B:
            if M[r][c] != target_q:
                raise CertificateError(f"Rectangle A x B not monochromatic at ({r}, {c})")

    rows_Ac = [r for r in range(m) if r not in rows_A]
    cols_Bc = [c for c in range(n) if c not in cols_B]

    rk_M = rank_exact_q(M)
    if rk_M < 1:
        raise CertificateError("matrix_M must have rank >= 1")
    M_ABc = [[M[r][c] for c in cols_Bc] for r in rows_A] if cols_Bc else []
    M_AcB = [[M[r][c] for c in cols_B] for r in rows_Ac] if rows_Ac else []
    rk_ABc = rank_exact_q(M_ABc)
    rk_AcB = rank_exact_q(M_AcB)

    # Verify Prop. A.3 monochromatic rank-split inequality: rank(M|_{A x B^c}) + rank(M|_{A^c x B}) <= r_M + 1
    if rk_ABc + rk_AcB > rk_M + 1:
        raise CertificateError(f"Prop. A.3 rank-split violated: {rk_ABc} + {rk_AcB} > {rk_M + 1}")
    if rk_M >= 2 and min(rk_ABc, rk_AcB) > (3 * rk_M) // 4:
        raise CertificateError("Prop. A.3 min-rank <= floor(3r/4) violated")

    density = Fraction(len(rows_A) * len(cols_B), m * n)
    # Since C = 238 and r^{1/2 - eps} >= 1 for r >= 1, density >= 2^{-238} strictly certifies Thm. 1.1(1)
    if density * (1 << 238) < ONE:
        raise CertificateError("Rectangle density violates Thm. 1.1(1) lower bound 2^{-238}")

    L_leaves = _parse_int(cert["protocol_leaves_L"], "protocol_leaves_L")
    if not (1 <= L_leaves <= 1000000):
        raise CertificateError("protocol_leaves_L out of bounds")
    bal_depth = 2 * ceil_log_three_halves(L_leaves)

    if _parse_int(cert["claimed_rank_M"], "claimed_rank_M") != rk_M:
        raise CertificateError(f"claimed_rank_M mismatch: exact={rk_M}")
    if _parse_int(cert["claimed_rank_ABc"], "claimed_rank_ABc") != rk_ABc:
        raise CertificateError(f"claimed_rank_ABc mismatch: exact={rk_ABc}")
    if _parse_int(cert["claimed_rank_AcB"], "claimed_rank_AcB") != rk_AcB:
        raise CertificateError(f"claimed_rank_AcB mismatch: exact={rk_AcB}")
    if _parse_rat(cert["claimed_rect_density"], "claimed_rect_density") != density:
        raise CertificateError(f"claimed_rect_density mismatch: exact={density}")
    if _parse_int(cert["claimed_balanced_depth_ub"], "claimed_balanced_depth_ub") != bal_depth:
        raise CertificateError(f"claimed_balanced_depth_ub mismatch: exact={bal_depth}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "rank_M": rk_M,
        "rank_split": f"{rk_ABc}+{rk_AcB}<={rk_M+1}",
        "density": format_rat(density),
        "balanced_depth_ub": bal_depth,
    }


# =============================================================================
# Mode 4: Eq. (1.7) Variational Penalty & Prop. A.3 / Thm. 1.1 Recursion Audit
# =============================================================================


def _verify_mode4(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "cert_id",
        "C0", "eps_q", "t_probes", "rank_k_samples",
        "claimed_C_prime", "claimed_max_g_prime", "claimed_min_midpoint_excess",
        "claimed_orbit_lengths",
    }
    _check_keys(cert, req, "Mode 4")
    C0 = _parse_int(cert["C0"], "C0")
    if not (1 <= C0 <= 10000):
        raise CertificateError("C0 must be in [1, 10000]")
    eps_q = _parse_rat(cert["eps_q"], "eps_q")
    if not (ZERO < eps_q <= Fraction(1, 4)):
        raise CertificateError("eps_q must lie in (0, 1/4]")

    raw_t = cert["t_probes"]
    if type(raw_t) is not list or not (2 <= len(raw_t) <= 32):
        raise CertificateError("t_probes must have length in [2, 32]")
    ts = [_parse_rat(raw_t[i], f"t_probes[{i}]") for i in range(len(raw_t))]
    for i in range(len(ts)):
        if not (-ONE <= ts[i] <= ONE):
            raise CertificateError(f"t_probes[{i}]={ts[i]} outside [-1, 1]")
        if i > 0 and ts[i] <= ts[i - 1]:
            raise CertificateError("t_probes must be strictly increasing")

    # Verify Eq. (1.7) penalty g'(t) <= -1 and exact midpoint strict concavity excess (1/16)(t_i - t_j)^2
    max_gp = max(penalty_g_prime_q(t) for t in ts)
    if max_gp > -ONE:
        raise CertificateError(f"Eq. (1.7) slope bound g'(t) <= -1 violated: max={max_gp}")
    min_excess: Fraction | None = None
    for i in range(len(ts)):
        for j in range(i + 1, len(ts)):
            mid = (ts[i] + ts[j]) * HALF
            excess = penalty_g_q(mid) - HALF * (penalty_g_q(ts[i]) + penalty_g_q(ts[j]))
            expected = Fraction(1, 16) * (ts[i] - ts[j]) ** 2
            if excess != expected or excess <= ZERO:
                raise CertificateError(f"Eq. (1.7) midpoint concavity mismatch at ({i}, {j})")
            if min_excess is None or excess < min_excess:
                min_excess = excess
    assert min_excess is not None

    # Verify Prop. A.3 exact integer constants: 2^11 < 3^7 and 3*29^4 < 4*27^4
    if not ((1 << 11) < 3 ** 7 and 3 * (29 ** 4) < 4 * (27 ** 4)):
        raise CertificateError("Prop. A.3 integer contraction constants failed")
    C_prime = 750 * C0

    raw_ks = cert["rank_k_samples"]
    if type(raw_ks) is not list or not (1 <= len(raw_ks) <= 16):
        raise CertificateError("rank_k_samples must have length in [1, 16]")
    ks = [_parse_int(k, "rank_k_samples") for k in raw_ks]
    if any(not (2 <= k <= 10 ** 9) for k in ks):
        raise CertificateError("rank_k_samples entries must be in [2, 10^9]")
    orbit_lens = [len(rank_halving_orbit(k)) - 1 for k in ks]

    if _parse_int(cert["claimed_C_prime"], "claimed_C_prime") != C_prime:
        raise CertificateError(f"claimed_C_prime mismatch: exact={C_prime}")
    if _parse_rat(cert["claimed_max_g_prime"], "claimed_max_g_prime") != max_gp:
        raise CertificateError(f"claimed_max_g_prime mismatch: exact={max_gp}")
    if _parse_rat(cert["claimed_min_midpoint_excess"], "claimed_min_midpoint_excess") != min_excess:
        raise CertificateError(f"claimed_min_midpoint_excess mismatch: exact={min_excess}")
    raw_ol = cert["claimed_orbit_lengths"]
    if type(raw_ol) is not list or [_parse_int(x, "orbit_len") for x in raw_ol] != orbit_lens:
        raise CertificateError(f"claimed_orbit_lengths mismatch: exact={orbit_lens}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "C_prime": C_prime,
        "max_g_prime": format_rat(max_gp),
        "min_midpoint_excess": format_rat(min_excess),
        "orbit_lengths": orbit_lens,
    }


def verify_certificate(cert: Dict[str, Any]) -> Dict[str, Any]:
    if type(cert) is not dict:
        raise CertificateError("Certificate root must be a JSON object")
    _validate_ast(cert)
    if cert.get("schema") != SCHEMA_VERSION:
        raise CertificateError(f"Unsupported schema: {cert.get('schema')!r}")
    cid = cert.get("cert_id")
    if type(cid) is not str or not cid.strip() or len(cid) > 128:
        raise CertificateError("cert_id must be non-empty string of length <= 128")
    mode = cert.get("mode")
    if mode == "boolean_sign_third_moment_cert":
        return _verify_mode1(cert)
    if mode == "quadratic_slice_bregman_cert":
        return _verify_mode2(cert)
    if mode == "monochromatic_rank_split_cert":
        return _verify_mode3(cert)
    if mode == "nw_recursion_and_penalty_cert":
        return _verify_mode4(cert)
    raise CertificateError(f"Unknown verification mode: {mode!r}")


def verify_certificate_json_text(raw_text: str) -> Dict[str, Any]:
    try:
        obj = json.loads(
            raw_text,
            parse_float=_deny_ieee754,
            parse_constant=_reject_constant,
            object_pairs_hook=_reject_duplicate_keys,
        )
    except CertificateError:
        raise
    except Exception as exc:
        raise CertificateError(f"JSON parse error: {exc}") from exc
    return verify_certificate(obj)


def verify_certificate_file(path: Path) -> Dict[str, Any]:
    return verify_certificate_json_text(path.read_text(encoding="utf-8"))
