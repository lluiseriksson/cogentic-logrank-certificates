"""Generate all 16 canonical LOGRANK-COGENTIC-CERT-1.0 certificates and 4 exact-Q
experimental studies for Paper 58 (Google Research Cogentic, Nov 25, 2026:
"Breaking the Square-Root Barrier for the Log-Rank Conjecture").

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Sequence

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.logrank_certifier import SCHEMA_VERSION, verify_certificate
from src.logrank_exact import (
    HALF,
    ONE,
    ZERO,
    MatQ,
    VecQ,
    ceil_log_three_halves,
    doubly_center_q,
    format_rat,
    hollow_quadratic_slices_q,
    mat_frob_sq_q,
    mat_mul_q,
    mat_sub_q,
    mat_trace_q,
    penalty_g_prime_q,
    penalty_g_q,
    rank_exact_q,
    rank_halving_orbit,
    third_moment_energy_q,
)

CERT_DIR = ROOT / "certificates"
RES_DIR = ROOT / "results"


def _fmt_vec(v: Sequence[Fraction]) -> List[str]:
    return [format_rat(x) for x in v]


def _fmt_mat(M: Sequence[Sequence[Fraction]]) -> List[List[str]]:
    return [_fmt_vec(row) for row in M]


def _walsh_rows(bits: int) -> List[List[int]]:
    n = 1 << bits
    rows: List[List[int]] = []
    for mask in range(n):
        row = [1 if (bin(mask & y).count("1") % 2 == 0) else -1 for y in range(n)]
        rows.append(row)
    return rows


def _make_mode1_eq(cert_id: str, bits: int) -> Dict[str, Any]:
    """Exact biased Boolean Equality sign matrix S = J_n - 2 I_n of size n = 2^bits."""
    n = 1 << bits
    S: MatQ = [[-ONE if i == j else ONE for j in range(n)] for i in range(n)]
    mu = [Fraction(1, n)] * n
    s1 = Fraction(n - 2, n)
    u1 = [ONE] * n
    v1 = [ONE] * n
    W = _walsh_rows(bits)
    sigma = [Fraction(2, n)] * (n - 1)
    A_vecs: MatQ = [[Fraction(-v, 1) for v in W[k]] for k in range(1, n)]
    B_vecs: MatQ = [[Fraction(v, 1) for v in W[k]] for k in range(1, n)]
    e3, _ = third_moment_energy_q(sigma, B_vecs, mu)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "boolean_sign_third_moment_cert",
        "cert_id": cert_id,
        "is_rademacher_barrier": False,
        "m": n,
        "n": n,
        "matrix_S": _fmt_mat(S),
        "mu_X": _fmt_vec(mu),
        "mu_Y": _fmt_vec(mu),
        "s1": format_rat(s1),
        "u1": _fmt_vec(u1),
        "v1": _fmt_vec(v1),
        "sigma": _fmt_vec(sigma),
        "A_vecs": _fmt_mat(A_vecs),
        "B_vecs": _fmt_mat(B_vecs),
        "claimed_rank_S": rank_exact_q(S),
        "claimed_bias_mu0": format_rat(s1),
        "claimed_eq16_max_residual": "0",
        "claimed_third_moment_energy": format_rat(e3),
        "claimed_projection_checks": (n - 1) * n,
    }


def _make_mode1_hadamard4(cert_id: str) -> Dict[str, Any]:
    """Exact 4x4 Sylvester Hadamard H_4: Boolean sign matrix with non-constant u1 = (2,0,0,0)."""
    W = _walsh_rows(2)
    S: MatQ = [[Fraction(v, 1) for v in row] for row in W]
    mu = [Fraction(1, 4)] * 4
    s1 = HALF
    u1 = [Fraction(2, 1), ZERO, ZERO, ZERO]
    v1 = [ONE, ONE, ONE, ONE]
    sigma = [HALF, HALF, HALF]
    A_vecs: MatQ = [
        [ZERO, Fraction(2, 1), ZERO, ZERO],
        [ZERO, ZERO, Fraction(2, 1), ZERO],
        [ZERO, ZERO, ZERO, Fraction(2, 1)],
    ]
    B_vecs: MatQ = [[Fraction(v, 1) for v in W[k]] for k in range(1, 4)]
    e3, _ = third_moment_energy_q(sigma, B_vecs, mu)
    bias = sum((mu[i] * mu[j] * S[i][j] for i in range(4) for j in range(4)), ZERO)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "boolean_sign_third_moment_cert",
        "cert_id": cert_id,
        "is_rademacher_barrier": False,
        "m": 4,
        "n": 4,
        "matrix_S": _fmt_mat(S),
        "mu_X": _fmt_vec(mu),
        "mu_Y": _fmt_vec(mu),
        "s1": format_rat(s1),
        "u1": _fmt_vec(u1),
        "v1": _fmt_vec(v1),
        "sigma": _fmt_vec(sigma),
        "A_vecs": _fmt_mat(A_vecs),
        "B_vecs": _fmt_mat(B_vecs),
        "claimed_rank_S": rank_exact_q(S),
        "claimed_bias_mu0": format_rat(bias),
        "claimed_eq16_max_residual": "0",
        "claimed_third_moment_energy": format_rat(e3),
        "claimed_projection_checks": 3 * 4,
    }


def _make_mode1_rademacher8(cert_id: str) -> Dict[str, Any]:
    """Exact Eq. (1.4) biased Rademacher barrier A_Rad(x,y) = 1/2 + (1/2) <x, y> on {-1,+1}^3:
    exact rank 4, bias 1/2, unit row/col L2 norms, identical spectrum (1/2,1/2,1/2,1/2) to Eq_4,
    yet ZERO third-moment energy E3 = 0 and nonzero Eq. (1.6) residual 3!"""
    pts = [[1 if ((i >> b) & 1) == 0 else -1 for b in range(3)] for i in range(8)]
    S: MatQ = [
        [HALF + HALF * Fraction(sum(pts[i][b] * pts[j][b] for b in range(3)), 1) for j in range(8)]
        for i in range(8)
    ]
    mu = [Fraction(1, 8)] * 8
    s1 = HALF
    u1 = [ONE] * 8
    v1 = [ONE] * 8
    sigma = [HALF, HALF, HALF]
    A_vecs: MatQ = [[Fraction(pts[i][b], 1) for i in range(8)] for b in range(3)]
    B_vecs: MatQ = [[Fraction(pts[j][b], 1) for j in range(8)] for b in range(3)]
    # Max residual of |S^2 - 1| is |2^2 - 1| = 3
    max_res = max(abs(S[i][j] * S[i][j] - ONE) for i in range(8) for j in range(8))
    return {
        "schema": SCHEMA_VERSION,
        "mode": "boolean_sign_third_moment_cert",
        "cert_id": cert_id,
        "is_rademacher_barrier": True,
        "m": 8,
        "n": 8,
        "matrix_S": _fmt_mat(S),
        "mu_X": _fmt_vec(mu),
        "mu_Y": _fmt_vec(mu),
        "s1": format_rat(s1),
        "u1": _fmt_vec(u1),
        "v1": _fmt_vec(v1),
        "sigma": _fmt_vec(sigma),
        "A_vecs": _fmt_mat(A_vecs),
        "B_vecs": _fmt_mat(B_vecs),
        "claimed_rank_S": rank_exact_q(S),
        "claimed_bias_mu0": "1/2",
        "claimed_eq16_max_residual": format_rat(max_res),
        "claimed_third_moment_energy": "0",
        "claimed_projection_checks": 0,
    }


def _make_mode2(
    cert_id: str,
    A: MatQ,
    mu_X: VecQ,
    mu_Y: VecQ,
    W: MatQ,
    R: MatQ,
    sig_diag: VecQ,
    H: MatQ,
    L: MatQ,
) -> Dict[str, Any]:
    m, n = len(A), len(A[0])
    d = len(W[0])
    q = len(R)
    P = mat_mul_q(R, R)
    Adc, _ = doubly_center_q(A, mu_X, mu_Y)
    tau_w = sum((mu_X[x] * sum((W[x][a] * W[x][a] for a in range(d)), ZERO) for x in range(m)), ZERO)
    slices = hollow_quadratic_slices_q(Adc, mu_X, W)
    hollow_e = sum((mu_Y[y] * mat_frob_sq_q(slices[y]) for y in range(n)), ZERO)

    bregman = HALF * sum(
        (((R[i][j] - (sig_diag[i] if i == j else ZERO)) ** 2) / sig_diag[i] for i in range(q) for j in range(q)),
        ZERO,
    )
    HL = mat_mul_q(H, L)
    LH = mat_mul_q(L, H)
    comm_gap = HALF * mat_frob_sq_q(mat_sub_q(HL, LH))

    return {
        "schema": SCHEMA_VERSION,
        "mode": "quadratic_slice_bregman_cert",
        "cert_id": cert_id,
        "m": m,
        "n": n,
        "d": d,
        "q": q,
        "matrix_A": _fmt_mat(A),
        "mu_X": _fmt_vec(mu_X),
        "mu_Y": _fmt_vec(mu_Y),
        "bulk_map_W": _fmt_mat(W),
        "bregman_P": _fmt_mat(P),
        "bregman_R": _fmt_mat(R),
        "bregman_sigma_diag": _fmt_vec(sig_diag),
        "comm_H": _fmt_mat(H),
        "comm_L": _fmt_mat(L),
        "claimed_total_variance_tau": format_rat(tau_w),
        "claimed_hollow_energy": format_rat(hollow_e),
        "claimed_bregman_div": format_rat(bregman),
        "claimed_commutator_trace_gap": format_rat(comm_gap),
    }


def _make_mode3(
    cert_id: str,
    M_int: List[List[int]],
    rows_A: List[int],
    cols_B: List[int],
    mono_val: int,
    L_leaves: int,
) -> Dict[str, Any]:
    m, n = len(M_int), len(M_int[0])
    M = [[Fraction(v, 1) for v in row] for row in M_int]
    rows_Ac = [r for r in range(m) if r not in rows_A]
    cols_Bc = [c for c in range(n) if c not in cols_B]
    rk_M = rank_exact_q(M)
    rk_ABc = rank_exact_q([[M[r][c] for c in cols_Bc] for r in rows_A]) if cols_Bc else 0
    rk_AcB = rank_exact_q([[M[r][c] for c in cols_B] for r in rows_Ac]) if rows_Ac else 0
    density = Fraction(len(rows_A) * len(cols_B), m * n)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "monochromatic_rank_split_cert",
        "cert_id": cert_id,
        "m": m,
        "n": n,
        "matrix_M": M_int,
        "rect_rows_A": rows_A,
        "rect_cols_B": cols_B,
        "mono_value": mono_val,
        "protocol_leaves_L": L_leaves,
        "claimed_rank_M": rk_M,
        "claimed_rank_ABc": rk_ABc,
        "claimed_rank_AcB": rk_AcB,
        "claimed_rect_density": format_rat(density),
        "claimed_balanced_depth_ub": 2 * ceil_log_three_halves(L_leaves),
    }


def _make_mode4(
    cert_id: str,
    C0: int,
    eps_q: Fraction,
    ts: List[Fraction],
    ks: List[int],
) -> Dict[str, Any]:
    max_gp = max(penalty_g_prime_q(t) for t in ts)
    min_ex = min(
        Fraction(1, 16) * (ts[i] - ts[j]) ** 2
        for i in range(len(ts))
        for j in range(i + 1, len(ts))
    )
    orbit_lens = [len(rank_halving_orbit(k)) - 1 for k in ks]
    return {
        "schema": SCHEMA_VERSION,
        "mode": "nw_recursion_and_penalty_cert",
        "cert_id": cert_id,
        "C0": C0,
        "eps_q": format_rat(eps_q),
        "t_probes": _fmt_vec(ts),
        "rank_k_samples": ks,
        "claimed_C_prime": 750 * C0,
        "claimed_max_g_prime": format_rat(max_gp),
        "claimed_min_midpoint_excess": format_rat(min_ex),
        "claimed_orbit_lengths": orbit_lens,
    }


def build_16_certificates() -> List[Dict[str, Any]]:
    certs: List[Dict[str, Any]] = []

    # --- Mode 1: 4 certs (Boolean sign third-moment SVD vs. Rademacher barrier) ---
    certs.append(_make_mode1_eq("m1_bool_eq4_third_moment", 2))
    certs.append(_make_mode1_eq("m1_bool_eq8_third_moment", 3))
    certs.append(_make_mode1_hadamard4("m1_bool_hadamard4_asym_u1"))
    certs.append(_make_mode1_rademacher8("m1_rademacher_barrier_8x8"))

    # --- Mode 2: 4 certs (Hollow quadratic slices, Matrix Sqrt Bregman, Commutator) ---
    W4 = _walsh_rows(2)
    S_eq4: MatQ = [[-ONE if i == j else ONE for j in range(4)] for i in range(4)]
    mu4 = [Fraction(1, 4)] * 4
    # Variance-weighted bulk map W on Eq_4 using the 3 Walsh singular vectors (sigma=1/2 -> scale 1/2)
    W_eq4: MatQ = [[Fraction(W4[k][x], 2) for k in range(1, 4)] for x in range(4)]
    certs.append(_make_mode2(
        "m2_slice_bregman_eq4_nonzero",
        S_eq4, mu4, mu4, W_eq4,
        R=[[Fraction(3, 4), Fraction(1, 4)], [Fraction(1, 4), Fraction(3, 4)]],
        sig_diag=[HALF, HALF],
        H=[[Fraction(2, 1), ONE], [ONE, Fraction(3, 1)]],
        L=[[ONE, Fraction(2, 1)], [Fraction(2, 1), Fraction(4, 1)]],
    ))

    # Eq_8 bulk map with 4 Walsh modes -> strictly larger hollow quadratic slice energy!
    W8 = _walsh_rows(3)
    S_eq8: MatQ = [[-ONE if i == j else ONE for j in range(8)] for i in range(8)]
    mu8 = [Fraction(1, 8)] * 8
    W_eq8: MatQ = [[Fraction(W8[k][x], 4) for k in range(1, 5)] for x in range(8)]
    certs.append(_make_mode2(
        "m2_slice_bregman_eq8_3x3",
        S_eq8, mu8, mu8, W_eq8,
        R=[
            [Fraction(5, 4), Fraction(1, 4), ZERO],
            [Fraction(1, 4), ONE, Fraction(1, 4)],
            [ZERO, Fraction(1, 4), Fraction(3, 4)],
        ],
        sig_diag=[ONE, HALF, Fraction(1, 4)],
        H=[[Fraction(3, 1), ONE, ZERO], [ONE, Fraction(2, 1), -ONE], [ZERO, -ONE, Fraction(4, 1)]],
        L=[[ONE, ZERO, Fraction(2, 1)], [ZERO, Fraction(3, 1), ONE], [Fraction(2, 1), ONE, Fraction(2, 1)]],
    ))

    # Rademacher barrier with linear Rademacher bulk map -> EXACT ZERO hollow quadratic slice energy!
    pts = [[1 if ((i >> b) & 1) == 0 else -1 for b in range(3)] for i in range(8)]
    S_rad8: MatQ = [
        [HALF + HALF * Fraction(sum(pts[i][b] * pts[j][b] for b in range(3)), 1) for j in range(8)]
        for i in range(8)
    ]
    W_rad8: MatQ = [[Fraction(pts[x][b], 2) for b in range(3)] for x in range(8)]
    certs.append(_make_mode2(
        "m2_slice_bregman_rademacher_zero",
        S_rad8, mu8, mu8, W_rad8,
        R=[[HALF, ZERO], [ZERO, HALF]],  # R == Sigma -> exact Bregman divergence 0!
        sig_diag=[HALF, HALF],
        H=[[Fraction(2, 1), ZERO], [ZERO, Fraction(5, 1)]],
        L=[[Fraction(3, 1), ZERO], [ZERO, Fraction(7, 1)]],  # commuting -> commutator gap 0!
    ))

    # 4x4 Bregman & non-commuting symmetric matrices on Hadamard H_4
    S_h4: MatQ = [[Fraction(v, 1) for v in row] for row in W4]
    W_h4: MatQ = [[Fraction(W4[k][x], 2) for k in range(1, 4)] for x in range(4)]
    certs.append(_make_mode2(
        "m2_slice_bregman_hadamard4_4x4",
        S_h4, mu4, mu4, W_h4,
        R=[
            [ONE, Fraction(1, 4), ZERO, ZERO],
            [Fraction(1, 4), ONE, Fraction(1, 4), ZERO],
            [ZERO, Fraction(1, 4), Fraction(3, 4), Fraction(1, 4)],
            [ZERO, ZERO, Fraction(1, 4), Fraction(3, 4)],
        ],
        sig_diag=[HALF, HALF, HALF, HALF],
        H=[
            [Fraction(2, 1), ONE, ZERO, ZERO],
            [ONE, Fraction(3, 1), ONE, ZERO],
            [ZERO, ONE, Fraction(4, 1), ONE],
            [ZERO, ZERO, ONE, Fraction(5, 1)],
        ],
        L=[
            [ONE, ZERO, ONE, ZERO],
            [ZERO, Fraction(2, 1), ZERO, ONE],
            [ONE, ZERO, Fraction(3, 1), ZERO],
            [ZERO, ONE, ZERO, Fraction(4, 1)],
        ],
    ))

    # --- Mode 3: 4 certs (Monochromatic Rectangles, Rank-Split <= r+1, Protocol Balancing) ---
    M_eq8 = [[1 if i == j else 0 for j in range(8)] for i in range(8)]
    certs.append(_make_mode3("m3_rect_eq8_zero_block", M_eq8, [0, 1, 2, 3], [4, 5, 6, 7], 0, 15))

    M_disj3 = [[1 if (i & j) == 0 else 0 for j in range(8)] for i in range(8)]
    # Rows with bit 0 == 1 ([1,3,5,7]) and cols with bit 0 == 1 ([1,3,5,7]) form a 4x4 0-monochromatic rectangle!
    certs.append(_make_mode3("m3_rect_disj3_8x8", M_disj3, [1, 3, 5, 7], [1, 3, 5, 7], 0, 27))

    # 12x12 Boolean matrix with a 4x4 1-monochromatic block A=[0..3], B=[0..3] testing the +1 slack!
    M_one12 = [[0 for _ in range(12)] for _ in range(12)]
    for i in range(4):
        for j in range(4):
            M_one12[i][j] = 1
    for i in range(4):
        M_one12[i][4 + i] = 1
    for j in range(4):
        M_one12[4 + j][j] = 1
    for k in range(4):
        M_one12[8 + k][8 + k] = 1
    certs.append(_make_mode3("m3_rect_one_block_12x12", M_one12, [0, 1, 2, 3], [0, 1, 2, 3], 1, 64))

    M_gt4 = [[1 if i > j else 0 for j in range(16)] for i in range(16)]
    certs.append(_make_mode3("m3_rect_gt4_16x16", M_gt4, list(range(8)), list(range(8, 16)), 0, 31))

    # --- Mode 4: 4 certs (Eq. 1.7 Concave Penalty & Prop. A.3 / Thm. 1.1 Recursion) ---
    certs.append(_make_mode4(
        "m4_nw_cogentic_thm11_canonical",
        238, Fraction(1, 200000),
        [Fraction(-1, 1), Fraction(-1, 2), ZERO, Fraction(1, 4), HALF, Fraction(3, 4), ONE],
        [2, 8, 64, 1024, 65536, 1000000],
    ))
    certs.append(_make_mode4(
        "m4_nw_fine_penalty_grid_17pts",
        238, Fraction(1, 200000),
        [Fraction(-8 + i, 8) for i in range(17)],
        [4, 16, 256, 4096],
    ))
    certs.append(_make_mode4(
        "m4_nw_high_rank_orbit_1e9",
        238, Fraction(1, 200000),
        [Fraction(-1, 1), ZERO, HALF, ONE],
        [1000, 100000, 10000000, 1000000000],
    ))
    certs.append(_make_mode4(
        "m4_nw_unit_C0_propa3_exact",
        1, Fraction(1, 4),
        [Fraction(-1, 1), Fraction(-1, 3), Fraction(1, 3), ONE],
        [2, 3, 5, 10, 100, 10000],
    ))

    assert len(certs) == 16
    return certs


def main() -> None:
    CERT_DIR.mkdir(parents=True, exist_ok=True)
    RES_DIR.mkdir(parents=True, exist_ok=True)

    certs = build_16_certificates()
    atlas_rows: List[Dict[str, Any]] = []
    for cert in certs:
        p = CERT_DIR / f"{cert['cert_id']}.cert.json"
        p.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        # Warm-up + 7-run exact mean
        res = verify_certificate(cert)
        assert res["verified"] is True
        ts: List[float] = []
        for _ in range(7):
            t0 = time.perf_counter()
            verify_certificate(cert)
            ts.append((time.perf_counter() - t0) * 1000.0)
        atlas_rows.append({
            "cert_id": cert["cert_id"],
            "mode": cert["mode"],
            "mean_ms": round(sum(ts) / len(ts), 3),
            "summary": res,
        })

    (RES_DIR / "exp1_certificate_atlas.json").write_text(
        json.dumps({"count": len(atlas_rows), "certificates": atlas_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # Exp 2: Exact third-moment energy E_3 = (n-1)(n-2) * (2/n)^2 = 4(n-1)(n-2)/n^2 for Eq_n (n=2^b) vs. 0 for Rademacher!
    exp2_rows = []
    for b in range(2, 9):
        n = 1 << b
        e3_q = Fraction(4 * (n - 1) * (n - 2), n * n)
        bias_q = Fraction(n - 2, n)
        exp2_rows.append({
            "bits": b,
            "n": n,
            "bias_exact": format_rat(bias_q),
            "bias_val": float(bias_q),
            "bool_third_moment_exact": format_rat(e3_q),
            "bool_third_moment_val": float(e3_q),
            "rademacher_third_moment_val": 0.0,
        })
    (RES_DIR / "exp2_third_moment_separation.json").write_text(
        json.dumps({"rows": exp2_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # Exp 3: Eq. (1.7) Variational Penalty g(t) & exact midpoint concavity excess across [-1, 1]
    exp3_rows = []
    for i in range(21):
        t = Fraction(-10 + i, 10)
        g = penalty_g_q(t)
        gp = penalty_g_prime_q(t)
        exp3_rows.append({
            "t_exact": format_rat(t),
            "t_val": float(t),
            "g_exact": format_rat(g),
            "g_val": float(g),
            "g_prime_exact": format_rat(gp),
            "g_prime_val": float(gp),
        })
    (RES_DIR / "exp3_variational_penalty_curve.json").write_text(
        json.dumps({"rows": exp3_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # Exp 4: Prop. A.3 Rank-Halving Orbit Steps & Asymptotic Exponent Separation r^{1/2 - 5e-6} vs sqrt(r) vs sqrt(r) log r
    exp4_rows = []
    for p10 in range(1, 10):
        r = 10 ** p10
        steps = len(rank_halving_orbit(r)) - 1
        # Exact ratio of Cogentic exponent vs sqrt(r): r^{-5e-6} (computed for plotting in exp JSON only, never in src/)
        exp4_rows.append({
            "log10_r": p10,
            "r": r,
            "orbit_steps": steps,
            "balanced_depth_L_eq_r": 2 * ceil_log_three_halves(r),
            "subsqrt_factor": r ** (-5e-6),
        })
    (RES_DIR / "exp4_nw_orbit_and_scaling.json").write_text(
        json.dumps({"rows": exp4_rows}, indent=2) + "\n", encoding="utf-8"
    )

    print(f"[PASS] Generated 16 canonical LOGRANK-COGENTIC-CERT-1.0 certificates and 4 result JSONs.")
    for r in atlas_rows:
        print(f"  {r['cert_id']:36s}  {r['mean_ms']:6.3f} ms  {r['summary']}")


if __name__ == "__main__":
    main()
