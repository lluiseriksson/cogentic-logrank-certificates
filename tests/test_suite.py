"""66-test pytest suite (1 test covering all 16 canonical certs + 3 raw-JSON parser tests
+ 62 parametrized live adversarial forgery attacks, with exact branch assertions) for
Paper 58 (LOGRANK-COGENTIC-CERT-1.0).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any, Callable, Dict, List, Tuple

import pytest

from src.logrank_certifier import (
    CertificateError,
    verify_certificate,
    verify_certificate_file,
    verify_certificate_json_text,
)

ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = ROOT / "certificates"


def _load(stem: str) -> Dict[str, Any]:
    return json.loads((CERT_DIR / f"{stem}.cert.json").read_text(encoding="utf-8"))


def test_all_16_canonical_certificates_pass() -> None:
    paths = sorted(CERT_DIR.glob("*.cert.json"))
    assert len(paths) == 16
    for p in paths:
        res = verify_certificate_file(p)
        assert res["verified"] is True


def test_raw_json_rejects_ieee754_float() -> None:
    raw = json.dumps(_load("m1_bool_eq4_third_moment")).replace('"1/2"', "0.5", 1)
    with pytest.raises(CertificateError, match="floating-point"):
        verify_certificate_json_text(raw)


def test_raw_json_rejects_nan_infinity() -> None:
    raw = '{"schema": "LOGRANK-COGENTIC-CERT-1.0", "mode": "nw_recursion_and_penalty_cert", "cert_id": "x", "C0": NaN}'
    with pytest.raises(CertificateError, match="Non-finite"):
        verify_certificate_json_text(raw)


def test_raw_json_rejects_duplicate_keys() -> None:
    raw = '{"schema": "LOGRANK-COGENTIC-CERT-1.0", "schema": "LOGRANK-COGENTIC-CERT-1.0", "mode": "nw_recursion_and_penalty_cert", "cert_id": "x"}'
    with pytest.raises(CertificateError, match="Duplicate"):
        verify_certificate_json_text(raw)


def _build_62_attacks() -> List[Tuple[str, str, Callable[[], Dict[str, Any]]]]:
    m1 = _load("m1_bool_eq4_third_moment")
    m1_eq8 = _load("m1_bool_eq8_third_moment")
    m1_rad = _load("m1_rademacher_barrier_8x8")
    m2 = _load("m2_slice_bregman_eq4_nonzero")
    m2_rad = _load("m2_slice_bregman_rademacher_zero")
    m3 = _load("m3_rect_eq8_zero_block")
    m4 = _load("m4_nw_cogentic_thm11_canonical")

    def _swap_top_mode(c: Dict[str, Any]) -> None:
        c["s1"], c["sigma"][0] = c["sigma"][0], c["s1"]
        c["u1"], c["A_vecs"][0] = c["A_vecs"][0], c["u1"]
        c["v1"], c["B_vecs"][0] = c["B_vecs"][0], c["v1"]
        c["claimed_third_moment_energy"] = "75/16"

    def _neg_sqrt_root(c: Dict[str, Any]) -> None:
        c["bregman_R"] = [["-1/2", "0"], ["0", "-1/2"]]
        c["claimed_bregman_div"] = "2"

    def mod(base: Dict[str, Any], fn: Callable[[Dict[str, Any]], None]) -> Callable[[], Dict[str, Any]]:
        def _run() -> Dict[str, Any]:
            c = copy.deepcopy(base)
            fn(c)
            return c
        return _run

    attacks: List[Tuple[str, str, Callable[[], Dict[str, Any]]]] = [
        # --- 12 Schema / Parser / AST Attacks ---
        ("S01_wrong_schema", "Unsupported schema", mod(m1, lambda c: c.__setitem__("schema", "LOGRANK-0.9"))),
        ("S02_unknown_mode", "Unknown verification mode", mod(m1, lambda c: c.__setitem__("mode", "bogus"))),
        ("S03_empty_cert_id", "cert_id", mod(m1, lambda c: c.__setitem__("cert_id", "   "))),
        ("S04_non_reduced_rat", "unreduced", mod(m1, lambda c: c.__setitem__("s1", "2/4"))),
        ("S05_leading_zero_rat", "leading zero", mod(m1, lambda c: c.__setitem__("s1", "01/2"))),
        ("S06_negative_zero_rat", "negative zero", mod(m1, lambda c: c.__setitem__("claimed_eq16_max_residual", "-0"))),
        ("S07_plus_sign_rat", "leading '\\+'", mod(m1, lambda c: c.__setitem__("s1", "+1/2"))),
        ("S08_unicode_digit_rat", "non-ASCII", mod(m1, lambda c: c.__setitem__("s1", "١/2"))),
        ("S09_int_in_rat_field", "canonical rational str", mod(m1, lambda c: c.__setitem__("s1", 1))),
        ("S10_bool_in_int_field", "strict int", mod(m1, lambda c: c.__setitem__("m", True))),
        ("S11_oversized_rat_str", "exceeds cap", mod(m1, lambda c: c.__setitem__("s1", "1" + "0" * 2005))),
        ("S12_denom_one_rat", "denominator must be >= 2", mod(m1, lambda c: c.__setitem__("s1", "1/1"))),

        # --- 12 Mode 1 (Sec. 1.2 & Eq. (1.6) Boolean Sign Third-Moment SVD) Forgeries ---
        ("M1_01_non_boolean_entry", "not in", mod(m1, lambda c: c["matrix_S"][0].__setitem__(0, "2"))),
        ("M1_02_prob_not_sum_1", "must sum to 1", mod(m1, lambda c: c["mu_X"].__setitem__(0, "1/2"))),
        ("M1_03_prob_nonpositive", "strictly positive", mod(m1, lambda c: c["mu_X"].__setitem__(0, "0"))),
        ("M1_04_s1_nonpositive", "strictly positive", mod(m1, lambda c: c.__setitem__("s1", "0"))),
        ("M1_05_sigma_unsorted", "non-increasing", mod(m1, lambda c: c["sigma"].__setitem__(1, "1"))),
        ("M1_06_u_not_orthonormal", "orthonormality", mod(m1, lambda c: c["u1"].__setitem__(0, "2"))),
        ("M1_07_v_not_orthonormal", "orthonormality", mod(m1, lambda c: c["B_vecs"][0].__setitem__(0, "2"))),
        ("M1_08_svd_recon_mismatch", "reconstruction mismatch", mod(m1, lambda c: c.__setitem__("sigma", ["1/3", "1/3", "1/3"]))),
        ("M1_09_forged_rank_S", "claimed_rank_S", mod(m1, lambda c: c.__setitem__("claimed_rank_S", 3))),
        ("M1_10_forged_bias", "claimed_bias_mu0", mod(m1, lambda c: c.__setitem__("claimed_bias_mu0", "1/4"))),
        ("M1_11_forged_e3_energy", "claimed_third_moment_energy", mod(m1, lambda c: c.__setitem__("claimed_third_moment_energy", "0"))),
        ("M1_12_rad_nonunit_l2", "unit L\\^2", mod(m1_rad, lambda c: (
            c.__setitem__("s1", "1"),
            c.__setitem__("matrix_S", [[f"{2 * int(v) + 1}/2" for v in row] for row in c["matrix_S"]]),
        ))),
        ("M1_13_s1_lt_sigma0_swap", "s1 >= sigma\\[0\\]", mod(m1_eq8, _swap_top_mode)),

        # --- 13 Mode 2 (Sec. 2.1-2.2 Hollow Slices, Matrix Sqrt Bregman & Commutator) Forgeries ---
        ("M2_01_d_out_of_bounds", "dimensions out of bounds", mod(m2, lambda c: c.__setitem__("d", 1))),
        ("M2_02_P_asymmetric", "must be symmetric", mod(m2, lambda c: c["bregman_P"][0].__setitem__(1, "1"))),
        ("M2_03_R_asymmetric", "must be symmetric", mod(m2, lambda c: c["bregman_R"][0].__setitem__(1, "1/2"))),
        ("M2_04_R_sq_ne_P", "matrix square root", mod(m2, lambda c: c["bregman_P"][0].__setitem__(0, "1"))),
        ("M2_05_sigma_nonpositive", "strictly positive", mod(m2, lambda c: c["bregman_sigma_diag"].__setitem__(0, "0"))),
        ("M2_06_H_asymmetric", "must be symmetric", mod(m2, lambda c: c["comm_H"][0].__setitem__(1, "9"))),
        ("M2_07_L_asymmetric", "must be symmetric", mod(m2, lambda c: c["comm_L"][0].__setitem__(1, "9"))),
        ("M2_08_forged_tau", "claimed_total_variance_tau", mod(m2, lambda c: c.__setitem__("claimed_total_variance_tau", "1"))),
        ("M2_09_forged_hollow", "claimed_hollow_energy", mod(m2, lambda c: c.__setitem__("claimed_hollow_energy", "0"))),
        ("M2_10_forged_bregman", "claimed_bregman_div", mod(m2, lambda c: c.__setitem__("claimed_bregman_div", "0"))),
        ("M2_11_forged_comm_gap", "claimed_commutator_trace_gap", mod(m2, lambda c: c.__setitem__("claimed_commutator_trace_gap", "0"))),
        ("M2_12_extra_key", "schema key mismatch", mod(m2, lambda c: c.__setitem__("extra", 1))),
        ("M2_13_R_non_psd_neg_root", "positive semidefinite", mod(m2_rad, _neg_sqrt_root)),

        # --- 12 Mode 3 (Thm. 1.1 & Prop. A.3 Monochromatic Rectangle & Rank-Split) Forgeries ---
        ("M3_01_non_binary_M", "must be 0 or 1", mod(m3, lambda c: c["matrix_M"][0].__setitem__(0, 2))),
        ("M3_02_bad_mono_val", "mono_value", mod(m3, lambda c: c.__setitem__("mono_value", 2))),
        ("M3_03_empty_rect_A", "non-empty", mod(m3, lambda c: c.__setitem__("rect_rows_A", []))),
        ("M3_04_unsorted_rect_B", "strictly increasing", mod(m3, lambda c: c.__setitem__("rect_cols_B", [5, 4, 6, 7]))),
        ("M3_05_non_monochromatic", "not monochromatic", mod(m3, lambda c: c.__setitem__("rect_cols_B", [0, 4, 5, 6]))),
        ("M3_06_zero_matrix", "rank >= 1", mod(m3, lambda c: c.__setitem__("matrix_M", [[0] * 8 for _ in range(8)]))),
        ("M3_07_leaves_zero", "protocol_leaves_L", mod(m3, lambda c: c.__setitem__("protocol_leaves_L", 0))),
        ("M3_08_forged_rank_M", "claimed_rank_M", mod(m3, lambda c: c.__setitem__("claimed_rank_M", 7))),
        ("M3_09_forged_rank_ABc", "claimed_rank_ABc", mod(m3, lambda c: c.__setitem__("claimed_rank_ABc", 3))),
        ("M3_10_forged_rank_AcB", "claimed_rank_AcB", mod(m3, lambda c: c.__setitem__("claimed_rank_AcB", 3))),
        ("M3_11_forged_density", "claimed_rect_density", mod(m3, lambda c: c.__setitem__("claimed_rect_density", "1/2"))),
        ("M3_12_forged_depth", "claimed_balanced_depth_ub", mod(m3, lambda c: c.__setitem__("claimed_balanced_depth_ub", 12))),

        # --- 12 Mode 4 (Eq. (1.7) Concave Penalty & Prop. A.3 Recursion) Forgeries ---
        ("M4_01_C0_zero", "C0 must be", mod(m4, lambda c: c.__setitem__("C0", 0))),
        ("M4_02_eps_zero", "eps_q must lie", mod(m4, lambda c: c.__setitem__("eps_q", "0"))),
        ("M4_03_eps_too_large", "eps_q must lie", mod(m4, lambda c: c.__setitem__("eps_q", "1/3"))),
        ("M4_04_t_out_of_range", "outside \\[-1, 1\\]", mod(m4, lambda c: c["t_probes"].__setitem__(0, "-2"))),
        ("M4_05_t_not_increasing", "strictly increasing", mod(m4, lambda c: c["t_probes"].__setitem__(1, "-1"))),
        ("M4_06_t_too_short", "length in \\[2, 32\\]", mod(m4, lambda c: c.__setitem__("t_probes", ["0"]))),
        ("M4_07_k_too_small", "rank_k_samples", mod(m4, lambda c: c["rank_k_samples"].__setitem__(0, 1))),
        ("M4_08_forged_C_prime", "claimed_C_prime", mod(m4, lambda c: c.__setitem__("claimed_C_prime", 178000))),
        ("M4_09_forged_max_gp", "claimed_max_g_prime", mod(m4, lambda c: c.__setitem__("claimed_max_g_prime", "-2"))),
        ("M4_10_forged_min_ex", "claimed_min_midpoint_excess", mod(m4, lambda c: c.__setitem__("claimed_min_midpoint_excess", "0"))),
        ("M4_11_forged_orbits", "claimed_orbit_lengths", mod(m4, lambda c: c["claimed_orbit_lengths"].__setitem__(0, 9))),
        ("M4_12_missing_key", "schema key mismatch", mod(m4, lambda c: c.pop("C0"))),
    ]
    assert len(attacks) == 62
    return attacks


@pytest.mark.parametrize("name,pattern,builder", _build_62_attacks(), ids=[a[0] for a in _build_62_attacks()])
def test_live_adversarial_forgery_rejected(
    name: str,
    pattern: str,
    builder: Callable[[], Dict[str, Any]],
) -> None:
    forged = builder()
    with pytest.raises(CertificateError, match=pattern):
        verify_certificate(forged)
