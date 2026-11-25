"""Comprehensive 80-test suite for VPVNP-CERT-1.0.

Includes:
  - 1 aggregate canonical 16-certificate replay,
  - 3 raw-JSON zero-float / NaN / duplicate-key parser tests,
  - 2 exact arithmetic soundness regressions (Lambda(Z^4) 4096-quadruple identity & D=4 Clifford involutions),
  - 74 parametrized live adversarial forgery tests (12 schema/parser, 16 Mode 1,
    17 Mode 2, 14 Mode 3, 15 Mode 4), each asserting an exact regex match on the
    intended CertificateError branch.
"""

from __future__ import annotations

import copy
import json
from pathlib import Path
import pytest

from src.vpvnp_certifier import (
    PROTOCOL_ID,
    verify_certificate_dict,
    verify_certificate_file,
    verify_certificate_str,
)
from src.vpvnp_exact import (
    CertificateError,
    apply_signed_perm,
    build_signed_perm_involution,
    extract_exterior_packet_arrays,
)

ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = ROOT / "certificates"


def _load(name: str) -> dict:
    return json.loads((CERT_DIR / f"{name}.cert.json").read_text(encoding="utf-8"))


def test_all_16_canonical_certificates_verify() -> None:
    files = sorted(CERT_DIR.glob("*.cert.json"))
    assert len(files) == 16
    for f in files:
        res = verify_certificate_file(f)
        assert res["protocol"] == PROTOCOL_ID


def test_raw_json_rejects_float_literal() -> None:
    raw = '{"protocol": "VPVNP-CERT-1.0", "certificate_id": "x", "mode": "hinge_stretch_and_replay_cert", "payload": {"w": 1.5}}'
    with pytest.raises(CertificateError, match="Floating-point literal rejected"):
        verify_certificate_str(raw)


def test_raw_json_rejects_nan_constant() -> None:
    raw = '{"protocol": "VPVNP-CERT-1.0", "certificate_id": "x", "mode": "hinge_stretch_and_replay_cert", "payload": {"w": NaN}}'
    with pytest.raises(CertificateError, match="Non-standard JSON constant rejected"):
        verify_certificate_str(raw)


def test_raw_json_rejects_duplicate_keys() -> None:
    raw = '{"protocol": "VPVNP-CERT-1.0", "protocol": "VPVNP-CERT-1.0"}'
    with pytest.raises(CertificateError, match="Duplicate JSON key rejected"):
        verify_certificate_str(raw)


def test_regression_lambda4_4096_exact() -> None:
    A, B, C, Dp = extract_exterior_packet_arrays()
    for x in range(8):
        for y in range(8):
            for i in range(8):
                for j in range(8):
                    lhs = 1 if (x == y and i == j) else 0
                    rhs = sum(A[x][i][z] * B[y][j][z] + C[y][i][z] * Dp[x][j][z] for z in range(8))
                    assert lhs == rhs


def test_regression_clifford_d4_orthogonality() -> None:
    ops = [build_signed_perm_involution(4, j) for j in range(4)]
    v = [i * 3 - 20 for i in range(16)]
    imgs = [apply_signed_perm(op, v) for op in ops]
    for i in range(4):
        for j in range(i + 1, 4):
            assert sum(a * b for a, b in zip(imgs[i], imgs[j])) == 0


def _build_68_forgeries() -> list[tuple[str, dict, str]]:
    m1 = _load("m1_hinge_d2_f7_replay")
    m2 = _load("m2_cartier_f7_q7_box")
    m3 = _load("m3_clifford_d3_l8_gray5")
    m4 = _load("m4_packet_4096_balanced_11_12")

    cases: list[tuple[str, dict, str]] = []

    def add(name: str, base: dict, mutator, regex: str) -> None:
        c = copy.deepcopy(base)
        mutator(c)
        cases.append((name, c, regex))

    # --- Schema / Top-Level (12) ---
    add("S01_bad_protocol", m1, lambda c: c.__setitem__("protocol", "FAKE-1.0"), "Unsupported protocol")
    add("S02_empty_cert_id", m1, lambda c: c.__setitem__("certificate_id", ""), "non-empty string")
    add("S03_unknown_mode", m1, lambda c: c.__setitem__("mode", "bogus_mode"), "Unknown certificate mode")
    add("S04_extra_top_key", m1, lambda c: c.__setitem__("rogue", 1), "Unexpected top-level keys")
    add("S05_bad_description", m1, lambda c: c.__setitem__("description", 99), "Optional field 'description' must be a string")
    add("S06_bad_note", m1, lambda c: c.__setitem__("note", True), "Optional field 'note' must be a string")
    add("S07_payload_not_obj", m1, lambda c: c.__setitem__("payload", "bad"), "must be a JSON object")
    add("S08_missing_protocol", m1, lambda c: c.pop("protocol"), "Missing required string field 'protocol'")
    add("S09_bool_as_int", m1, lambda c: c["payload"].__setitem__("shortening_D", True), "must be an exact integer")
    add("S10_float_in_dict", m1, lambda c: c["payload"].__setitem__("shortening_w", 11.0), "must be an exact integer")
    add("S11_missing_key", m1, lambda c: c["payload"].pop("omega_vec"), "Missing keys in Mode 1 payload")
    add("S12_extra_key", m1, lambda c: c["payload"].__setitem__("extra", 1), "Unexpected keys in Mode 1 payload")

    # --- Mode 1 Forgeries (14) ---
    add("M1_01_short_D_too_small", m1, lambda c: c["payload"].__setitem__("shortening_D", 1), "out of bounded canonical range")
    add("M1_02_short_ineq_violated", m1, lambda c: c["payload"].__setitem__("shortening_w", 12), "strict shortening inequality")
    add("M1_03_hub_u_zero", m1, lambda c: c["payload"].__setitem__("hub_u_num", 0), "Hub displacement parameters must be positive")
    add("M1_04_hub_no_saving", m1, lambda c: c["payload"].__setitem__("hub_h", 100), "fails strict net wire-cost saving")
    add("M1_05_composite_p", m1, lambda c: c["payload"].__setitem__("replay_prime_p", 9), "replay_prime_p must be a prime")
    add("M1_06_bad_dim", m1, lambda c: c["payload"].__setitem__("replay_dim", 1), "replay_dim must lie in")
    add("M1_07_star_oob", m1, lambda c: c["payload"].__setitem__("marked_pin", 3), "marked_pin out of range")
    add("M1_08_omega_star_zero", m1, lambda c: c["payload"]["omega_vec"].__setitem__(0, 0), "must be nonzero mod p")
    add("M1_09_omega_noncanon", m1, lambda c: c["payload"]["omega_vec"].__setitem__(1, 7), "outside canonical")
    add("M1_10_fc_noncanon", m1, lambda c: c["payload"]["F_c_row"].__setitem__(0, -1), "outside canonical")
    add("M1_11_empty_W_mats", m1, lambda c: c["payload"].__setitem__("W_matrices", []), "1\\.\\.8 dim x dim matrices")
    add("M1_12_cw_len_mismatch", m1, lambda c: c["payload"]["coeff_weights"].pop(), "one length-dim row per W_mu")
    add("M1_13_boundary_law_broken", m1, lambda c: c["payload"]["F_c_row"].__setitem__(0, (c["payload"]["F_c_row"][0] + 1) % 7), "Lemma 3.3 boundary law failed")
    add("M1_14_wrong_e_star_claim", m1, lambda c: c["payload"].__setitem__("claimed_e_star_omega", 1), "claimed_e_star_omega")
    add(
        "M1_15_all_zero_replay",
        m1,
        lambda c: (
            c["payload"].__setitem__("W_matrices", [[[0, 0, 0], [0, 0, 0], [0, 0, 0]]]),
            c["payload"].__setitem__("coeff_weights", [[0, 0, 0]]),
            c["payload"].__setitem__("F_c_row", [0, 0, 0]),
        ),
        "Degenerate replay witness",
    )
    add(
        "M1_16_tautological_fc_eq_srow",
        m1,
        lambda c: c["payload"].__setitem__("F_c_row", [1, 0, 0]),
        "Tautological replay witness",
    )

    # --- Mode 2 Forgeries (17) ---
    add("M2_01_composite_p", m2, lambda c: c["payload"].__setitem__("prime_p", 9), "prime characteristic p")
    add("M2_02_q_not_p_power", m2, lambda c: c["payload"].__setitem__("q_power", 10), "exact power of prime_p")
    add("M2_03_bad_H_box", m2, lambda c: c["payload"].__setitem__("H_box", 20), "Section 5.2 definition")
    add("M2_04_mu_gt_L", m2, lambda c: c["payload"].__setitem__("mu_x", 4), "mu_x must lie in")
    add("M2_05_g_neg_exp", m2, lambda c: c["payload"]["g_poly"][0].__setitem__(0, -1), "g_poly exponents must lie in")
    add("M2_06_g_deg_gt_S", m2, lambda c: c["payload"]["g_poly"][0].__setitem__(0, 3), "g_poly exponents must lie in")
    add("M2_07_f_outside_box", m2, lambda c: c["payload"]["f_box_poly"][0].__setitem__(0, 40), "violates Section 5.2 box B")
    add("M2_08_noncanon_coeff", m2, lambda c: c["payload"]["g_poly"][0].__setitem__(2, 7), "outside canonical nonzero")
    add("M2_09_dup_monomial", m2, lambda c: c["payload"]["g_poly"].append(list(c["payload"]["g_poly"][0])), "Duplicate monomial")
    add("M2_10_empty_d_poly", m2, lambda c: c["payload"].__setitem__("D_test_poly", []), "1\\.\\.16")
    add("M2_11_wrong_cartier_out", m2, lambda c: c["payload"]["claimed_cartier_terms"][0].__setitem__(2, (c["payload"]["claimed_cartier_terms"][0][2] % 6) + 1), "Claimed Cartier output")
    add("M2_12_ortho_noncanon", m2, lambda c: c["payload"].__setitem__("claimed_ortho_coeff", 7), "outside canonical")
    add("M2_13_wrong_ortho_coeff", m2, lambda c: c["payload"].__setitem__("claimed_ortho_coeff", (c["payload"]["claimed_ortho_coeff"] + 1) % 7), "claimed_ortho_coeff")
    add("M2_14_L_out_of_range", m2, lambda c: c["payload"].__setitem__("L_bound", 0), "L_bound and S_bound")
    add("M2_15_zero_coeff_smuggle", m2, lambda c: c["payload"]["g_poly"].append([50, 50, 0]), "outside canonical nonzero")
    add("M2_16_const_D_test", m2, lambda c: c["payload"].__setitem__("D_test_poly", [[0, 0, 1]]), "D_test_poly must be non-constant")
    add("M2_17_absent_ortho_target", m2, lambda c: c["payload"].__setitem__("ortho_target_exp", [0, 0]), "must index a certified nonzero monomial")

    # --- Mode 3 Forgeries (14) ---
    add("M3_01_dim_too_small", m3, lambda c: c["payload"].__setitem__("dim_D", 1), "dim_D must lie in")
    add("M3_02_dim_too_large", m3, lambda c: c["payload"].__setitem__("dim_D", 6), "dim_D must lie in")
    add("M3_03_vec_wrong_len", m3, lambda c: c["payload"]["witness_vector"].pop(), "list of length in \\[8, 8\\]")
    add("M3_04_vec_all_zero", m3, lambda c: c["payload"].__setitem__("witness_vector", [0] * 8), "witness_vector must be nonzero")
    add("M3_05_vec_non_int", m3, lambda c: c["payload"]["witness_vector"].__setitem__(0, "bad"), "contains non-integer")
    add("M3_06_l_too_small", m3, lambda c: c["payload"].__setitem__("cycle_len_l", 4), "outside valid windowed-host")
    add("M3_07_l_too_large", m3, lambda c: c["payload"].__setitem__("cycle_len_l", 25), "outside valid windowed-host")
    add("M3_08_radius_too_big", m3, lambda c: c["payload"].__setitem__("radius_a", 3), "outside valid windowed-host")
    add("M3_09_radius_neg", m3, lambda c: c["payload"].__setitem__("radius_a", -1), "outside valid windowed-host")
    add("M3_10_wrong_Va", m3, lambda c: c["payload"].__setitem__("claimed_Va", c["payload"]["claimed_Va"] + 1), "claimed_Va=")
    add("M3_11_wrong_Va_next", m3, lambda c: c["payload"].__setitem__("claimed_Va_next", c["payload"]["claimed_Va_next"] + 1), "claimed_Va_next=")
    add("M3_12_gray_bits_small", m3, lambda c: c["payload"].__setitem__("gray_bits", 1), "gray_bits must lie in")
    add("M3_13_gray_bits_large", m3, lambda c: c["payload"].__setitem__("gray_bits", 9), "gray_bits must lie in")
    add("M3_14_extra_m3_key", m3, lambda c: c["payload"].__setitem__("rogue", 0), "Unexpected keys in Mode 3")

    # --- Mode 4 Forgeries (14) ---
    add("M4_01_full_flag_false", m4, lambda c: c["payload"].__setitem__("verify_full_4096_packet", False), "must be boolean true")
    add("M4_02_full_flag_int", m4, lambda c: c["payload"].__setitem__("verify_full_4096_packet", 1), "must be boolean true")
    add("M4_03_empty_samples", m4, lambda c: c["payload"].__setitem__("sample_quadruples", []), "1\\.\\.16")
    add("M4_04_sample_bad_len", m4, lambda c: c["payload"]["sample_quadruples"][0].pop(), "must be 7 integers")
    add("M4_05_sample_idx_oob", m4, lambda c: c["payload"]["sample_quadruples"][0].__setitem__(0, 8), "indices out of \\[0, 7\\]")
    add("M4_06_sample_wrong_val", m4, lambda c: c["payload"]["sample_quadruples"][0].__setitem__(6, 0), "disagrees with exact integral packet")
    add("M4_07_empty_hist", m4, lambda c: c["payload"].__setitem__("selector_histograms", []), "1\\.\\.32")
    add("M4_08_hist_zero_pair", m4, lambda c: c["payload"]["selector_histograms"].__setitem__(0, [0, 0]), "positive sum")
    add("M4_09_hist_neg_cnt", m4, lambda c: c["payload"]["selector_histograms"].__setitem__(0, [-1, 5]), "positive sum")
    add("M4_10_wrong_cost_a", m4, lambda c: c["payload"].__setitem__("claimed_grouping_a_bits", 999), "claimed_grouping_a_bits")
    add("M4_11_wrong_cost_b", m4, lambda c: c["payload"].__setitem__("claimed_grouping_b_bits", 999), "claimed_grouping_b_bits")
    add("M4_12_wrong_min_bits", m4, lambda c: c["payload"].__setitem__("claimed_min_bits", 100), "claimed_min_bits")
    add("M4_13_wrong_unaltered", m4, lambda c: c["payload"].__setitem__("claimed_unaltered_bits", 100), "claimed_unaltered_bits")
    add("M4_14_wrong_ratio", m4, lambda c: c["payload"].__setitem__("claimed_ratio", [1, 2]), "claimed_ratio disagrees")
    add("M4_15_unreduced_ratio", m4, lambda c: c["payload"].__setitem__("claimed_ratio", [22, 24]), "lowest terms \\(gcd == 1\\)")

    assert len(cases) == 74
    return cases


FORGERIES = _build_68_forgeries()


@pytest.mark.parametrize("name,cert,expected_regex", FORGERIES, ids=[c[0] for c in FORGERIES])
def test_adversarial_forgery_rejected(name: str, cert: dict, expected_regex: str) -> None:
    with pytest.raises(CertificateError, match=expected_regex):
        verify_certificate_dict(cert)
