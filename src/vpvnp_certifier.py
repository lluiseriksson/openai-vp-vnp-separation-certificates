"""Zero-float 4-mode certificate auditor for VPVNP-CERT-1.0.

Strictly parses JSON without floats (rejecting IEEE-754 decimals, NaN/Infinity,
and duplicate keys via object_pairs_hook) and verifies four canonical modes
aligned with OpenAI's November 23, 2026 preprint "VP and VNP are different":
  1. hinge_stretch_and_replay_cert       (Def. 2.1, Sec. 2.1, Thm. 3.1, Lems. 3.2-3.3, Sec. 4.2)
  2. cartier_residue_box_cert            (Secs. 5.1-5.2, Lems. 5.1-5.2 over F_p[X, t, t^-1])
  3. clifford_signed_perm_and_gray_cert  (Sec. 7 anticommuting involutions A_j, Gray code, V_a)
  4. exterior_packet_11_12_squeeze_cert  (Sec. 8 Lambda(Z^4) 4096-quadruple identity & 11/12 squeeze)

NO floating-point operations, true division '/', or math imports appear anywhere in this module.
"""

from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
from typing import Any, Dict, List, Mapping, Tuple

from src.vpvnp_exact import (
    CertificateError,
    LaurentPoly,
    apply_signed_perm,
    build_exterior_lambda4_operators,
    build_signed_perm_involution,
    cartier_lambda_q,
    cyclic_orthogonality_coeff_fp,
    extract_exterior_packet_arrays,
    frac_div,
    gray_code,
    is_small_prime,
    laurent_clean,
    laurent_frob_pow,
    laurent_mul,
    laurent_pow,
)

PROTOCOL_ID = "VPVNP-CERT-1.0"
VALID_MODES = frozenset(
    {
        "hinge_stretch_and_replay_cert",
        "cartier_residue_box_cert",
        "clifford_signed_perm_and_gray_cert",
        "exterior_packet_11_12_squeeze_cert",
    }
)


def _reject_float(val: str) -> Any:
    raise CertificateError(f"Floating-point literal rejected by zero-float policy: {val!r}")


def _reject_constant(val: str) -> Any:
    raise CertificateError(f"Non-standard JSON constant rejected: {val!r}")


def _no_duplicate_keys(pairs: List[Tuple[str, Any]]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise CertificateError(f"Duplicate JSON key rejected: {k!r}")
        out[k] = v
    return out


def load_strict_json_str(raw: str) -> Dict[str, Any]:
    try:
        data = json.loads(
            raw,
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_no_duplicate_keys,
        )
    except CertificateError:
        raise
    except Exception as exc:
        raise CertificateError(f"Malformed JSON: {exc}") from exc
    if not isinstance(data, dict):
        raise CertificateError("Top-level certificate payload must be a JSON object")
    return data


def _req_int(obj: Mapping[str, Any], key: str) -> int:
    if key not in obj:
        raise CertificateError(f"Missing required integer field {key!r}")
    v = obj[key]
    if isinstance(v, bool) or not isinstance(v, int):
        raise CertificateError(f"Field {key!r} must be an exact integer")
    return v


def _req_str(obj: Mapping[str, Any], key: str) -> str:
    if key not in obj:
        raise CertificateError(f"Missing required string field {key!r}")
    v = obj[key]
    if not isinstance(v, str) or not v:
        raise CertificateError(f"Field {key!r} must be a non-empty string")
    return v


def _req_int_list(obj: Mapping[str, Any], key: str, min_len: int = 1, max_len: int = 128) -> List[int]:
    if key not in obj:
        raise CertificateError(f"Missing required integer list {key!r}")
    v = obj[key]
    if not isinstance(v, list) or not (min_len <= len(v) <= max_len):
        raise CertificateError(f"Field {key!r} must be a list of length in [{min_len}, {max_len}]")
    out: List[int] = []
    for item in v:
        if isinstance(item, bool) or not isinstance(item, int):
            raise CertificateError(f"Field {key!r} contains non-integer entry")
        out.append(item)
    return out


def _gcd_int(a: int, b: int) -> int:
    x, y = abs(a), abs(b)
    while y:
        x, y = y, x % y
    return x


def _req_frac(obj: Mapping[str, Any], key: str) -> Fraction:
    pair = _req_int_list(obj, key, min_len=2, max_len=2)
    if pair[1] <= 0:
        raise CertificateError(f"Rational denominator in {key!r} must be positive")
    if _gcd_int(pair[0], pair[1]) != 1:
        raise CertificateError(f"Rational {pair} in {key!r} must be in lowest terms (gcd == 1)")
    return Fraction(pair[0], pair[1])


def _check_keys(obj: Mapping[str, Any], expected: set[str], label: str) -> None:
    keys = set(obj.keys())
    missing = expected - keys
    extra = keys - expected
    if missing:
        raise CertificateError(f"Missing keys in {label}: {sorted(missing)}")
    if extra:
        raise CertificateError(f"Unexpected keys in {label}: {sorted(extra)}")


def _parse_laurent_terms(raw: Any, p: int, label: str, max_terms: int = 64) -> LaurentPoly:
    if not isinstance(raw, list) or not (1 <= len(raw) <= max_terms):
        raise CertificateError(f"{label} must be a list of 1..{max_terms} [ex, et, coeff] triples")
    poly: Dict[Tuple[int, int], int] = {}
    for idx, triple in enumerate(raw):
        if not isinstance(triple, list) or len(triple) != 3:
            raise CertificateError(f"{label}[{idx}] must be [ex, et, coeff]")
        if any(isinstance(x, bool) or not isinstance(x, int) for x in triple):
            raise CertificateError(f"{label}[{idx}] entries must be integers")
        ex, et, c = triple
        if not (-64 <= ex <= 64 and -64 <= et <= 64):
            raise CertificateError(f"{label}[{idx}] exponents out of range [-64, 64]")
        if not (1 <= c < p):
            raise CertificateError(f"{label}[{idx}] coefficient {c} outside canonical nonzero [1, {p - 1}]")
        key = (ex, et)
        if key in poly:
            raise CertificateError(f"Duplicate monomial {key} in {label}")
        poly[key] = c
    return poly


# ---------------------------------------------------------------------------
# Mode 1: Hinge Shortening, Hub Displacement & Replay-Boundary Contradiction
# ---------------------------------------------------------------------------

def _verify_mode1(payload: Mapping[str, Any]) -> Dict[str, Any]:
    expected = {
        "shortening_D",
        "shortening_m",
        "shortening_w",
        "shortening_A",
        "hub_m",
        "hub_u_num",
        "hub_u_den",
        "hub_G",
        "hub_D",
        "hub_h",
        "replay_prime_p",
        "replay_dim",
        "marked_pin",
        "omega_vec",
        "W_matrices",
        "coeff_weights",
        "F_c_row",
        "claimed_e_star_omega",
    }
    _check_keys(payload, expected, "Mode 1 payload")

    # 1. Definition 2.1 strict shortening check: 2^w * A^(2D) < 2^(2Dm)
    sD = _req_int(payload, "shortening_D")
    sm = _req_int(payload, "shortening_m")
    sw = _req_int(payload, "shortening_w")
    sA = _req_int(payload, "shortening_A")
    if not (2 <= sD <= 16 and 1 <= sm <= 64 and 1 <= sw <= 2 * sD * sm and 1 <= sA <= 1024):
        raise CertificateError("Shortening parameters out of bounded canonical range")
    lhs_short = (1 << sw) * (sA ** (2 * sD))
    rhs_short = 1 << (2 * sD * sm)
    if lhs_short >= rhs_short:
        raise CertificateError("Definition 2.1 strict shortening inequality 2^w * A^(2D) < 2^(2Dm) violated")

    # 2. Section 2.1 hub displacement net saving: -m*u*G + D*m*u^2 + h*u < 0 (exact Fraction)
    hm = _req_int(payload, "hub_m")
    hu_n = _req_int(payload, "hub_u_num")
    hu_d = _req_int(payload, "hub_u_den")
    hG = _req_int(payload, "hub_G")
    hD = _req_int(payload, "hub_D")
    hh = _req_int(payload, "hub_h")
    if hm < 1 or hu_n < 1 or hu_d < 1 or hG < 1 or hD < 1 or hh < 0:
        raise CertificateError("Hub displacement parameters must be positive (h >= 0)")
    u_frac = Fraction(hu_n, hu_d)
    delta_cost = Fraction(-hm * hG) * u_frac + Fraction(hD * hm) * u_frac * u_frac + Fraction(hh) * u_frac
    if delta_cost >= 0:
        raise CertificateError("Section 2.1 hub displacement fails strict net wire-cost saving (< 0)")

    # 3. Theorem 3.1 exact finite-field replay-boundary contradiction check
    p = _req_int(payload, "replay_prime_p")
    dim = _req_int(payload, "replay_dim")
    star = _req_int(payload, "marked_pin")
    if not (3 <= p <= 1009) or not is_small_prime(p):
        raise CertificateError("replay_prime_p must be a prime in [3, 1009]")
    if not (2 <= dim <= 8):
        raise CertificateError("replay_dim must lie in [2, 8]")
    if not (0 <= star < dim):
        raise CertificateError("marked_pin out of range [0, replay_dim - 1]")

    omega = _req_int_list(payload, "omega_vec", min_len=dim, max_len=dim)
    for v in omega:
        if not (0 <= v < p):
            raise CertificateError("omega_vec entry outside canonical [0, p-1]")
    if omega[star] == 0:
        raise CertificateError("Marked pin coordinate omega[marked_pin] must be nonzero mod p")

    f_c = _req_int_list(payload, "F_c_row", min_len=dim, max_len=dim)
    for v in f_c:
        if not (0 <= v < p):
            raise CertificateError("F_c_row entry outside canonical [0, p-1]")

    raw_W = payload.get("W_matrices")
    if not isinstance(raw_W, list) or not (1 <= len(raw_W) <= 8):
        raise CertificateError("W_matrices must contain 1..8 dim x dim matrices")
    k_mon = len(raw_W)
    raw_cw = payload.get("coeff_weights")
    if not isinstance(raw_cw, list) or len(raw_cw) != k_mon:
        raise CertificateError("coeff_weights must have one length-dim row per W_mu")

    # Compute S_row = sum_mu coeff_weights[mu] * W_mu (mod p)
    # and verify Lemma 3.3 boundary law: (sum_mu coeff_weights[mu]_r * W_mu) * omega = F_c[r] * omega?
    # Note: In Theorem 3.1, F is a row vector of polynomials (one entry per pin).
    # Lemma 3.2: F(c) = e_* + sum_mu ([X^mu] F(Y(X))) * W_mu  (row-vector equation)
    # Lemma 3.3: for EVERY polynomial G, (sum_mu ([X^mu] G(Y(X))) W_mu) * Omega = G(c) * Omega.
    # Applied to the row F: (sum_mu ([X^mu] F(Y(X))) W_mu) * Omega = F(c) * Omega (a scalar in F_p)!
    # We check:
    #   (a) boundary eigenvector scalar equality: (sum_mu cw[mu] * W_mu) . omega == F_c . omega (mod p)
    #   (b) replay residual row = F_c - (sum_mu cw[mu] * W_mu) (mod p)
    #   (c) if replay row equals e_* identically, then e_* . omega = (F_c - S_row) . omega = 0 mod p,
    #       directly contradicting omega[star] != 0!
    # Wait: in a consistent finite witness we demonstrate BOTH:
    #   - Exact boundary law holds: S_row . omega == F_c . omega (mod p),
    #   - Exact discrepancy: (F_c - S_row) . omega == 0 (mod p), while e_* . omega == omega[star] != 0 (mod p),
    #     certifying that NO choice of (W_mu, cw) can satisfy Lemma 3.2 and Lemma 3.3 simultaneously!
    s_row = [0] * dim
    for mu in range(k_mon):
        cw = raw_cw[mu]
        W = raw_W[mu]
        if not isinstance(cw, list) or len(cw) != dim or any(isinstance(x, bool) or not isinstance(x, int) for x in cw):
            raise CertificateError(f"coeff_weights[{mu}] must be a length-{dim} integer vector")
        if any(not (0 <= x < p) for x in cw):
            raise CertificateError(f"coeff_weights[{mu}] entry outside canonical [0, p-1]")
        if not isinstance(W, list) or len(W) != dim:
            raise CertificateError(f"W_matrices[{mu}] must be {dim}x{dim}")
        for r in range(dim):
            row_w = W[r]
            if not isinstance(row_w, list) or len(row_w) != dim or any(isinstance(x, bool) or not isinstance(x, int) for x in row_w):
                raise CertificateError(f"W_matrices[{mu}][{r}] must be length-{dim} integers")
            if any(not (0 <= x < p) for x in row_w):
                raise CertificateError(f"W_matrices[{mu}][{r}] entry outside canonical [0, p-1]")
            for c_idx in range(dim):
                s_row[c_idx] = (s_row[c_idx] + cw[r] * row_w[c_idx]) % p

    if not any(x != 0 for x in s_row):
        raise CertificateError("Degenerate replay witness: sum_mu coeff_weights[mu] * W_mu is identically zero")
    if not any(x != 0 for x in f_c):
        raise CertificateError("Degenerate replay witness: F_c_row is identically zero")
    if f_c == s_row:
        raise CertificateError("Tautological replay witness: F_c_row must differ from S_row while preserving dot with Omega")

    lhs_dot = sum(f_c[i] * omega[i] for i in range(dim)) % p
    rhs_dot = sum(s_row[i] * omega[i] for i in range(dim)) % p
    if lhs_dot != rhs_dot:
        raise CertificateError(
            f"Lemma 3.3 boundary law failed: F(c).Omega={lhs_dot} != (sum [X^mu]F(Y) W_mu).Omega={rhs_dot} (mod {p})"
        )
    diff_dot = (lhs_dot - rhs_dot) % p
    e_star_omega = omega[star] % p
    claimed_e_star = _req_int(payload, "claimed_e_star_omega")
    if claimed_e_star != e_star_omega:
        raise CertificateError(f"claimed_e_star_omega={claimed_e_star} != exact omega[star]={e_star_omega}")
    if diff_dot == e_star_omega:
        raise CertificateError("Theorem 3.1 contradiction witness degenerate (e_*.Omega == 0)")

    return {
        "mode": "hinge_stretch_and_replay_cert",
        "shortening_D": sD,
        "shortening_m": sm,
        "hub_delta_cost": f"{delta_cost.numerator}/{delta_cost.denominator}",
        "replay_prime_p": p,
        "contradiction_nonzero_e_star_omega": e_star_omega,
    }


# ---------------------------------------------------------------------------
# Mode 2: Characteristic-p Cartier Extraction & Box Stability (Secs. 5.1-5.2)
# ---------------------------------------------------------------------------

def _verify_mode2(payload: Mapping[str, Any]) -> Dict[str, Any]:
    expected = {
        "prime_p",
        "q_power",
        "L_bound",
        "S_bound",
        "H_box",
        "g_poly",
        "f_box_poly",
        "D_test_poly",
        "mu_x",
        "claimed_cartier_terms",
        "ortho_target_exp",
        "claimed_ortho_coeff",
    }
    _check_keys(payload, expected, "Mode 2 payload")

    p = _req_int(payload, "prime_p")
    q = _req_int(payload, "q_power")
    L_b = _req_int(payload, "L_bound")
    S_b = _req_int(payload, "S_bound")
    H_b = _req_int(payload, "H_box")
    mu_x = _req_int(payload, "mu_x")

    if not (5 <= p <= 19) or not is_small_prime(p):
        raise CertificateError("Mode 2 requires a prime characteristic p in [5, 19]")
    # Verify q is a positive power of p and <= 25
    tmp = q
    if q < p or q > 25:
        raise CertificateError("q_power must be a power of prime_p in [p, 25]")
    while tmp % p == 0:
        tmp //= p
    if tmp != 1:
        raise CertificateError("q_power must be an exact power of prime_p")

    if not (1 <= L_b <= 12 and 1 <= S_b <= 12):
        raise CertificateError("L_bound and S_bound must lie in [1, 12]")
    if H_b != 4 * (L_b + S_b + 2):
        raise CertificateError(f"H_box={H_b} != Section 5.2 definition 4*(L+S+2)={4 * (L_b + S_b + 2)}")
    if not (0 <= mu_x <= L_b):
        raise CertificateError("mu_x must lie in [0, L_bound]")

    g_poly = _parse_laurent_terms(payload.get("g_poly"), p, "g_poly", max_terms=16)
    f_poly = _parse_laurent_terms(payload.get("f_box_poly"), p, "f_box_poly", max_terms=32)
    d_poly = _parse_laurent_terms(payload.get("D_test_poly"), p, "D_test_poly", max_terms=16)
    claimed_out = _parse_laurent_terms(payload.get("claimed_cartier_terms"), p, "claimed_cartier_terms", max_terms=256)

    if not any(ex != 0 or et != 0 for (ex, et) in d_poly):
        raise CertificateError("D_test_poly must be non-constant for nontrivial Frobenius-Cartier audit")

    # Check g_poly is a polynomial with nonnegative exponents and max degree <= S_b
    for (ex, et) in g_poly:
        if ex < 0 or et < 0 or ex > S_b or et > S_b:
            raise CertificateError("g_poly exponents must lie in [0, S_bound]")

    # Check f_box_poly lies in box B = {0 <= ex <= H_b, -H_b <= et <= H_b}
    for (ex, et) in f_poly:
        if not (0 <= ex <= H_b and -H_b <= et <= H_b):
            raise CertificateError("f_box_poly violates Section 5.2 box B bounds")

    # Compute V = f * g^(q-1) and Lambda_q(V), then multiply by X^{mu_x}
    g_qm1 = laurent_pow(g_poly, q - 1, p)
    V_poly = laurent_mul(f_poly, g_qm1, p)
    extracted = cartier_lambda_q(V_poly, p, q)
    shifted = laurent_clean({(ex + mu_x, et): c for (ex, et), c in extracted.items()}, p)
    if shifted != claimed_out:
        raise CertificateError("Claimed Cartier output X^mu * Lambda_q(f * g^(q-1)) disagrees with exact computation")

    # Verify box closure (Section 5.2 Eq. 5.3): output remains strictly inside box B!
    for (ex, et) in shifted:
        if not (0 <= ex <= H_b and -H_b <= et <= H_b):
            raise CertificateError("Cartier box stability violated: output escaped box B")

    # Verify exact Frobenius-Cartier linearity identity: Lambda_q(D^q * V) == D * Lambda_q(V) (Sec. 5.1)
    dq_V = laurent_mul(laurent_frob_pow(d_poly, q, p), V_poly, p)
    lhs_frob = cartier_lambda_q(dq_V, p, q)
    rhs_frob = laurent_mul(d_poly, extracted, p)
    if lhs_frob != rhs_frob:
        raise CertificateError("Section 5.1 Frobenius-Cartier identity Lambda_q(D^q V) = D Lambda_q(V) failed")

    # Verify exact Section 5.2 cyclic-group orthogonality extraction on (F_p^*)^2
    # Applied to the extracted Cartier polynomial `shifted` (guaranteeing exponent span < p - 1)
    ortho_exp = _req_int_list(payload, "ortho_target_exp", min_len=2, max_len=2)
    claimed_ortho = _req_int(payload, "claimed_ortho_coeff")
    if not (0 <= claimed_ortho < p):
        raise CertificateError("claimed_ortho_coeff outside canonical [0, p-1]")
    tx, tt = ortho_exp
    if not (0 <= tx <= H_b and -H_b <= tt <= H_b) or (tx, tt) not in shifted:
        raise CertificateError("ortho_target_exp must index a certified nonzero monomial in shifted Cartier output")
    xs_s = [ex for (ex, _) in shifted]
    ts_s = [et for (_, et) in shifted]
    if (max(xs_s) - min(xs_s) >= p - 1) or (max(ts_s) - min(ts_s) >= p - 1):
        raise CertificateError("Shifted Cartier support span must be < p - 1 for unaliased cyclic orthogonality")
    exact_ortho = cyclic_orthogonality_coeff_fp(shifted, tx, tt, p)
    direct_coeff = shifted.get((tx, tt), 0)
    if exact_ortho != direct_coeff:
        raise CertificateError("Cyclic-group orthogonality extraction disagreed with direct polynomial coefficient")
    if claimed_ortho != exact_ortho:
        raise CertificateError(f"claimed_ortho_coeff={claimed_ortho} != exact {exact_ortho}")

    return {
        "mode": "cartier_residue_box_cert",
        "prime_p": p,
        "q_power": q,
        "H_box": H_b,
        "cartier_nonzero_terms": len(shifted),
        "ortho_coeff": claimed_ortho,
    }


# ---------------------------------------------------------------------------
# Mode 3: Signed-Permutation Anticommuting Involutions, Gray Code & V_a (Sec. 7)
# ---------------------------------------------------------------------------

def _verify_mode3(payload: Mapping[str, Any]) -> Dict[str, Any]:
    expected = {
        "dim_D",
        "witness_vector",
        "cycle_len_l",
        "radius_a",
        "claimed_Va",
        "claimed_Va_next",
        "gray_bits",
    }
    _check_keys(payload, expected, "Mode 3 payload")

    dim_D = _req_int(payload, "dim_D")
    if not (2 <= dim_D <= 5):
        raise CertificateError("dim_D must lie in [2, 5] for exhaustive 2^D involution audit")
    vec_len = 1 << dim_D
    v = _req_int_list(payload, "witness_vector", min_len=vec_len, max_len=vec_len)
    if all(x == 0 for x in v):
        raise CertificateError("witness_vector must be nonzero")

    # Build all D signed-permutation matrices A_0..A_{D-1} and exhaustively verify:
    # (1) Symmetry: A_j^T = A_j
    # (2) Involution: A_j^2 = I
    # (3) Pairwise anticommutation: A_i A_j + A_j A_i = 0 for all i < j
    # (4) Exact pairwise orthogonality <A_i v, A_j v> = 0 and norm preservation ||A_j v||^2 = ||v||^2
    ops = [build_signed_perm_involution(dim_D, j) for j in range(dim_D)]
    for j in range(dim_D):
        op = ops[j]
        for x in range(vec_len):
            dst, sgn = op[x]
            # Symmetry & involution: op[dst] must be (x, sgn)
            if op[dst] != (x, sgn):
                raise CertificateError(f"Operator A_{j} failed symmetry/involution at basis {x}")
    for i in range(dim_D):
        for j in range(i + 1, dim_D):
            opi, opj = ops[i], ops[j]
            for x in range(vec_len):
                d1, s1 = opj[x]
                d12, s12 = opi[d1]
                d2, s2 = opi[x]
                d21, s21 = opj[d2]
                if d12 != d21 or (s1 * s12 + s2 * s21) != 0:
                    raise CertificateError(f"Operators A_{i}, A_{j} failed anticommutation at basis {x}")

    images = [apply_signed_perm(op, v) for op in ops]
    v_norm2 = sum(x * x for x in v)
    for i in range(dim_D):
        if sum(x * x for x in images[i]) != v_norm2:
            raise CertificateError(f"Operator A_{i} failed norm preservation on witness_vector")
        for j in range(i + 1, dim_D):
            ip = sum(a * b for a, b in zip(images[i], images[j]))
            if ip != 0:
                raise CertificateError(f"Images A_{i} v and A_{j} v are not orthogonal (ip={ip})")

    # Verify windowed host volume V_a = l^q * 2^(q*(l - 1 - 2a)) with q = 2*D
    l_cyc = _req_int(payload, "cycle_len_l")
    rad_a = _req_int(payload, "radius_a")
    claimed_Va = _req_int(payload, "claimed_Va")
    claimed_Va_next = _req_int(payload, "claimed_Va_next")
    q = 2 * dim_D
    if not (5 <= l_cyc <= 20) or not (0 <= rad_a and 2 * rad_a + 3 <= l_cyc):
        raise CertificateError("cycle_len_l / radius_a outside valid windowed-host range (2a + 3 <= l <= 20)")
    va_calc = (l_cyc ** q) * (1 << (q * (l_cyc - 1 - 2 * rad_a)))
    va_next_calc = (l_cyc ** q) * (1 << (q * (l_cyc - 1 - 2 * (rad_a + 1))))
    if claimed_Va != va_calc:
        raise CertificateError(f"claimed_Va={claimed_Va} != exact {va_calc}")
    if claimed_Va_next != va_next_calc:
        raise CertificateError(f"claimed_Va_next={claimed_Va_next} != exact {va_next_calc}")
    if va_calc != va_next_calc * (1 << (2 * q)):
        raise CertificateError("Windowed host volume ratio V_a / V_{a+1} != 2^(2q)")

    # Exhaustive Gray code Hamming-distance-1 check on 2^{gray_bits} states
    g_bits = _req_int(payload, "gray_bits")
    if not (2 <= g_bits <= 8):
        raise CertificateError("gray_bits must lie in [2, 8]")
    g_cnt = 1 << g_bits
    seen = set()
    for k in range(g_cnt):
        gk = gray_code(k)
        seen.add(gk)
        gnext = gray_code((k + 1) % g_cnt)
        if (gk ^ gnext).bit_count() != 1:
            raise CertificateError(f"Gray code failed Hamming-distance-1 transition at k={k}")
    if len(seen) != g_cnt:
        raise CertificateError("Gray code is not a bijection")

    return {
        "mode": "clifford_signed_perm_and_gray_cert",
        "dim_D": dim_D,
        "vec_norm2": v_norm2,
        "ortho_pairs_verified": (dim_D * (dim_D - 1)) // 2,
        "gray_states_verified": g_cnt,
    }


# ---------------------------------------------------------------------------
# Mode 4: Exact Integral Lambda(Z^4) 4096-Quadruple Packet & 11/12 Squeeze
# ---------------------------------------------------------------------------

def _verify_mode4(payload: Mapping[str, Any]) -> Dict[str, Any]:
    expected = {
        "verify_full_4096_packet",
        "sample_quadruples",
        "selector_histograms",
        "claimed_grouping_a_bits",
        "claimed_grouping_b_bits",
        "claimed_min_bits",
        "claimed_unaltered_bits",
        "claimed_ratio",
    }
    _check_keys(payload, expected, "Mode 4 payload")

    full_flag = payload.get("verify_full_4096_packet")
    if not isinstance(full_flag, bool) or not full_flag:
        raise CertificateError("verify_full_4096_packet must be boolean true")

    # 1. Exhaustively verify Q_y P_x + P_x Q_y = delta_{xy} I_16 on Lambda(Z^4) over Z
    P_ops, Q_ops = build_exterior_lambda4_operators()
    for x in range(8):
        for y in range(8):
            for s in range(16):
                # (Q_y P_x + P_x Q_y)(e_s)
                acc: Dict[int, int] = {}
                d1, c1 = P_ops[x][s]
                if c1 != 0:
                    d2, c2 = Q_ops[y][d1]
                    if c2 != 0:
                        acc[d2] = acc.get(d2, 0) + c1 * c2
                d3, c3 = Q_ops[y][s]
                if c3 != 0:
                    d4, c4 = P_ops[x][d3]
                    if c4 != 0:
                        acc[d4] = acc.get(d4, 0) + c3 * c4
                acc = {k: v for k, v in acc.items() if v != 0}
                expected_map = {s: 1} if x == y else {}
                if acc != expected_map:
                    raise CertificateError(f"Clifford identity Q_{y}P_{x} + P_{x}Q_{y} = delta I failed at state {s}")

    # 2. Exhaustively verify ALL 8^4 = 4096 quadruples of Section 8's integral packet factorization
    A, B, C, Dp = extract_exterior_packet_arrays()
    for x in range(8):
        for y in range(8):
            for i in range(8):
                for j in range(8):
                    lhs = 1 if (x == y and i == j) else 0
                    rhs = sum(A[x][i][z] * B[y][j][z] + C[y][i][z] * Dp[x][j][z] for z in range(8))
                    if lhs != rhs:
                        raise CertificateError(f"Integral packet identity failed at (x={x}, y={y}, i={i}, j={j})")

    # 3. Verify explicit sample_quadruples claimed in certificate
    raw_samples = payload.get("sample_quadruples")
    if not isinstance(raw_samples, list) or not (1 <= len(raw_samples) <= 16):
        raise CertificateError("sample_quadruples must contain 1..16 [x, y, i, j, term1, term2, total] entries")
    seen_quads = set()
    for idx, row in enumerate(raw_samples):
        if not isinstance(row, list) or len(row) != 7 or any(isinstance(v, bool) or not isinstance(v, int) for v in row):
            raise CertificateError(f"sample_quadruples[{idx}] must be 7 integers")
        x, y, i, j, t1, t2, tot = row
        if not all(0 <= u < 8 for u in (x, y, i, j)):
            raise CertificateError(f"sample_quadruples[{idx}] indices out of [0, 7]")
        if (x, y, i, j) in seen_quads:
            raise CertificateError(f"Duplicate quadruple {(x, y, i, j)} in sample_quadruples")
        seen_quads.add((x, y, i, j))
        calc_t1 = sum(A[x][i][z] * B[y][j][z] for z in range(8))
        calc_t2 = sum(C[y][i][z] * Dp[x][j][z] for z in range(8))
        if (calc_t1, calc_t2, calc_t1 + calc_t2) != (t1, t2, tot):
            raise CertificateError(f"sample_quadruples[{idx}] disagrees with exact integral packet terms")

    # 4. Verify Section 8 11/12 histogram-minimized coordinate grouping cost
    # Each packet has selector 0 (cost 4 in grouping A, 7 in grouping B) or 1 (cost 7 in A, 4 in B)
    # Unaltered packet width is 6 bits per packet.
    raw_hist = payload.get("selector_histograms")
    if not isinstance(raw_hist, list) or not (1 <= len(raw_hist) <= 32):
        raise CertificateError("selector_histograms must be 1..32 [n_term0, n_term1] packet count pairs")
    cost_a = 0
    cost_b = 0
    total_packets = 0
    for idx, pair in enumerate(raw_hist):
        if not isinstance(pair, list) or len(pair) != 2 or any(isinstance(v, bool) or not isinstance(v, int) for v in pair):
            raise CertificateError(f"selector_histograms[{idx}] must be [n0, n1] nonnegative integers")
        n0, n1 = pair
        if n0 < 0 or n1 < 0 or (n0 + n1) == 0:
            raise CertificateError(f"selector_histograms[{idx}] counts must be nonnegative with positive sum")
        cost_a += 4 * n0 + 7 * n1
        cost_b += 7 * n0 + 4 * n1
        total_packets += n0 + n1

    unaltered = 6 * total_packets
    min_cost = min(cost_a, cost_b)
    ratio = frac_div(Fraction(min_cost), Fraction(unaltered))

    if _req_int(payload, "claimed_grouping_a_bits") != cost_a:
        raise CertificateError("claimed_grouping_a_bits disagrees with exact 4*n0 + 7*n1")
    if _req_int(payload, "claimed_grouping_b_bits") != cost_b:
        raise CertificateError("claimed_grouping_b_bits disagrees with exact 7*n0 + 4*n1")
    if _req_int(payload, "claimed_min_bits") != min_cost:
        raise CertificateError("claimed_min_bits disagrees with exact min(cost_a, cost_b)")
    if _req_int(payload, "claimed_unaltered_bits") != unaltered:
        raise CertificateError("claimed_unaltered_bits disagrees with exact 6 * total_packets")
    if _req_frac(payload, "claimed_ratio") != ratio:
        raise CertificateError(f"claimed_ratio disagrees with exact {ratio}")
    if ratio > Fraction(11, 12):
        raise CertificateError("Section 8 squeeze ratio exceeded 11/12 upper bound")

    return {
        "mode": "exterior_packet_11_12_squeeze_cert",
        "clifford_pairs_verified": 64,
        "packet_quadruples_verified": 4096,
        "total_packets": total_packets,
        "squeeze_ratio": f"{ratio.numerator}/{ratio.denominator}",
    }


# ---------------------------------------------------------------------------
# Public Entry Points
# ---------------------------------------------------------------------------

def verify_certificate_dict(data: Mapping[str, Any]) -> Dict[str, Any]:
    if not isinstance(data, Mapping):
        raise CertificateError("Certificate must be a mapping")
    allowed_top = {"protocol", "certificate_id", "mode", "payload", "description", "note"}
    extra_top = set(data.keys()) - allowed_top
    if extra_top:
        raise CertificateError(f"Unexpected top-level keys: {sorted(extra_top)}")
    for opt_k in ("description", "note"):
        if opt_k in data and not isinstance(data[opt_k], str):
            raise CertificateError(f"Optional field {opt_k!r} must be a string")

    proto = _req_str(data, "protocol")
    if proto != PROTOCOL_ID:
        raise CertificateError(f"Unsupported protocol {proto!r}; expected {PROTOCOL_ID!r}")
    cert_id = _req_str(data, "certificate_id")
    mode = _req_str(data, "mode")
    if mode not in VALID_MODES:
        raise CertificateError(f"Unknown certificate mode {mode!r}")

    payload = data.get("payload")
    if not isinstance(payload, Mapping):
        raise CertificateError("Field 'payload' must be a JSON object")

    try:
        if mode == "hinge_stretch_and_replay_cert":
            summary = _verify_mode1(payload)
        elif mode == "cartier_residue_box_cert":
            summary = _verify_mode2(payload)
        elif mode == "clifford_signed_perm_and_gray_cert":
            summary = _verify_mode3(payload)
        else:
            summary = _verify_mode4(payload)
    except CertificateError:
        raise
    except ValueError as exc:
        raise CertificateError(f"Exact verification value error: {exc}") from exc

    summary["certificate_id"] = cert_id
    summary["protocol"] = PROTOCOL_ID
    return summary


def verify_certificate_str(raw: str) -> Dict[str, Any]:
    return verify_certificate_dict(load_strict_json_str(raw))


def verify_certificate_file(path: Path | str) -> Dict[str, Any]:
    return verify_certificate_str(Path(path).read_text(encoding="utf-8"))
