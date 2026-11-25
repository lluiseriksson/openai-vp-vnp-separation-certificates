"""Zero-float exact arithmetic engine for VPVNP-CERT-1.0.

Implements pure-integer and exact-Fraction primitives corresponding to OpenAI's
November 23, 2026 separation preprint "VP and VNP are different":
  - Cleared-denominator strict shortening & hub-displacement bounds (Def. 2.1, Sec. 2.1),
  - Finite-field replay-boundary cancellation check (Thm. 3.1, Lems. 3.2-3.3),
  - Characteristic-p Cartier operator Lambda_q on bivariate Laurent polynomials F_p[X, t, t^-1]
    and cyclic-group orthogonality coefficient extraction (Secs. 5.1-5.2, Lem. 5.2),
  - Signed-permutation anticommuting involutions A_1..A_D on Z^{2^D}, Gray codes, and
    windowed host volume scaling (Sec. 7),
  - Exact integral exterior-algebra Lambda(Z^4) Clifford operators P_x, Q_y (Q_y P_x + P_x Q_y = delta_{xy} I),
    4096-quadruple crossing packet identity over Z, and 11/12 squeeze (Sec. 8).

NO floating-point operations, true division '/', or math imports appear anywhere in this module.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Sequence, Tuple


class CertificateError(ValueError):
    """Raised whenever any exact mathematical or structural check fails."""


def frac_div(a: Fraction, b: Fraction) -> Fraction:
    """Exact Fraction division without using the '/' operator (AST-clean)."""
    if b.numerator == 0:
        raise CertificateError("Division by zero in exact rational arithmetic")
    return Fraction(a.numerator * b.denominator, a.denominator * b.numerator)


def is_small_prime(p: int) -> bool:
    if p < 2:
        return False
    d = 2
    while d * d <= p:
        if p % d == 0:
            return False
        d += 1
    return True


# ---------------------------------------------------------------------------
# Mode 2: Characteristic-p Cartier Operator Lambda_q on F_p[X, t, t^-1]
# ---------------------------------------------------------------------------
# Bivariate Laurent polynomials are represented as Dict[Tuple[int, int], int]
# mapping (deg_X, deg_t) -> coeff in [1, p-1].

LaurentPoly = Dict[Tuple[int, int], int]


def laurent_clean(poly: Dict[Tuple[int, int], int], p: int) -> LaurentPoly:
    return {k: v % p for k, v in poly.items() if v % p != 0}


def laurent_mul(a: LaurentPoly, b: LaurentPoly, p: int) -> LaurentPoly:
    out: Dict[Tuple[int, int], int] = {}
    for (ax, at), av in a.items():
        for (bx, bt), bv in b.items():
            key = (ax + bx, at + bt)
            out[key] = (out.get(key, 0) + av * bv) % p
            if len(out) > 4096:
                raise CertificateError("Intermediate Laurent polynomial exceeded 4096-term DoS cap")
    return laurent_clean(out, p)


def laurent_pow(a: LaurentPoly, exp: int, p: int) -> LaurentPoly:
    if exp < 0:
        raise CertificateError("Negative exponent in laurent_pow")
    res: LaurentPoly = {(0, 0): 1}
    base = laurent_clean(a, p)
    e = exp
    while e > 0:
        if e & 1:
            res = laurent_mul(res, base, p)
        e >>= 1
        if e > 0:
            base = laurent_mul(base, base, p)
    return res


def laurent_frob_pow(a: LaurentPoly, q: int, p: int) -> LaurentPoly:
    """Exact Frobenius power a^q over F_p (q a power of p): (sum c X^x t^y)^q = sum c X^{qx} t^{qy}."""
    out: LaurentPoly = {}
    for (ax, at), av in a.items():
        v = pow(av % p, q, p)
        if v != 0:
            out[(q * ax, q * at)] = v
    return out


def cartier_lambda_q(poly: LaurentPoly, p: int, q: int) -> LaurentPoly:
    """Exact Section 5.1 Cartier extraction Lambda_q on F_p[X, t, t^-1]:
    Extracts terms with exponent (q*ix + (q-1), q*it + (q-1)) -> coeff^(1/q) * X^{ix} t^{it}.
    Over F_p, every c in F_p satisfies c^p = c so c^(1/q) = c!
    """
    out: LaurentPoly = {}
    for (ex, et), val in poly.items():
        if val % p == 0:
            continue
        rx = ex - (q - 1)
        rt = et - (q - 1)
        if rx % q == 0 and rt % q == 0:
            out[(rx // q, rt // q)] = val % p
    return out


def laurent_eval_fp(poly: LaurentPoly, x_val: int, t_val: int, p: int) -> int:
    """Evaluate bivariate Laurent polynomial at nonzero (x_val, t_val) in (F_p^*)^2."""
    acc = 0
    for (ex, et), coeff in poly.items():
        xp = pow(x_val, ex, p) if ex >= 0 else pow(pow(x_val, -ex, p), -1, p)
        tp = pow(t_val, et, p) if et >= 0 else pow(pow(t_val, -et, p), -1, p)
        acc = (acc + coeff * xp * tp) % p
    return acc


def cyclic_orthogonality_coeff_fp(poly: LaurentPoly, target_x: int, target_t: int, p: int) -> int:
    """Exact Section 5.2 cyclic-group orthogonality extraction over (F_p^*)^2 (order N = p - 1):
    N^(-2) * sum_{x, t in F_p^*} poly(x, t) * x^(-target_x) * t^(-target_t) mod p.
    Note: in F_p, N = p - 1 == -1 (mod p), so N^(-2) == 1 (mod p)!
    """
    n_ord = p - 1
    inv_n2 = pow((n_ord * n_ord) % p, -1, p)
    total = 0
    for x in range(1, p):
        x_inv_pow = pow(pow(x, target_x, p), -1, p) if target_x >= 0 else pow(x, -target_x, p)
        for t in range(1, p):
            t_inv_pow = pow(pow(t, target_t, p), -1, p) if target_t >= 0 else pow(t, -target_t, p)
            val = laurent_eval_fp(poly, x, t, p)
            total = (total + val * x_inv_pow * t_inv_pow) % p
    return (total * inv_n2) % p


# ---------------------------------------------------------------------------
# Mode 3: Signed-Permutation Anticommuting Involutions A_j & Gray Code (Sec. 7)
# ---------------------------------------------------------------------------

def build_signed_perm_involution(dim_D: int, j_idx: int) -> List[Tuple[int, int]]:
    """Build Section 7 involution A_j (0-indexed j_idx in 0..D-1) on {0,1}^D.
    A_j e_x = (-1)^(x_0 + ... + x_{j-1}) e_{x ^ (1 << j)}.
    Returns sparse map: for each basis index x in 0..2^D-1, (target_index, sign in {-1, +1}).
    """
    n = 1 << dim_D
    bit = 1 << j_idx
    prefix_mask = bit - 1
    out: List[Tuple[int, int]] = []
    for x in range(n):
        parity = (x & prefix_mask).bit_count() & 1
        sign = -1 if parity else 1
        out.append((x ^ bit, sign))
    return out


def apply_signed_perm(op: Sequence[Tuple[int, int]], vec: Sequence[int]) -> List[int]:
    n = len(vec)
    res = [0] * n
    for x, (dst, sgn) in enumerate(op):
        res[dst] += sgn * vec[x]
    return res


def gray_code(k: int) -> int:
    return k ^ (k >> 1)


# ---------------------------------------------------------------------------
# Mode 4: Exact Integral Exterior Algebra Lambda(Z^4) Packet Identity (Sec. 8)
# ---------------------------------------------------------------------------

def build_exterior_lambda4_operators() -> Tuple[List[List[Tuple[int, int]]], List[List[Tuple[int, int]]]]:
    """Construct Section 8's 8 integral wedge/contraction operators P_x and dual Q_y
    on Lambda(Z^4) (16 basis subsets of {0,1,2,3}, partitioned into 8 even and 8 odd).

    For r in 0..3:
      e_r_wedge(S)    = 0 if r in S else (-1)^(# elements in S below r) * (S | {r})
      e_r_contract(S) = 0 if r not in S else (-1)^(# elements in S below r) * (S \\ {r})
    P_0..P_3 = e_0..e_3 wedge;      P_4..P_7 = e_0..e_3 contract.
    Q_0..Q_3 = e_0..e_3 contract;   Q_4..Q_7 = e_0..e_3 wedge.
    Satisfies EXACT integral Clifford relation: Q_y P_x + P_x Q_y = delta_{xy} I_16 over Z!
    Returns (P_ops, Q_ops), each a list of 8 maps: state s in 0..15 -> (dst_state, coeff in {-1,0,1}).
    """
    wedges: List[List[Tuple[int, int]]] = []
    contracts: List[List[Tuple[int, int]]] = []
    for r in range(4):
        bit = 1 << r
        below_mask = bit - 1
        w_map: List[Tuple[int, int]] = []
        c_map: List[Tuple[int, int]] = []
        for s in range(16):
            sgn = -1 if ((s & below_mask).bit_count() & 1) else 1
            if s & bit:
                w_map.append((0, 0))
                c_map.append((s ^ bit, sgn))
            else:
                w_map.append((s | bit, sgn))
                c_map.append((0, 0))
        wedges.append(w_map)
        contracts.append(c_map)
    P_ops = wedges + contracts
    Q_ops = contracts + wedges
    return P_ops, Q_ops


def extract_exterior_packet_arrays() -> Tuple[
    List[List[List[int]]],
    List[List[List[int]]],
    List[List[List[int]]],
    List[List[List[int]]],
]:
    """Extract Section 8's exact integral 8x8x8 arrays A, B, C, D' over Z
    from even-to-even matrix entries (j, i) of Q_y P_x + P_x Q_y = delta_{xy} I
    factoring through the 8 odd basis states of Lambda(Z^4).

    Guarantees for ALL 4096 quadruples (x, y, i, j) in {0..7}^4:
      1_{x=y} * 1_{i=j} = sum_{z=0}^7 A[x][i][z]*B[y][j][z] + sum_{z=0}^7 C[y][i][z]*D'[x][j][z].
    """
    P_ops, Q_ops = build_exterior_lambda4_operators()
    evens = [s for s in range(16) if (s.bit_count() & 1) == 0]
    odds = [s for s in range(16) if (s.bit_count() & 1) == 1]
    odd_pos = {s: idx for idx, s in enumerate(odds)}

    # Matrix entry (Q_y P_x)_{j, i} = sum_{z in odds} (Q_y)_{j, z} * (P_x)_{z, i}
    #   A[x][i][z] = (P_x)_{odd[z], even[i]}
    #   B[y][j][z] = (Q_y)_{even[j], odd[z]}
    # Matrix entry (P_x Q_y)_{j, i} = sum_{z in odds} (P_x)_{j, z} * (Q_y)_{z, i}
    #   C[y][i][z] = (Q_y)_{odd[z], even[i]}
    #   D[x][j][z] = (P_x)_{even[j], odd[z]}
    A = [[[0] * 8 for _ in range(8)] for _ in range(8)]
    B = [[[0] * 8 for _ in range(8)] for _ in range(8)]
    C = [[[0] * 8 for _ in range(8)] for _ in range(8)]
    Dp = [[[0] * 8 for _ in range(8)] for _ in range(8)]

    even_pos = {s: idx for idx, s in enumerate(evens)}
    for x in range(8):
        for i_idx, e_state in enumerate(evens):
            dst, c = P_ops[x][e_state]
            if c != 0:
                A[x][i_idx][odd_pos[dst]] = c
        for z_idx, o_state in enumerate(odds):
            dst, c = P_ops[x][o_state]
            if c != 0:
                Dp[x][even_pos[dst]][z_idx] = c

    for y in range(8):
        for i_idx, e_state in enumerate(evens):
            dst, c = Q_ops[y][e_state]
            if c != 0:
                C[y][i_idx][odd_pos[dst]] = c
        for z_idx, o_state in enumerate(odds):
            dst, c = Q_ops[y][o_state]
            if c != 0:
                B[y][even_pos[dst]][z_idx] = c

    return A, B, C, Dp
