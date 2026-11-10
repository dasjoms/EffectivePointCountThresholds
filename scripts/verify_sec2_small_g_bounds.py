#!/usr/bin/env python3
"""
Computational checks for Section 2 (Theorems 2.1, 2.2, and 2.3(2)):
  - Theorem 2.1: N(5) <= 4 for q >= 10^5.
  - Theorem 2.2: N(6) <= 4 for q >= 10^6.
  - Theorem 2.3(2): N(7) <= 5 for q >= 10^6.

Computes the reduced cyclotomic norm differences E_3, E_4, and F_5(B) - F_5(A)
symbolically over Z, checks them against Res_T(Phi_d(T), P(T)) on random integer
specializations, and evaluates the rational dominance ratios at q_0 using the
Weil coefficient bounds |b_k| <= binom(g, k) * 2^k * q^(k/2).
"""

from fractions import Fraction
import math
import random
import sympy as sp

q, T = sp.symbols("q T")
u = q + 1
v = q - 1
ii, w, th = sp.symbols("ii w th")


def weil_poly_at_point(g, b_vals, qv):
    return sp.expand(
        sum(((-1) ** k) * b_vals[k] * (T**k) * ((T**2 + qv) ** (g - k)) for k in range(g + 1))
    )


def F4_reduced(g, bA, bB, gens):
    """Primitive polynomial E_4 = (F_4(B) - F_4(A)) / (4 * (q^2 + 1)) in Z[q, ...]."""
    gens_ii = [ii] + list(gens)
    mod_ii = sp.Poly(ii**2 + 1, *gens_ii, domain="ZZ")

    def re_im(bs):
        vi = sp.Poly(-v * ii, *gens_ii, domain="ZZ")
        acc = sp.Poly(0, *gens_ii, domain="ZZ")
        pw = sp.Poly(1, *gens_ii, domain="ZZ")
        for k in range(g, -1, -1):
            acc = acc + sp.Poly(((-1) ** k) * bs[k], *gens_ii, domain="ZZ") * pw
            if k > 0:
                _, pw = sp.div(pw * vi, mod_ii)
        # Extract coeff of ii^0 and ii^1:
        re_d, im_d = {}, {}
        for mon, c in acc.terms():
            if mon[0] == 0:
                re_d[mon[1:]] = c
            else:
                im_d[mon[1:]] = c
        return sp.Poly(re_d, *gens, domain="ZZ"), sp.Poly(im_d, *gens, domain="ZZ")

    RA, MA = re_im(bA)
    RB, MB = re_im(bB)
    diff = (RB + RA) * (RB - RA) + (MB + MA) * (MB - MA)
    div_p = sp.Poly(4 * (q**2 + 1), *gens, domain="ZZ")
    quo, rem = sp.div(diff, div_p)
    assert rem.is_zero
    return quo


def F3_reduced(g, bA, bB, gens):
    """Polynomial E_3 = (F_3(B) - F_3(A)) / 3 in Z[q, ...]."""
    gens_w = [w] + list(gens)
    mod_w_p = sp.Poly(w**2 + w + 1, *gens_w, domain="ZZ")

    def eval_z3(bs):
        z3 = sp.Poly(-q + (1 - q) * w, *gens_w, domain="ZZ")
        acc = sp.Poly(0, *gens_w, domain="ZZ")
        pw = sp.Poly(1, *gens_w, domain="ZZ")
        for k in range(g, -1, -1):
            acc = acc + sp.Poly(((-1) ** k) * bs[k], *gens_w, domain="ZZ") * pw
            if k > 0:
                _, pw = sp.div(pw * z3, mod_w_p)
        x_d, y_d = {}, {}
        for mon, c in acc.terms():
            if mon[0] == 0:
                x_d[mon[1:]] = c
            else:
                y_d[mon[1:]] = c
        X0 = sp.Poly(x_d, *gens, domain="ZZ")
        Y0 = sp.Poly(y_d, *gens, domain="ZZ")
        return X0 * X0 - X0 * Y0 + Y0 * Y0

    diff = eval_z3(bB) - eval_z3(bA)
    quo, rem = sp.div(diff, sp.Poly(3, *gens, domain="ZZ"))
    assert rem.is_zero
    return quo


def F5_diff_poly(g, bA, bB, gens):
    """Polynomial F_5(B) - F_5(A) in Z[q, ...] via DMP arithmetic."""
    gens_th = [th] + list(gens)
    mod_th_p = sp.Poly(th**2 + th - 1, *gens_th, domain="ZZ")
    trZ = sp.Poly(th * (q + 1), *gens_th, domain="ZZ")
    nmZ = sp.Poly(q**2 - q + 1 - q * th, *gens_th, domain="ZZ")

    def N_th(bs):
        U = sp.Poly(0, *gens_th, domain="ZZ")
        V = sp.Poly(bs[0], *gens_th, domain="ZZ")
        for k in range(1, g + 1):
            _, nU = sp.div(U * trZ + V, mod_th_p)
            _, nV = sp.div(
                -U * nmZ + sp.Poly(((-1) ** k) * bs[k], *gens_th, domain="ZZ"), mod_th_p
            )
            U, V = nU, nV
        _, res = sp.div(U * U * nmZ + U * V * trZ + V * V, mod_th_p)
        a0_d, a1_d = {}, {}
        for mon, c in res.terms():
            if mon[0] == 0:
                a0_d[mon[1:]] = c
            else:
                a1_d[mon[1:]] = c
        return sp.Poly(a0_d, *gens, domain="ZZ"), sp.Poly(a1_d, *gens, domain="ZZ")

    A0, A1 = N_th(bA)
    B0, B1 = N_th(bB)
    d0, d1 = B0 - A0, B1 - A1
    return (2 * A0 - A1) * d0 + (-A0 - 2 * A1) * d1 + d0 * d0 - d0 * d1 - d1 * d1


def cross_check_resultant_identities():
    """Verify F4_reduced, F3_reduced, F5_diff_poly match Res_T(Phi_d, P) on test points."""
    rng = random.Random(260628989)
    for g in [5, 6, 7]:
        qv = rng.randint(5, 19)
        bA_v = [1] + [rng.randint(-9, 9) for _ in range(g)]
        d2v, d3v = rng.randint(-3, 3), rng.randint(-3, 3)
        bB_v = list(bA_v)
        uv = qv + 1
        if g == 5:
            bB_v[2] += d2v
            bB_v[4] -= uv * uv * d2v
            bB_v[3] += d3v
            bB_v[5] -= uv * uv * d3v
        elif g == 6:
            m4v = rng.randint(-3, 3)
            bB_v[2] += d2v
            bB_v[4] += m4v - uv * uv * d2v
            bB_v[6] -= uv * uv * m4v
            bB_v[3] += d3v
            bB_v[5] -= uv * uv * d3v
        else:
            m4v, m5v = rng.randint(-3, 3), rng.randint(-3, 3)
            bB_v[2] += d2v
            bB_v[4] += m4v - uv * uv * d2v
            bB_v[6] -= uv * uv * m4v
            bB_v[3] += d3v
            bB_v[5] += m5v - uv * uv * d3v
            bB_v[7] -= uv * uv * m5v
        PA_v = weil_poly_at_point(g, bA_v, qv)
        PB_v = weil_poly_at_point(g, bB_v, qv)
        for d in [1, 2]:
            assert sp.resultant(sp.cyclotomic_poly(d, T), PB_v, T) == sp.resultant(
                sp.cyclotomic_poly(d, T), PA_v, T
            )
        # Symbolic specialized at bA_v, bB_v (keep q symbolic first for division):
        bA_s = [sp.Integer(v_i) for v_i in bA_v]
        if g == 5:
            bB_s = [
                sp.Integer(1),
                bA_s[1],
                bA_s[2] + d2v,
                bA_s[3] + d3v,
                bA_s[4] - u**2 * d2v,
                bA_s[5] - u**2 * d3v,
            ]
        elif g == 6:
            bB_s = [
                sp.Integer(1),
                bA_s[1],
                bA_s[2] + d2v,
                bA_s[3] + d3v,
                bA_s[4] + m4v - u**2 * d2v,
                bA_s[5] - u**2 * d3v,
                bA_s[6] - u**2 * m4v,
            ]
        else:
            bB_s = [
                sp.Integer(1),
                bA_s[1],
                bA_s[2] + d2v,
                bA_s[3] + d3v,
                bA_s[4] + m4v - u**2 * d2v,
                bA_s[5] + m5v - u**2 * d3v,
                bA_s[6] - u**2 * m4v,
                bA_s[7] - u**2 * m5v,
            ]
        r4 = int(
            sp.resultant(sp.cyclotomic_poly(4, T), PB_v, T)
            - sp.resultant(sp.cyclotomic_poly(4, T), PA_v, T)
        )
        assert r4 == 4 * (qv * qv + 1) * int(F4_reduced(g, bA_s, bB_s, [q]).eval(qv))
        r3 = int(
            sp.resultant(sp.cyclotomic_poly(3, T), PB_v, T)
            - sp.resultant(sp.cyclotomic_poly(3, T), PA_v, T)
        )
        assert r3 == 3 * int(F3_reduced(g, bA_s, bB_s, [q]).eval(qv))
        if g == 7:
            r5 = int(
                sp.resultant(sp.cyclotomic_poly(5, T), PB_v, T)
                - sp.resultant(sp.cyclotomic_poly(5, T), PA_v, T)
            )
            assert r5 == int(F5_diff_poly(g, bA_s, bB_s, [q]).eval(qv))


def check_dominance(poly, weight_fn, lead_pred, q0):
    """
    Check that the single leading monomial matching `lead_pred(mon)` strictly
    dominates the sum of upper bounds of all remaining monomials for q >= q0.
    Here `mon[0]` is the exponent of q (= s^2), and `weight_fn(mon)` returns
    `(coeff_bound, extra_s_exp)` for the remaining variables at s = sqrt(q).
    Note: for non-square q0 (such as q0 = 10^5), s0 = isqrt(q0) <= sqrt(q0) <= sqrt(q)
    satisfies 1/s0 >= 1/sqrt(q); since tot_s <= D_s, (1/s0)^(D_s - tot_s) rigorously
    upper-bounds (1/sqrt(q))^(D_s - tot_s) for all q >= q0.
    """
    s0 = int(math.isqrt(q0))
    assert s0 * s0 <= q0
    leads = [(m, int(c)) for m, c in poly.terms() if lead_pred(m)]
    assert leads, "No leading monomial matched"
    top_qm = max(m[0] for m, _ in leads)
    top_c = abs(next(c for m, c in leads if m[0] == top_qm))
    D_s = 2 * top_qm
    rem_sum = Fraction(0)
    for m, c in poly.terms():
        if lead_pred(m) and m[0] == top_qm:
            continue
        cb, ws = weight_fn(m)
        tot_s = 2 * m[0] + ws
        assert tot_s <= D_s, f"Weight overflow at {m}: {tot_s} > {D_s}"
        rem_sum += Fraction(abs(int(c))) * cb * (Fraction(1, s0) ** (D_s - tot_s))
    ratio = float(Fraction(top_c) / rem_sum)
    assert rem_sum < top_c, f"Dominance failed: ratio={ratio}"
    return ratio


def sum_terms_bound(terms, weight_fn, target_Ds, q0):
    s0 = int(math.isqrt(q0))
    assert s0 * s0 <= q0
    acc = Fraction(0)
    for m, c in terms:
        cb, ws = weight_fn(m)
        tot_s = 2 * m[0] + ws
        assert tot_s <= target_Ds, f"Weight overflow at {m}: {tot_s} > {target_Ds}"
        acc += Fraction(abs(int(c))) * cb * (Fraction(1, s0) ** (target_Ds - tot_s))
    return acc


def verify_g5():
    g, q0 = 5, 10**5
    # Integer check of (160 * q0^(3/2) * (q0 + 1)^2 + 64 * q0^(5/2)) < (q0 + 1)^4:
    assert ((160 * ((q0 + 1) ** 2) + 64 * q0) ** 2) * (q0**3) < ((q0 + 1) ** 8)
    b = [sp.Integer(1)] + [sp.Symbol(f"b{k}") for k in range(1, g + 1)]
    Bc = [Fraction(1)] + [Fraction(math.comb(g, k) * (2**k)) for k in range(1, g + 1)]
    d2, d3 = sp.symbols("d2 d3")
    bB = [sp.Integer(1), b[1], b[2] + d2, b[3] + d3, b[4] - u**2 * d2, b[5] - u**2 * d3]

    # Step 2: d2 = 0 from F4_reduced (gens: q, d2, d3, b1..b5):
    P4 = F4_reduced(g, b, bB, [q, d2, d3, *b[1:]])

    def w_g5_s2(m):
        bc = math.prod(Bc[k] ** m[2 + k] for k in range(1, g + 1))
        bs = sum(k * m[2 + k] for k in range(1, g + 1))
        if m[1] >= 1:
            return (Fraction(160) ** (m[1] - 1)) * (Fraction(64) ** m[2]) * bc, m[2] + bs
        return (Fraction(64) ** m[2]) * bc, m[2] + bs

    r2 = check_dominance(P4, w_g5_s2, lambda m: m[1] == 1 and sum(m[2:]) == 0, q0)

    # Step 3: d3 = 0 from F3_reduced|_{d2=0} (gens: q, d3, b1..b5):
    bB3 = [sp.Integer(1), b[1], b[2], b[3] + d3, b[4], b[5] - u**2 * d3]
    P3 = F3_reduced(g, b, bB3, [q, d3, *b[1:]])
    r3 = check_dominance(
        P3,
        lambda m: (
            (Fraction(64) ** (m[1] - 1)) * math.prod(Bc[k] ** m[1 + k] for k in range(1, g + 1)),
            (m[1] - 1) + sum(k * m[1 + k] for k in range(1, g + 1)),
        ),
        lambda m: m[1] == 1 and sum(m[2:]) == 0,
        q0,
    )
    print(f"  g = 5, N = 4 (q >= 10^5): d_2 ratio {r2:.2f}, d_3 ratio {r3:.2f}.")


def verify_g6():
    g, q0 = 6, 10**6
    # Integer check of (320 * q0^(3/2) * (q0 + 1)^2 + 384 * q0^(5/2)) < (q0 + 1)^4:
    assert ((320 * ((q0 + 1) ** 2) + 384 * q0) ** 2) * (q0**3) < ((q0 + 1) ** 8)
    # Note (480 * q^2 + 128 * q) < 480 * (q + 1)^2 for all q >= 1 since 128 < 2 * 480.
    b = [sp.Integer(1)] + [sp.Symbol(f"b{k}") for k in range(1, g + 1)]
    Bc = [Fraction(1)] + [Fraction(math.comb(g, k) * (2**k)) for k in range(1, g + 1)]
    d2, d3, m4 = sp.symbols("d2 d3 m4")
    bB = [
        sp.Integer(1),
        b[1],
        b[2] + d2,
        b[3] + d3,
        b[4] + m4 - u**2 * d2,
        b[5] - u**2 * d3,
        b[6] - u**2 * m4,
    ]
    P4 = F4_reduced(g, b, bB, [q, d2, d3, m4, *b[1:]])

    def w_g6_s2(m):
        bc = math.prod(Bc[k] ** m[3 + k] for k in range(1, g + 1))
        bs = sum(k * m[3 + k] for k in range(1, g + 1))
        c_d2 = Fraction(480) ** (m[1] - 1) if m[1] >= 1 else Fraction(1)
        return c_d2 * (Fraction(384) ** m[2]) * (Fraction(128) ** m[3]) * bc, m[2] + 2 * m[3] + bs

    r2 = check_dominance(P4, w_g6_s2, lambda m: m[1] == 1 and sum(m[2:]) == 0, q0)

    # Step 3: d2 = 0 => couple P4_0 and P3_0 on (d3, m4):
    bB0 = [x.subs(d2, 0) for x in bB]
    P4_0 = F4_reduced(g, b, bB0, [q, d3, m4, *b[1:]])
    # First check d3 = 0 => m4 = 0:
    P4_d30 = F4_reduced(g, b, [x.subs(d3, 0) for x in bB0], [q, m4, *b[1:]])
    check_dominance(
        P4_d30,
        lambda m: (
            (Fraction(128) ** (m[1] - 1)) * math.prod(Bc[k] ** m[1 + k] for k in range(1, g + 1)),
            2 * (m[1] - 1) + sum(k * m[1 + k] for k in range(1, g + 1)),
        ),
        lambda m: m[1] == 1 and sum(m[2:]) == 0,
        q0,
    )
    # For |d3| >= 1, bound |m4| <= C_m4 * s * |d3| from P4_0 (top m4 term is q^6 * m4, Ds=12):
    top_qm = max(m[0] for m, _ in P4_0.terms() if m[2] == 1 and m[1] == 0 and sum(m[3:]) == 0)
    Ds_m4 = 2 * top_qm
    rem_m4 = sum_terms_bound(
        [
            (m, c)
            for m, c in P4_0.terms()
            if m[2] >= 1 and not (m[0] == top_qm and m[2] == 1 and m[1] == 0 and sum(m[3:]) == 0)
        ],
        lambda m: (
            (Fraction(384) ** m[1])
            * (Fraction(128) ** (m[2] - 1))
            * math.prod(Bc[k] ** m[2 + k] for k in range(1, g + 1)),
            m[1] + 2 * (m[2] - 1) + sum(k * m[2 + k] for k in range(1, g + 1)),
        ),
        Ds_m4,
        q0,
    )
    rem_d3 = sum_terms_bound(
        [(m, c) for m, c in P4_0.terms() if m[2] == 0 and m[1] >= 1],
        lambda m: (
            (Fraction(384) ** (m[1] - 1)) * math.prod(Bc[k] ** m[2 + k] for k in range(1, g + 1)),
            (m[1] - 1) + sum(k * m[2 + k] for k in range(1, g + 1)),
        ),
        Ds_m4 + 1,
        q0,
    )
    C_m4_per_d3 = rem_d3 / (Fraction(1) - rem_m4)  # |m4| <= C_m4_per_d3 * s^(+1) * |d3|

    P3_0 = F3_reduced(g, b, bB0, [q, d3, m4, *b[1:]])

    def w_g6_s3(m):
        bc = math.prod(Bc[k] ** m[2 + k] for k in range(1, g + 1))
        bs = sum(k * m[2 + k] for k in range(1, g + 1))
        if m[1] >= 1:
            return (Fraction(384) ** (m[1] - 1)) * (Fraction(128) ** m[2]) * bc, (m[1] - 1) + 2 * m[2] + bs
        return C_m4_per_d3 * (Fraction(128) ** (m[2] - 1)) * bc, 1 + 2 * (m[2] - 1) + bs

    r3 = check_dominance(P3_0, w_g6_s3, lambda m: m[1] == 1 and sum(m[2:]) == 0, q0)
    print(f"  g = 6, N = 4 (q >= 10^6): d_2 ratio {r2:.2f}, (d_3, m_4) ratio {r3:.2f}.")


def verify_g7():
    g, q0 = 7, 10**6
    # Integer check of (560*q0^(3/2)*(q0+1)^4 + 1344*q0^(5/2)*(q0+1)^2 + 256*q0^(7/2)) < (q0+1)^6:
    assert (
        (560 * ((q0 + 1) ** 4) + 1344 * q0 * ((q0 + 1) ** 2) + 256 * (q0**2)) ** 2
    ) * (q0**3) < ((q0 + 1) ** 12)
    # Note (1120*q^2 + 896*q) < 1120*(q+1)^2 and (1344*q^2 + 256*q) < 1344*(q+1)^2 for all q >= 1.
    b = [sp.Integer(1)] + [sp.Symbol(f"b{k}") for k in range(1, g + 1)]
    Bc = [Fraction(1)] + [Fraction(math.comb(g, k) * (2**k)) for k in range(1, g + 1)]
    d2, d3, m4, m5 = sp.symbols("d2 d3 m4 m5")
    bB = [
        sp.Integer(1),
        b[1],
        b[2] + d2,
        b[3] + d3,
        b[4] + m4 - u**2 * d2,
        b[5] + m5 - u**2 * d3,
        b[6] - u**2 * m4,
        b[7] - u**2 * m5,
    ]
    P4 = F4_reduced(g, b, bB, [q, d2, d3, m4, m5, *b[1:]])

    def w_g7_s2(m):
        bc = math.prod(Bc[k] ** m[4 + k] for k in range(1, g + 1))
        bs = sum(k * m[4 + k] for k in range(1, g + 1))
        c_d2 = Fraction(1120) ** (m[1] - 1) if m[1] >= 1 else Fraction(1)
        return (
            c_d2 * (Fraction(1344) ** m[2]) * (Fraction(896) ** m[3]) * (Fraction(256) ** m[4]) * bc,
            m[2] + 2 * m[3] + 3 * m[4] + bs,
        )

    r2 = check_dominance(P4, w_g7_s2, lambda m: m[1] == 1 and sum(m[2:]) == 0, q0)

    # Step 3 (d2 = 0): bound |m4| / |d3| <= C_m4_d3 * s from P4_0 and eliminate d3 via P3_0:
    bB0 = [x.subs(d2, 0) for x in bB]
    P4_0 = F4_reduced(g, b, bB0, [q, d3, m4, m5, *b[1:]])
    top_qm = max(
        m[0] for m, _ in P4_0.terms() if m[2] == 1 and m[1] == 0 and m[3] == 0 and sum(m[4:]) == 0
    )
    Ds_m4 = 2 * top_qm
    rem_m4 = sum_terms_bound(
        [
            (m, c)
            for m, c in P4_0.terms()
            if m[2] >= 1
            and not (m[0] == top_qm and m[2] == 1 and m[1] == 0 and m[3] == 0 and sum(m[4:]) == 0)
        ],
        lambda m: (
            (Fraction(1344) ** m[1])
            * (Fraction(896) ** (m[2] - 1))
            * (Fraction(256) ** m[3])
            * math.prod(Bc[k] ** m[3 + k] for k in range(1, g + 1)),
            m[1] + 2 * (m[2] - 1) + 3 * m[3] + sum(k * m[3 + k] for k in range(1, g + 1)),
        ),
        Ds_m4,
        q0,
    )
    rem_d3_div = sum_terms_bound(
        [(m, c) for m, c in P4_0.terms() if m[2] == 0 and m[1] >= 1],
        lambda m: (
            (Fraction(1344) ** (m[1] - 1))
            * (Fraction(256) ** m[3])
            * math.prod(Bc[k] ** m[3 + k] for k in range(1, g + 1)),
            (m[1] - 1) + 3 * m[3] + sum(k * m[3 + k] for k in range(1, g + 1)),
        ),
        Ds_m4 + 1,
        q0,
    )
    rem_m5_only = sum_terms_bound(
        [(m, c) for m, c in P4_0.terms() if m[2] == 0 and m[1] == 0 and m[3] >= 1],
        lambda m: (
            (Fraction(256) ** m[3]) * math.prod(Bc[k] ** m[3 + k] for k in range(1, g + 1)),
            3 * m[3] + sum(k * m[3 + k] for k in range(1, g + 1)),
        ),
        Ds_m4 + 1,
        q0,
    )
    C_m4_d3 = (rem_d3_div + rem_m5_only) / (Fraction(1) - rem_m4)

    P3_0 = F3_reduced(g, b, bB0, [q, d3, m4, m5, *b[1:]])

    def w_g7_s3(m):
        bc = math.prod(Bc[k] ** m[3 + k] for k in range(1, g + 1))
        bs = sum(k * m[3 + k] for k in range(1, g + 1))
        if m[1] >= 1:
            return (
                (Fraction(1344) ** (m[1] - 1)) * (Fraction(896) ** m[2]) * (Fraction(256) ** m[3]) * bc,
                (m[1] - 1) + 2 * m[2] + 3 * m[3] + bs,
            )
        if m[2] >= 1:
            return (
                C_m4_d3 * (Fraction(896) ** (m[2] - 1)) * (Fraction(256) ** m[3]) * bc,
                1 + 2 * (m[2] - 1) + 3 * m[3] + bs,
            )
        return (Fraction(256) ** m[3]) * bc, 3 * m[3] + bs

    r3 = check_dominance(P3_0, w_g7_s3, lambda m: m[1] == 1 and sum(m[2:]) == 0, q0)

    # Step 4 (d2 = d3 = 0): couple P4_00 and P5_00 on (m4, m5):
    bB00 = [x.subs({d2: 0, d3: 0}) for x in bB]
    P4_00 = F4_reduced(g, b, bB00, [q, m4, m5, *b[1:]])
    # First check m5 = 0 => m4 = 0:
    P4_m50 = F4_reduced(g, b, [x.subs(m5, 0) for x in bB00], [q, m4, *b[1:]])
    check_dominance(
        P4_m50,
        lambda m: (
            (Fraction(896) ** (m[1] - 1)) * math.prod(Bc[k] ** m[1 + k] for k in range(1, g + 1)),
            2 * (m[1] - 1) + sum(k * m[1 + k] for k in range(1, g + 1)),
        ),
        lambda m: m[1] == 1 and sum(m[2:]) == 0,
        q0,
    )
    # For |m5| >= 1, bound |m4| <= C_alpha * s^(-3) * |m5| (so |m4| <= 256 * C_alpha * s^0):
    top_qm00 = max(m[0] for m, _ in P4_00.terms() if m[1] == 1 and m[2] == 0 and sum(m[3:]) == 0)
    Ds00 = 2 * top_qm00
    rem00_m4 = sum_terms_bound(
        [
            (m, c)
            for m, c in P4_00.terms()
            if m[1] >= 1 and not (m[0] == top_qm00 and m[1] == 1 and m[2] == 0 and sum(m[3:]) == 0)
        ],
        lambda m: (
            (Fraction(896) ** (m[1] - 1))
            * (Fraction(256) ** m[2])
            * math.prod(Bc[k] ** m[2 + k] for k in range(1, g + 1)),
            2 * (m[1] - 1) + 3 * m[2] + sum(k * m[2 + k] for k in range(1, g + 1)),
        ),
        Ds00,
        q0,
    )
    rem00_m5 = sum_terms_bound(
        [(m, c) for m, c in P4_00.terms() if m[1] == 0 and m[2] >= 1],
        lambda m: (
            (Fraction(256) ** (m[2] - 1)) * math.prod(Bc[k] ** m[2 + k] for k in range(1, g + 1)),
            3 * (m[2] - 1) + sum(k * m[2 + k] for k in range(1, g + 1)),
        ),
        Ds00 - 3,
        q0,
    )
    C_alpha = rem00_m5 / (Fraction(1) - rem00_m4)
    C_M4_max = C_alpha * 256  # |m4| <= C_M4_max * s^0

    P5_00 = F5_diff_poly(g, b, bB00, [q, m4, m5, *b[1:]])

    def w_g7_s5(m):
        bc = math.prod(Bc[k] ** m[2 + k] for k in range(1, g + 1))
        bs = sum(k * m[2 + k] for k in range(1, g + 1))
        if m[2] >= 1:
            return (C_M4_max ** m[1]) * (Fraction(256) ** (m[2] - 1)) * bc, 3 * (m[2] - 1) + bs
        return C_alpha * (C_M4_max ** (m[1] - 1)) * bc, -3 + bs

    r5 = check_dominance(P5_00, w_g7_s5, lambda m: m[2] == 1 and m[1] == 0 and sum(m[3:]) == 0, q0)
    print(
        f"  g = 7, N = 5 (q >= 10^6): d_2 ratio {r2:.2f}, "
        f"d_3 ratio {r3:.2f}, (m_4, m_5) ratio {r5:.2f}."
    )


def main():
    print("Section 2: resultant identities and dominance bounds (g = 5, 6, 7)")
    cross_check_resultant_identities()
    print("  Resultant identities for E_3, E_4, and F_5 matched sp.resultant on test specializations.")
    verify_g5()
    verify_g6()
    verify_g7()


if __name__ == "__main__":
    main()
