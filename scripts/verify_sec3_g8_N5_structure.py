#!/usr/bin/env python3
"""
Computational checks for Section 3, Proposition 3.2(1) (g = 8, N = 5):
  1. Archimedean elimination on (E_3, E_4, E_5) for q >= 10^8:
     Using integer and rational dominance bounds, checks that d_1 = d_2 = d_3 = m_5 = nu_6 = 0,
     so every collision on c_1, ..., c_5 for q >= 10^8 takes the form
       P_B(T) - P_A(T) = m_4 * T^4 * (T^4 - 1) * (T^4 - q^4),   1 <= |m_4| <= 512
     (and |m_4| <= 520 for q >= 12 whenever this difference form holds).
  2. Large-q asymptotics and Cauchy-Schwarz bounds:
     - Checks F_1(B) = F_1(A), F_2(B) = F_2(A), F_4(B) = F_4(A) for the single-parameter difference.
     - Computes the leading s-powers of (F_3(B) - F_3(A)) / (3 m_4) and (F_5(B) - F_5(A)) / (5 m_4),
       confirming r_2 = a_1^2 and t_6 = a_1^3 + t_3^2 + o(1).
     - Computes the Newton-sum expressions 8*p_4 - p_2^2 = 128 - 20*a_1^2 and
       (p_2*p_6 - p_4^2)|_{a_1=2} = -144 - 36*t_3^2.
"""

from fractions import Fraction
import math
from pathlib import Path
import sys
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_sec2_small_g_bounds import (
    F3_reduced,
    F4_reduced,
    F5_diff_poly,
    check_dominance,
    q,
    sum_terms_bound,
    u,
    v,
)


def check_g8_elimination(q0=10**8):
    """Check d_1 = d_2 = d_3 = m_5 = nu_6 = 0 via rational dominance bounds for q >= q0."""
    g = 8
    s0 = math.isqrt(q0)
    assert s0 * s0 == q0
    Bc = [Fraction(1)] + [Fraction(math.comb(g, k) * (2**k)) for k in range(1, g + 1)]
    b = [sp.Integer(1)] + [sp.Symbol(f"b{k}") for k in range(1, g + 1)]

    # Step 1: d_1 = 0 from F_1(B) = F_1(A) and F_2(B) = F_2(A).
    # Since F_1 = F_2 = 0 <=> u^2 - X^2 divides Delta h(X), equating odd coeffs gives
    #   d_7 + u^2 d_5 + u^4 d_3 + u^6 d_1 = 0,
    # where |d_k| <= 2 * Bc[k] * q^(k/2) = (896*q^(3/2), 3584*q^(5/2), 2048*q^(7/2)) for k = 3, 5, 7:
    D_max = [Fraction(0)] + [2 * Bc[k] for k in range(1, g + 1)]
    assert (int(D_max[3]), int(D_max[4]), int(D_max[5]), int(D_max[6]), int(D_max[7]), int(D_max[8])) == (
        896,
        2240,
        3584,
        3584,
        2048,
        512,
    )
    assert (
        (int(D_max[3]) * ((q0 + 1) ** 4) + int(D_max[5]) * q0 * ((q0 + 1) ** 2) + int(D_max[7]) * (q0**2))
        ** 2
    ) * (q0**3) < ((q0 + 1) ** 12)

    d2, d3, m4, m5, mu6, nu6, r6, c1s, c2s = sp.symbols("d2 d3 m4 m5 mu6 nu6 r6 c1s c2s")

    # Step 2: With d_1 = 0, F_1 = F_2 = 0 gives
    #   Delta h(X) = d_2*(X^6 - u^2*X^4) + d_3*(X^5 - u^2*X^3) + m_4*(X^4 - u^2*X^2)
    #                + m_5*(X^3 - u^2*X) + mu_6*(X^2 - u^2),
    # so d_8 = -u^2 mu_6, d_7 = -u^2 m_5, d_6 = mu_6 - u^2 m_4, d_5 = m_5 - u^2 d_3, d_4 = m_4 - u^2 d_2.
    # Dividing successively by u^2 = (q + 1)^2 gives, for all q >= 1:
    #   |mu_6| < 512*q^2,  |m_5| < 2048*q^(3/2),  |m_4| < 3584*q,  |d_3| < 3584*q^(1/2),  |d_2| < 2240.
    assert int(D_max[6]) * (q0**3) + int(D_max[8]) * (q0**2) < int(D_max[6]) * q0 * ((q0 + 1) ** 2)
    assert int(D_max[5]) * (q0**2) + int(D_max[7]) * q0 < int(D_max[5]) * ((q0 + 1) ** 2)
    assert int(D_max[4]) * (q0**2) + int(D_max[6]) * q0 < int(D_max[4]) * ((q0 + 1) ** 2)

    bB_s2 = [
        sp.Integer(1),
        b[1],
        b[2] + d2,
        b[3] + d3,
        b[4] + m4 - u**2 * d2,
        b[5] + m5 - u**2 * d3,
        b[6] + mu6 - u**2 * m4,
        b[7] - u**2 * m5,
        b[8] - u**2 * mu6,
    ]
    P4_s2 = F4_reduced(g, b, bB_s2, [q, d2, d3, m4, m5, mu6, *b[1:]])

    def w_s2(m):
        bc = math.prod(Bc[k] ** m[5 + k] for k in range(1, g + 1))
        bs = sum(k * m[5 + k] for k in range(1, g + 1))
        c_d2 = D_max[4] ** (m[1] - 1) if m[1] >= 1 else Fraction(1)
        return (
            c_d2
            * (D_max[5] ** m[2])
            * (D_max[6] ** m[3])
            * (D_max[7] ** m[4])
            * (D_max[8] ** m[5])
            * bc,
            m[2] + 2 * m[3] + 3 * m[4] + 4 * m[5] + bs,
        )

    r_d2 = check_dominance(P4_s2, w_s2, lambda m: m[1] == 1 and sum(m[2:]) == 0, q0)

    # Step 3: With d_2 = 0, eliminate d_3 = 0 from coupled (P4_0, P3_0):
    bB_s3 = [x.subs(d2, 0) for x in bB_s2]
    P4_0 = F4_reduced(g, b, bB_s3, [q, d3, m4, m5, mu6, *b[1:]])
    # In P4_0, top m_4 term is q^10 * m_4 (Ds = 20); isolate |m_4| / |d_3| <= C_m4_d3 * q^(1/2) when |d_3| >= 1:
    rem_m4 = sum_terms_bound(
        [
            (m, c)
            for m, c in P4_0.terms()
            if m[2] >= 1 and not (m[0] == 10 and m[2] == 1 and m[1] == 0 and m[3] == 0 and m[4] == 0 and sum(m[5:]) == 0)
        ],
        lambda m: (
            (D_max[5] ** m[1])
            * (D_max[6] ** (m[2] - 1))
            * (D_max[7] ** m[3])
            * (D_max[8] ** m[4])
            * math.prod(Bc[k] ** m[4 + k] for k in range(1, g + 1)),
            m[1] + 2 * (m[2] - 1) + 3 * m[3] + 4 * m[4] + sum(k * m[4 + k] for k in range(1, g + 1)),
        ),
        20,
        q0,
    )
    rem_d3_div = sum_terms_bound(
        [(m, c) for m, c in P4_0.terms() if m[2] == 0 and m[1] >= 1],
        lambda m: (
            (D_max[5] ** (m[1] - 1))
            * (D_max[7] ** m[3])
            * (D_max[8] ** m[4])
            * math.prod(Bc[k] ** m[4 + k] for k in range(1, g + 1)),
            (m[1] - 1) + 3 * m[3] + 4 * m[4] + sum(k * m[4 + k] for k in range(1, g + 1)),
        ),
        21,
        q0,
    )
    rem_rest = sum_terms_bound(
        [(m, c) for m, c in P4_0.terms() if m[2] == 0 and m[1] == 0 and (m[3] >= 1 or m[4] >= 1)],
        lambda m: (
            (D_max[7] ** m[3])
            * (D_max[8] ** m[4])
            * math.prod(Bc[k] ** m[4 + k] for k in range(1, g + 1)),
            3 * m[3] + 4 * m[4] + sum(k * m[4 + k] for k in range(1, g + 1)),
        ),
        21,
        q0,
    )
    C_m4_d3 = (rem_d3_div + rem_rest) / (Fraction(1) - rem_m4)

    P3_0 = F3_reduced(g, b, bB_s3, [q, d3, m4, m5, mu6, *b[1:]])

    def w_s3(m):
        bc = math.prod(Bc[k] ** m[4 + k] for k in range(1, g + 1))
        bs = sum(k * m[4 + k] for k in range(1, g + 1))
        if m[1] >= 1:
            return (
                (D_max[5] ** (m[1] - 1))
                * (D_max[6] ** m[2])
                * (D_max[7] ** m[3])
                * (D_max[8] ** m[4])
                * bc,
                (m[1] - 1) + 2 * m[2] + 3 * m[3] + 4 * m[4] + bs,
            )
        if m[2] >= 1:
            return (
                C_m4_d3
                * (D_max[6] ** (m[2] - 1))
                * (D_max[7] ** m[3])
                * (D_max[8] ** m[4])
                * bc,
                1 + 2 * (m[2] - 1) + 3 * m[3] + 4 * m[4] + bs,
            )
        return (D_max[7] ** m[3]) * (D_max[8] ** m[4]) * bc, 3 * m[3] + 4 * m[4] + bs

    r_d3 = check_dominance(P3_0, w_s3, lambda m: m[1] == 1 and sum(m[2:]) == 0, q0)

    # Also bound |m_4| <= M4_APRIORI when d_3 = 0 directly from P4_0|_{d_3 = 0}:
    P4_00 = F4_reduced(g, b, [x.subs(d3, 0) for x in bB_s3], [q, m4, m5, mu6, *b[1:]])
    rem00_m4 = sum_terms_bound(
        [
            (m, c)
            for m, c in P4_00.terms()
            if m[1] >= 1 and not (m[0] == 10 and m[1] == 1 and m[2] == 0 and m[3] == 0 and sum(m[4:]) == 0)
        ],
        lambda m: (
            (D_max[6] ** (m[1] - 1))
            * (D_max[7] ** m[2])
            * (D_max[8] ** m[3])
            * math.prod(Bc[k] ** m[3 + k] for k in range(1, g + 1)),
            2 * (m[1] - 1) + 3 * m[2] + 4 * m[3] + sum(k * m[3 + k] for k in range(1, g + 1)),
        ),
        20,
        q0,
    )
    rem00_rest = sum_terms_bound(
        [(m, c) for m, c in P4_00.terms() if m[1] == 0 and (m[2] >= 1 or m[3] >= 1)],
        lambda m: (
            (D_max[7] ** m[2])
            * (D_max[8] ** m[3])
            * math.prod(Bc[k] ** m[3 + k] for k in range(1, g + 1)),
            3 * m[2] + 4 * m[3] + sum(k * m[3 + k] for k in range(1, g + 1)),
        ),
        20,
        q0,
    )
    M4_APRIORI = Fraction(int(math.floor(rem00_rest / (Fraction(1) - rem00_m4))))
    M5_APRIORI = Fraction(2048)
    NU6_APRIORI = Fraction(512) + M4_APRIORI  # |nu_6| = |mu_6 - v^2 m_4| < (512 + M4_APRIORI)*q^2

    # Step 4: Set mu_6 = v^2 * m_4 + nu_6 and eliminate m_5 = 0, nu_6 = 0 from coupled (E_4, E_5, E_3):
    bB = [
        sp.Integer(1),
        b[1],
        b[2],
        b[3],
        b[4] + m4,
        b[5] + m5,
        b[6] + (v**2 - u**2) * m4 + nu6,
        b[7] - u**2 * m5,
        b[8] - u**2 * (v**2 * m4 + nu6),
    ]
    P4_check = F4_reduced(g, b, bB, [q, m4, m5, nu6, *b[1:]])
    assert all(m[1] == 0 for m, _ in P4_check.terms()), "m_4 should cancel identically in E_4"

    bB_no_m4 = [x.subs(m4, 0) for x in bB]
    # 4a: m_5 = 0 => nu_6 = 0 from F_4 = 0:
    P4_m50 = F4_reduced(g, b, [x.subs(m5, 0) for x in bB_no_m4], [q, nu6, *b[1:]])
    check_dominance(
        P4_m50,
        lambda m: (
            (NU6_APRIORI ** (m[1] - 1)) * math.prod(Bc[k] ** m[1 + k] for k in range(1, g + 1)),
            4 * (m[1] - 1) + sum(k * m[1 + k] for k in range(1, g + 1)),
        ),
        lambda m: m[1] == 1 and sum(m[2:]) == 0,
        q0,
    )

    # 4b: Write nu_6 = b_1 * m_5 + r_6 in F_4 = 0 to bound |r_6| <= C_r6 * q^(-1/2) * |m_5|:
    P4_r6 = F4_reduced(g, b, [x.subs(nu6, b[1] * m5 + r6) for x in bB_no_m4], [q, m5, r6, *b[1:]])
    R6_AP = NU6_APRIORI + Bc[1] * M5_APRIORI
    rem_r6 = sum_terms_bound(
        [
            (m, c)
            for m, c in P4_r6.terms()
            if m[2] >= 1 and not (m[0] == 8 and m[2] == 1 and m[1] == 0 and sum(m[3:]) == 0)
        ],
        lambda m: (
            (M5_APRIORI ** m[1])
            * (R6_AP ** (m[2] - 1))
            * math.prod(Bc[k] ** m[2 + k] for k in range(1, g + 1)),
            3 * m[1] + 4 * (m[2] - 1) + sum(k * m[2 + k] for k in range(1, g + 1)),
        ),
        16,
        q0,
    )
    rem_m5_p4 = sum_terms_bound(
        [(m, c) for m, c in P4_r6.terms() if m[2] == 0 and m[1] >= 1],
        lambda m: (
            (M5_APRIORI ** (m[1] - 1)) * math.prod(Bc[k] ** m[2 + k] for k in range(1, g + 1)),
            3 * (m[1] - 1) + sum(k * m[2 + k] for k in range(1, g + 1)),
        ),
        15,
        q0,
    )
    C_r6 = rem_m5_p4 / (Fraction(1) - rem_r6)
    C_nu6_per_m5 = Bc[1] + C_r6 / (s0**2)

    # 4c: Check m_4 = 0 => m_5 = 0 from F_5 = 0:
    P5_raw = F5_diff_poly(g, b, bB, [q, m4, m5, nu6, *b[1:]])
    P5, rem5_div = sp.div(P5_raw, sp.Poly(5, q, m4, m5, nu6, *b[1:], domain="ZZ"))
    assert rem5_div.is_zero
    P5_m40 = sp.Poly(
        {(m[0], m[2], m[3], *m[4:]): c for m, c in P5.terms() if m[1] == 0},
        q,
        m5,
        nu6,
        *b[1:],
        domain="ZZ",
    )

    def w_m40(m):
        bc = math.prod(Bc[k] ** m[2 + k] for k in range(1, g + 1))
        bs = sum(k * m[2 + k] for k in range(1, g + 1))
        if m[1] >= 1:
            return (
                (M5_APRIORI ** (m[1] - 1)) * ((C_nu6_per_m5 * M5_APRIORI) ** m[2]) * bc,
                3 * (m[1] - 1) + 4 * m[2] + bs,
            )
        return (
            C_nu6_per_m5 * ((C_nu6_per_m5 * M5_APRIORI) ** (m[2] - 1)) * bc,
            1 + 4 * (m[2] - 1) + bs,
        )

    r_m40 = check_dominance(P5_m40, w_m40, lambda m: m[1] == 1 and sum(m[2:]) == 0, q0)

    # 4d: For |m_4| >= 1, bound |m_5| <= C_m5_s * q^(1/2) * |m_4| from F_5 = 0, sharpening |m_4| <= 512:
    rem5_m5 = sum_terms_bound(
        [
            (m, c)
            for m, c in P5.terms()
            if (m[2] >= 1 or m[3] >= 1)
            and not (m[0] == 27 and m[2] == 1 and m[1] == 0 and m[3] == 0 and sum(m[4:]) == 0)
        ],
        lambda m: (
            (M4_APRIORI ** m[1])
            * (
                (M5_APRIORI ** (m[2] - 1)) * ((C_nu6_per_m5 * M5_APRIORI) ** m[3])
                if m[2] >= 1
                else C_nu6_per_m5 * ((C_nu6_per_m5 * M5_APRIORI) ** (m[3] - 1))
            )
            * math.prod(Bc[k] ** m[3 + k] for k in range(1, g + 1)),
            (3 * (m[2] - 1) + 4 * m[3] if m[2] >= 1 else 1 + 4 * (m[3] - 1))
            + sum(k * m[3 + k] for k in range(1, g + 1)),
        ),
        54,
        q0,
    )
    rem5_m4 = sum_terms_bound(
        [(m, c) for m, c in P5.terms() if m[2] == 0 and m[3] == 0 and m[1] >= 1],
        lambda m: (
            (M4_APRIORI ** (m[1] - 1)) * math.prod(Bc[k] ** m[3 + k] for k in range(1, g + 1)),
            sum(k * m[3 + k] for k in range(1, g + 1)),
        ),
        55,
        q0,
    )
    C_m5_s = rem5_m4 / (Fraction(1) - rem5_m5)
    m4_refined = (512 * (q0**2) + C_nu6_per_m5 * C_m5_s * q0 * M4_APRIORI) / ((q0 - 1) ** 2)
    M4_SHARP = Fraction(int(math.floor(m4_refined)))
    assert M4_SHARP == 512
    M5_NEW_S1 = C_m5_s * M4_SHARP
    R6_NEW_S0 = C_r6 * M5_NEW_S1

    # 4e: Bound |b_1| <= B1_INT from E_3 = 0 (-q^11 * b_1 * m_4 + ... = 0):
    P3_r6 = F3_reduced(g, b, [x.subs(nu6, b[1] * m5 + r6) for x in bB], [q, m4, m5, r6, *b[1:]])
    rem3_with_b1 = sum_terms_bound(
        [
            (m, c)
            for m, c in P3_r6.terms()
            if m[4] >= 1
            and not (
                m[0] == 11 and m[1] == 1 and m[2] == 0 and m[3] == 0 and m[4] == 1 and sum(m[5:]) == 0
            )
        ],
        lambda m: (
            (M4_SHARP ** max(0, m[1] - 1))
            * (C_m5_s * (M5_NEW_S1 ** (m[2] - 1)) if (m[1] == 0 and m[2] >= 1) else (M5_NEW_S1 ** m[2]))
            * (
                (R6_NEW_S0 ** m[3])
                if (m[1] >= 1 or m[2] >= 1)
                else (C_r6 * C_m5_s * (R6_NEW_S0 ** (m[3] - 1)))
            )
            * (Bc[1] ** (m[4] - 1))
            * math.prod(Bc[k] ** m[3 + k] for k in range(2, g + 1)),
            m[2] + (m[4] - 1) + sum(k * m[3 + k] for k in range(2, g + 1)),
        ),
        22,
        q0,
    )
    rem3_no_b1 = sum_terms_bound(
        [(m, c) for m, c in P3_r6.terms() if m[4] == 0],
        lambda m: (
            (M4_SHARP ** max(0, m[1] - 1))
            * (C_m5_s * (M5_NEW_S1 ** (m[2] - 1)) if (m[1] == 0 and m[2] >= 1) else (M5_NEW_S1 ** m[2]))
            * (
                (R6_NEW_S0 ** m[3])
                if (m[1] >= 1 or m[2] >= 1)
                else (C_r6 * C_m5_s * (R6_NEW_S0 ** (m[3] - 1)))
            )
            * math.prod(Bc[k] ** m[3 + k] for k in range(2, g + 1)),
            m[2] + sum(k * m[3 + k] for k in range(2, g + 1)),
        ),
        22,
        q0,
    )
    B1_INT = Fraction(int(math.floor(rem3_no_b1 / (Fraction(1) - rem3_with_b1))))

    # 4f: Refine |m_5| <= C_m5_per_m4 * |m_4| and |nu_6| <= C_nu6_per_m4 * |m_4|,
    # then bound |c_2| = |b_2 + (b_1 + 8)q| <= C2_INT from E_3 = 0 and eliminate m_5 = 0 from E_5 = 0:
    NU6_PER_M5 = B1_INT + C_r6 / s0
    rem5_m4_const = sum_terms_bound(
        [(m, c) for m, c in P5.terms() if m[2] == 0 and m[3] == 0 and m[1] >= 1],
        lambda m: (
            (M4_SHARP ** (m[1] - 1))
            * (B1_INT ** m[4])
            * math.prod(Bc[k] ** m[3 + k] for k in range(2, g + 1)),
            sum(k * m[3 + k] for k in range(2, g + 1)),
        ),
        54,
        q0,
    )
    C_m5_per_m4 = rem5_m4_const / (Fraction(1) - rem5_m5)
    M5_CONST = C_m5_per_m4 * M4_SHARP
    C_nu6_per_m4 = NU6_PER_M5 * C_m5_per_m4
    NU6_CONST = C_nu6_per_m4 * M4_SHARP

    subs_c12 = {b[1]: c1s, b[2]: (-c1s - 8) * q + c2s}
    P3_c2 = F3_reduced(
        g, [x.subs(subs_c12) for x in b], [x.subs(subs_c12) for x in bB], [q, m4, m5, nu6, c1s, c2s, *b[3:]]
    )
    C2_AP = Bc[2] + B1_INT + 8
    rem3_with_c2 = sum_terms_bound(
        [
            (m, c)
            for m, c in P3_c2.terms()
            if m[5] >= 1
            and not (
                m[0] == 10
                and m[1] == 1
                and m[2] == 0
                and m[3] == 0
                and m[4] == 0
                and m[5] == 1
                and sum(m[6:]) == 0
            )
        ],
        lambda m: (
            (
                (M4_SHARP ** (m[1] - 1)) * (M5_CONST ** m[2]) * (NU6_CONST ** m[3])
                if m[1] >= 1
                else (
                    C_m5_per_m4 * (M5_CONST ** (m[2] - 1)) * (NU6_CONST ** m[3])
                    if m[2] >= 1
                    else C_nu6_per_m4 * (NU6_CONST ** (m[3] - 1))
                )
            )
            * (B1_INT ** m[4])
            * (C2_AP ** (m[5] - 1))
            * math.prod(Bc[k] ** m[3 + k] for k in range(3, g + 1)),
            2 * (m[5] - 1) + sum(k * m[3 + k] for k in range(3, g + 1)),
        ),
        20,
        q0,
    )
    rem3_no_c2 = sum_terms_bound(
        [(m, c) for m, c in P3_c2.terms() if m[5] == 0],
        lambda m: (
            (
                (M4_SHARP ** (m[1] - 1)) * (M5_CONST ** m[2]) * (NU6_CONST ** m[3])
                if m[1] >= 1
                else (
                    C_m5_per_m4 * (M5_CONST ** (m[2] - 1)) * (NU6_CONST ** m[3])
                    if m[2] >= 1
                    else C_nu6_per_m4 * (NU6_CONST ** (m[3] - 1))
                )
            )
            * (B1_INT ** m[4])
            * math.prod(Bc[k] ** m[3 + k] for k in range(3, g + 1)),
            sum(k * m[3 + k] for k in range(3, g + 1)),
        ),
        20,
        q0,
    )
    C2_INT = Fraction(int(math.floor(rem3_no_c2 / (Fraction(1) - rem3_with_c2))))

    P5_c2_raw = F5_diff_poly(
        g, [x.subs(subs_c12) for x in b], [x.subs(subs_c12) for x in bB], [q, m4, m5, nu6, c1s, c2s, *b[3:]]
    )
    P5_c2, rem5c_div = sp.div(P5_c2_raw, sp.Poly(5, q, m4, m5, nu6, c1s, c2s, *b[3:], domain="ZZ"))
    assert rem5c_div.is_zero
    r_m5 = check_dominance(
        P5_c2,
        lambda m: (
            (M4_SHARP ** m[1])
            * (M5_CONST ** max(0, m[2] - 1))
            * (NU6_CONST ** m[3])
            * (B1_INT ** m[4])
            * (C2_INT ** m[5])
            * math.prod(Bc[k] ** m[3 + k] for k in range(3, g + 1)),
            sum(k * m[3 + k] for k in range(3, g + 1)),
        ),
        lambda m: m[2] == 1 and m[1] == 0 and sum(m[3:]) == 0,
        q0,
    )
    # Check |m_4| <= 520 for all q >= 12 once m_5 = nu_6 = 0:
    assert 512 * (12**4) <= 520 * ((12**2 - 1) ** 2)
    print(
        f"  Archimedean elimination on (E_3, E_4, E_5) checked for q >= 10^8 "
        f"(ratios: d_2 {r_d2:.1f}, d_3 {r_d3:.1f}, m_4=0 {r_m40:.1f}, m_5 {r_m5:.2f})."
    )


def main():
    print("Section 3: g = 8, N = 5 elimination and Cauchy-Schwarz bounds (Proposition 3.2(1))")
    check_g8_elimination(10**8)

    T, s, m4 = sp.symbols("T s m4", positive=True)
    a = [sp.Integer(1)] + [sp.Symbol(f"a{k}") for k in range(1, 9)]

    PA = (
        T**16
        + q**8
        + sum(a[k] * (T ** (16 - k) + (q ** (8 - k)) * (T**k)) for k in range(1, 8))
        + a[8] * (T**8)
    )
    dP = sp.expand(m4 * (T**4) * (T**4 - 1) * (T**4 - q**4))
    PB = sp.expand(PA + dP)

    # 1. Check vanishing at d = 1, 2, 4 and polynomial perturbation identity:
    db = [sp.Integer(0), 0, 0, 0, m4, 0, v**2 * m4 - u**2 * m4, 0, -u**2 * (v**2 * m4)]
    assert sp.expand(sum(((-1) ** k) * db[k] * (T**k) * ((T**2 + q) ** (8 - k)) for k in range(9)) - dP) == 0
    for d in [1, 2, 4]:
        Phi = sp.cyclotomic_poly(d, T)
        diff = sp.expand(sp.resultant(Phi, PB, T) - sp.resultant(Phi, PA, T))
        assert diff == 0, f"Expected F_{d}(B) - F_{d}(A) == 0, got {diff}"
    print("  F_1(B) = F_1(A), F_2(B) = F_2(A), F_4(B) = F_4(A) checked for m_4 * T^4 (T^4 - 1)(T^4 - q^4).")

    # 2. Extract (F_3(B) - F_3(A)) / (3 m_4) from sp.resultant (including the +q^8 constant term):
    dF3_exact = sp.expand(
        (sp.resultant(sp.cyclotomic_poly(3, T), PB, T) - sp.resultant(sp.cyclotomic_poly(3, T), PA, T))
        / (3 * m4)
    )
    expected_dF3 = sp.expand(
        a[1] * (q**11 + 1)
        - a[2] * (q**10 + q**6 + q**4 + 1)
        + a[3] * (q**5 + q**4)
        + a[4] * (q**8 + 1)
        - a[5] * (q**7 + q**4 + q**3 + 1)
        + a[6] * (q**4 + q**2)
        + a[7] * (q**5 + 1)
        - a[8] * (q**4 + 1)
        + q**8
        + q**4
        + m4 * (q**8 + q**4 + 1)
    )
    assert sp.expand(dF3_exact - expected_dF3) == 0

    # 3. Substitute asymptotic parameterization (using |a_1| <= 120 and |a_2 - a_1*q| <= 31001
    #    established for q >= 10^8 in check_g8_elimination above):
    c1, r2, t3, tr4, t5, t6, t7, t8 = sp.symbols("c1 r2 t3 tr4 t5 t6 t7 t8", real=True)
    a_sub = [
        sp.Integer(1),
        c1,
        c1 * s**2 + r2,
        t3 * s**3,
        r2 * s**4 + tr4 * s**3,
        t5 * s**5,
        t6 * s**6,
        t7 * s**7,
        t8 * s**8,
    ]
    ps3 = sp.Poly(sp.expand(dF3_exact.subs(q, s**2).subs(dict(zip(a[1:], a_sub[1:])))), s)
    assert ps3.degree() == 19
    assert sp.expand(ps3.nth(19) - (tr4 - t5)) == 0

    # Compute top s-powers of (F_5(B) - F_5(A)) / (5 m_4) via cyclotomic tower norm:
    th, z5 = sp.symbols("th z5")

    def mod_q5(e):
        r1 = sp.rem(sp.expand(e), z5**2 - th * z5 + 1, z5)
        p1 = sp.Poly(r1, z5)
        return sp.rem(sp.expand(p1.nth(0)), th**2 + th - 1, th) + z5 * sp.rem(
            sp.expand(p1.nth(1)), th**2 + th - 1, th
        )

    zp, zm = {0: sp.Integer(1)}, {0: sp.Integer(1)}
    for m in range(1, 9):
        zp[m] = mod_q5(zp[m - 1] * z5)
        zm[m] = mod_q5(zm[m - 1] * (th - z5))

    def N_th_from_a(arr, q_expr):
        val = mod_q5(
            arr[8]
            + (zp[8] + q_expr**8 * zm[8])
            + sum(arr[k] * (zp[8 - k] + q_expr ** (8 - k) * zm[8 - k]) for k in range(1, 8))
        )
        pv = sp.Poly(val, z5)
        X0, Y0 = pv.nth(0), pv.nth(1)
        return sp.expand(sp.rem(sp.expand(X0**2 + X0 * Y0 * th + Y0**2), th**2 + th - 1, th))

    aB_sub = list(a_sub)
    aB_sub[4] += m4
    aB_sub[8] -= m4 * (s**8 + 1)
    NA = sp.Poly(N_th_from_a(a_sub, s**2), th)
    NB = sp.Poly(N_th_from_a(aB_sub, s**2), th)
    A0, A1 = NA.nth(0), NA.nth(1)
    d0, d1_th = sp.expand(NB.nth(0) - A0), sp.expand(NB.nth(1) - A1)
    dF5_div = sp.expand(
        ((2 * A0 - A1) * d0 + (-A0 - 2 * A1) * d1_th + d0**2 - d0 * d1_th - d1_th**2) / (5 * m4)
    )
    ps5 = sp.Poly(dF5_div, s)
    assert ps5.degree() == 52
    assert sp.expand(ps5.nth(52) - (r2 - c1**2)) == 0
    assert ps5.nth(51) == 0
    assert sp.expand(ps5.nth(50) - (c1**3 + t3**2 - t6)) == 0
    print("  Leading s-powers of E_3 and E_5 checked (r_2 = a_1^2 and t_6 = a_1^3 + t_3^2 + o(1)).")

    # 4. Derive limiting elementary symmetric polynomials tb[k] of x_1, ..., x_8 in [-2, 2]
    #    symbolically from P_A(T) = sum_{k=0}^8 (-1)^k b_k T^k (T^2 + q)^(8 - k):
    b_syms = [sp.Integer(1)] + [sp.Symbol(f"b{k}") for k in range(1, 9)]
    P_from_b = sp.Poly(
        sp.expand(sum(((-1) ** k) * b_syms[k] * (T**k) * ((T**2 + q) ** (8 - k)) for k in range(9))),
        T,
    )
    b_subs = {}
    for k in range(1, 7):
        eq_k = sp.expand((P_from_b.nth(16 - k) - a[k]).subs(b_subs))
        b_subs[b_syms[k]] = sp.solve(eq_k, b_syms[k])[0]

    sub_lim = {
        q: s**2,
        a[1]: c1,
        a[2]: c1 * s**2 + c1**2,
        a[3]: t3 * s**3,
        a[4]: c1**2 * s**4 + tr4 * s**3,
        a[5]: t5 * s**5,
        a[6]: (c1**3 + t3**2) * s**6,
    }
    tb = [sp.Integer(1)] + [
        sp.expand(sp.limit(b_subs[b_syms[k]].subs(sub_lim) / (s**k), s, sp.oo)) for k in range(1, 7)
    ]

    p_sums = [sp.Integer(8)]
    for k in range(1, 7):
        pk = ((-1) ** (k - 1)) * (
            k * tb[k] - sum(((-1) ** (i - 1)) * tb[k - i] * p_sums[i] for i in range(1, k))
        )
        p_sums.append(sp.expand(pk))

    cs_1 = sp.expand(8 * p_sums[4] - p_sums[2] ** 2)
    assert sp.expand(cs_1 - (128 - 20 * c1**2)) == 0
    for bad_c1 in [-3, 3, -4, 4]:
        assert cs_1.subs(c1, bad_c1) < 0

    cs_at_2 = sp.expand((p_sums[2] * p_sums[6] - p_sums[4] ** 2).subs(c1, 2))
    assert sp.expand(cs_at_2 - (-144 - 36 * t3**2)) == 0
    print(
        "  Cauchy-Schwarz expressions 8*p_4 - p_2^2 = 128 - 20*a_1^2 and "
        "(p_2*p_6 - p_4^2)|_{a_1=2} = -144 - 36*t_3^2 checked."
    )


if __name__ == "__main__":
    main()
