#!/usr/bin/env python3
"""
Computational checks for the explicit ordinary Z[q]-families in Theorems 2.3(1) and 3.1:
  - Theorem 2.3(1): g = 7 ordinary Z[q]-family for prime powers q >= 5 (c_1..c_4 equal, c_5(A) != c_5(B)).
  - Theorem 3.1 (Remark 7.10): g = 8 ordinary Z[q]-family for prime powers q >= 4 realizing
    delta_5 = -(q + 1), delta_7 = q^3 + 1 (c_1..c_4 equal, c_5(A) != c_5(B)).
"""

import math
import sympy as sp


def build_weil_poly(g, h_expr, X, T, q):
    p = sp.Poly(h_expr, X)
    return sp.expand(sum(p.nth(g - k) * (T**k) * ((T**2 + q) ** (g - k)) for k in range(g + 1)))


def verify_g7_lower():
    q, X, T, us, xs = sp.symbols("q X T us xs", real=True)
    hA = (
        X**7
        - (7 * q + 1) * X**5
        + X**4
        + (14 * q**2 + 6 * q) * X**3
        + (q**2 - 3 * q + 2) * X**2
        - (7 * q**3 + 7 * q**2 - 1) * X
        - (3 * q**3 - 3 * q**2 + 5 * q - 1)
    )
    hB = hA - 2 * q * (X**2 - (q + 1) ** 2)

    PA = build_weil_poly(7, hA, X, T, q)
    PB = build_weil_poly(7, hB, X, T, q)

    # 1. Ordinariness in every characteristic p >= 2: a_7 == 1 (mod q)
    assert sp.rem(sp.Poly(PA, T).nth(7), q, q) == 1
    assert sp.rem(sp.Poly(PB, T).nth(7), q, q) == 1

    # 2. Cyclotomic resultant equality for d = 1..4, and non-vanishing for d = 5 (q >= 5)
    for d in [1, 2, 3, 4]:
        diff_d = sp.expand(
            sp.resultant(sp.cyclotomic_poly(d, T), PB, T)
            - sp.resultant(sp.cyclotomic_poly(d, T), PA, T)
        )
        assert diff_d == 0, f"g=7 failed at d={d}"
    diff5 = sp.expand(
        sp.resultant(sp.cyclotomic_poly(5, T), PB, T)
        - sp.resultant(sp.cyclotomic_poly(5, T), PA, T)
    )
    q_fac, rem5 = sp.div(diff5, -10 * q, q)
    assert rem5 == 0 and q_fac != 0
    assert sp.count_roots(sp.Poly(q_fac, q, domain="ZZ"), 5, sp.oo) == 0

    # 3. Sturm root counts at rational nodes for q >= 5 (us = q^(-1/2) in (0, 9/20], (20/9)^2 = 400/81 < 5)
    nodes = [
        sp.Rational(-2),
        sp.Rational(-9, 5),
        sp.Rational(-6, 5),
        sp.Rational(-2, 5),
        sp.Rational(2, 5),
        sp.Rational(6, 5),
        sp.Rational(9, 5),
        sp.Rational(2),
    ]
    for H in [
        sp.expand(hA.subs({X: xs / us, q: 1 / us**2}) * us**7),
        sp.expand(hB.subs({X: xs / us, q: 1 / us**2}) * us**7),
    ]:
        signs = [int(sp.sign(H.subs({us: 0, xs: nd}))) for nd in nodes]
        assert signs == [-1, 1, -1, 1, -1, 1, -1, 1]
        for nd in nodes:
            assert sp.count_roots(sp.Poly(H.subs(xs, nd), us), 0, sp.Rational(9, 20)) == 0
    # Sharpness of q >= 5: at q = 4, hB has only 5 real roots in (-4, 4):
    assert sp.count_roots(sp.Poly(hB.subs(q, 4), X, domain="ZZ"), -4, 4) == 5
    print(
        "  g = 7 (Theorem 2.3(1)): F_1..F_4 equal, F_5 != 0, and 7 real roots in (-2*sqrt(q), 2*sqrt(q)) for q >= 5 (sharp)."
    )


def verify_g8_lower():
    q, X, T, us, xs = sp.symbols("q X T us xs", real=True)
    hA = (
        X**8
        - 7 * q * X**6
        - X**5
        + (15 * q**2 - q) * X**4
        + (-q**2 + 6 * q) * X**3
        + (-11 * q**3 + 17 * q**2 - 37 * q - 2) * X**2
        + (3 * q**3 - 8 * q**2 + q) * X
        + (2 * q**4 - 15 * q**3 + 40 * q**2 + 1)
    )
    hB = hA - (q + 1) * X * (X**2 - (q + 1) ** 2)

    PA = build_weil_poly(8, hA, X, T, q)
    PB = build_weil_poly(8, hB, X, T, q)

    # 1. Check perturbation coefficients against Remark 7.10 of Chidambaram-Keller:
    #    PB(T) - PA(T) has delta_5 = -(q + 1), delta_7 = q^3 + 1, delta_k = 0 (k in {1..8} \ {5, 7}).
    dP = sp.Poly(sp.expand(PB - PA), T)
    expected_delta = {1: 0, 2: 0, 3: 0, 4: 0, 5: -(q + 1), 6: 0, 7: q**3 + 1, 8: 0}
    for k, exp_v in expected_delta.items():
        assert sp.expand(dP.nth(16 - k) - exp_v) == 0, f"Mismatch at delta_{k}"

    # 2. Ordinariness in every characteristic p >= 2: a_8 == 1 (mod q)
    assert sp.rem(sp.Poly(PA, T).nth(8), q, q) == 1
    assert sp.rem(sp.Poly(PB, T).nth(8), q, q) == 1

    # 3. Cyclotomic resultant equality for d = 1..4, and non-vanishing for d = 5 (q >= 4)
    for d in [1, 2, 3, 4]:
        diff_d = sp.expand(
            sp.resultant(sp.cyclotomic_poly(d, T), PB, T)
            - sp.resultant(sp.cyclotomic_poly(d, T), PA, T)
        )
        assert diff_d == 0, f"g=8 failed at d={d}"
    diff5 = sp.expand(
        sp.resultant(sp.cyclotomic_poly(5, T), PB, T)
        - sp.resultant(sp.cyclotomic_poly(5, T), PA, T)
    )
    q_fac, rem5 = sp.div(diff5, -5 * q * (q + 1), q)
    assert rem5 == 0 and q_fac != 0
    assert sp.count_roots(sp.Poly(q_fac, q, domain="ZZ"), 4, sp.oo) == 0

    # 4. Sturm root counts at rational nodes for hA on q >= 4 (us in (0, 1/2]) and hB on q >= 9 (us in (0, 1/3]),
    #    plus direct Sturm root counts for hB at the remaining prime powers q in {4, 5, 7, 8}:
    nodes = [
        sp.Rational(-2),
        sp.Rational(-33, 20),
        sp.Rational(-27, 20),
        sp.Rational(-4, 5),
        sp.Rational(0),
        sp.Rational(4, 5),
        sp.Rational(27, 20),
        sp.Rational(33, 20),
        sp.Rational(2),
    ]
    HA = sp.expand(hA.subs({X: xs / us, q: 1 / us**2}) * us**8)
    HB = sp.expand(hB.subs({X: xs / us, q: 1 / us**2}) * us**8)
    assert [int(sp.sign(HA.subs({us: 0, xs: nd}))) for nd in nodes] == [1, -1, 1, -1, 1, -1, 1, -1, 1]
    assert [int(sp.sign(HB.subs({us: 0, xs: nd}))) for nd in nodes] == [1, -1, 1, -1, 1, -1, 1, -1, 1]
    for nd in nodes:
        assert sp.count_roots(sp.Poly(HA.subs(xs, nd), us), 0, sp.Rational(1, 2)) == 0
        assert sp.count_roots(sp.Poly(HB.subs(xs, nd), us), 0, sp.Rational(1, 3)) == 0
    for qt in [4, 5, 7, 8]:
        rq = sp.Rational(int(math.isqrt(4 * qt * 10**8 - 1)), 10**4)
        poly_B = sp.Poly(hB.subs(q, qt), X, domain="ZZ")
        assert sp.count_roots(poly_B, -rq, rq) == 8
        assert sp.gcd(poly_B, poly_B.diff()).degree() == 0
    # Sharpness of q >= 4: at q = 3, hB has only 4 real roots in (-2*sqrt(3), 2*sqrt(3)):
    rq3 = sp.Rational(int(math.isqrt(12 * 10**8 - 1)), 10**4)
    assert sp.count_roots(sp.Poly(hB.subs(q, 3), X, domain="ZZ"), -rq3, rq3) == 4
    print(
        "  g = 8 (Theorem 3.1): F_1..F_4 equal, F_5 != 0, and 8 real roots in (-2*sqrt(q), 2*sqrt(q)) for q >= 4 (sharp)."
    )


def main():
    print("Sections 2 & 3: explicit ordinary Z[q]-families (g = 7, 8)")
    verify_g7_lower()
    verify_g8_lower()


if __name__ == "__main__":
    main()
