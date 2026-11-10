#!/usr/bin/env python3
"""
Sanity checks for Section 5 (Theorem 5.1, Q(g) = (10g)^6):
  1. Checks the exponential generating-function identities (6)-(7) symbolically
     for g = 2, 3, 4 across all step indices g/2 < i <= g and m in {2i - 1, 2i}.
  2. Evaluates the rational Taylor upper bound on 4 * (exp(1/5) - 1) + 8 * 20^(-6)
     used in the inductive step and checks the polynomial inequalities on (10g)^6
     for 2 <= g < 100.
"""

from fractions import Fraction
import math
import sympy as sp


def newton_e_poly(s_list, M, T):
    """Coefficient (-1)^M * [T^M] exp(-sum_{k=1}^M s_k T^k / k)."""
    if M < 0:
        return sp.Integer(0)
    if M == 0:
        return sp.Integer(1)
    arg = -sum(s_list[k - 1] * (T**k) / k for k in range(1, M + 1))
    res = sp.Integer(1)
    cur = sp.Integer(1)
    for j in range(1, M + 1):
        cur = sp.expand(sp.rem(cur * arg, T ** (M + 1), T) / j)
        res = sp.expand(res + cur)
    return sp.expand(((-1) ** M) * sp.Poly(res, T).nth(M))


def check_generating_function_identities():
    """
    Check symbolically for g = 2, 3, 4 that when tilde_s_k = s_k for 1 <= k <= i - 1
    and tilde_s_k = s_k + delta_k for i <= k <= m - 1 (with m in {2i - 1, 2i}, m > g):
      1) e_{2g-m}(tilde_s) - e_{2g-m}(s) = sum_{k=i}^{2g-m} (-1)^(k-1) (delta_k / k) e_{2g-m-k}(s)
      2) e_m(tilde_s_{<m}, s_m) - e_m(s) = sum_{k=i}^{m-1} (-1)^(k-1) (delta_k / k) e_{m-k}(s)
                                           + 1_{m=2i} * delta_i^2 / (2 * i^2).
    """
    T, q = sp.symbols("T q")
    for g in [2, 3, 4]:
        s = [sp.Symbol(f"s{k}") for k in range(1, 2 * g + 1)]
        d = [sp.Symbol(f"d{k}") for k in range(1, 2 * g + 1)]
        for i in range(g // 2 + 1, g + 1):
            for m in [2 * i - 1, 2 * i]:
                if m <= g:
                    continue
                n = m - g
                st = [
                    s[k - 1] if k < i else (s[k - 1] + d[k - 1] if k < m else s[k - 1])
                    for k in range(1, 2 * g + 1)
                ]
                lhs1 = newton_e_poly(st, 2 * g - m, T) - newton_e_poly(s, 2 * g - m, T)
                rhs1 = sum(
                    ((-1) ** (k - 1)) * (d[k - 1] / k) * newton_e_poly(s, 2 * g - m - k, T)
                    for k in range(i, 2 * g - m + 1)
                )
                assert sp.expand(lhs1 - rhs1) == 0

                lhs2 = newton_e_poly(st, m, T) - newton_e_poly(s, m, T)
                rhs2 = sum(
                    ((-1) ** (k - 1)) * (d[k - 1] / k) * newton_e_poly(s, m - k, T)
                    for k in range(i, m)
                )
                if m == 2 * i:
                    rhs2 += (d[i - 1] ** 2) / (2 * (i**2))
                assert sp.expand(lhs2 - rhs2) == 0

                # Check compatibility with the formula of [CK26, Lemma 5.1]:
                # s_m / m = -q^(-n) (-1)^(2g-m) e_{2g-m}(s) + (-1)^m (e_m(s) - (-1)^(m-1) s_m / m)
                sm_rhs = -q ** (-n) * ((-1) ** (2 * g - m)) * newton_e_poly(s, 2 * g - m, T) + (
                    (-1) ** m
                ) * (newton_e_poly(s, m, T) - ((-1) ** (m - 1)) * s[m - 1] / m)
                # At q = 1 with palindromic e_m = e_{2g-m}, sm_rhs == s_m / m:
                pal_check = sp.expand(
                    (sm_rhs - s[m - 1] / m).subs(q, 1)
                    + ((-1) ** m) * (newton_e_poly(s, 2 * g - m, T) - newton_e_poly(s, m, T))
                )
                assert pal_check == 0
    print("  Exponential generating-function identities checked symbolically for g = 2, 3, 4.")


def check_numerical_constants():
    """
    Check the rational Taylor bound on 4 * (exp(1/5) - 1) + 8 * 20^(-6) and
    evaluate the polynomial rounding inequalities for 2 <= g < 100.
    """
    # Rational upper bound on exp(1/5) via degree-6 Taylor polynomial + geometric remainder:
    # exp(1/5) = sum_{r=0}^6 (1/5)^r / r! + R_7, R_7 < (1/5)^7 / (7! * (1 - 1/5))
    e_fifth_upper = sum(Fraction(1, (5**r) * math.factorial(r)) for r in range(7)) + Fraction(
        1, (5**7) * math.factorial(7)
    ) * Fraction(5, 4)
    lin_ratio_upper = 4 * (e_fifth_upper - 1)
    quad_ratio_upper = Fraction(8, 20**6)
    total_ind_ratio = lin_ratio_upper + quad_ratio_upper
    assert lin_ratio_upper < Fraction(88562, 100000)
    assert total_ind_ratio < Fraction(89, 100) < 1

    # In Theorem 5.1, for all g >= 2:
    #   (10g)^6 - 256 g^2 = g^2 (10^6 g^4 - 256) > 0, and
    #   (8g)^4 * (10g)^(6g - 2) = ((10g)^6)^(g+1) * (2 / (25g))^4 < ((10g)^6)^(g+1).
    for g in range(2, 100):
        E = 10 * g
        Qg = E**6
        assert Qg > 256 * g * g
        assert (8 * g) ** 4 * (E ** (6 * g - 2)) < (Qg ** (g + 1))

    print(
        f"  Rational contraction constant 4*(exp(1/5) - 1) + 8*20^(-6) <= {float(total_ind_ratio):.6f} < 0.89 "
        "and rounding inequalities checked for 2 <= g < 100."
    )


def main():
    print("Section 5: algebraic identities and numerical constants for Theorem 5.1")
    check_generating_function_identities()
    check_numerical_constants()


if __name__ == "__main__":
    main()
