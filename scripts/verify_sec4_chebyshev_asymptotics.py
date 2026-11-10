#!/usr/bin/env python3
"""
Computational checks for Section 4 (Theorems 4.1 and 4.2):
  - Theorem 4.1: Checks the Chebyshev-totient construction g = 2 * sum_{d=1}^N phi(d)
    for N = 2, 3, 4, 5 (g = 4, 8, 12, 20):
      * Res_T(Phi_d, P_B) = Res_T(Phi_d, P_A) for 1 <= d <= N;
      * a_g(A) == +1 (mod q) and a_g(B) == -1 (mod q);
      * q^(-g/2) h_A(sqrt(q) x) -> 2*T_g(x/2) + 1 and
        q^(-g/2) h_B(sqrt(q) x) -> 2*T_g(x/2) - 1 as q -> oo.
  - Theorem 4.2: Checks the explicit polynomial families in `data/higher_genus_families.json`
    for (g, N + 1) in {(15, 7), (24, 8), (32, 9)} using `sympy`:
      * Integer coefficients in Z[q][X] with q-degree <= floor(k/2);
      * a_g(A), a_g(B) == +-1 (mod q);
      * F_d(A) = F_d(B) for 1 <= d <= N and F_{N+1}(B) != F_{N+1}(A) for q >= q_0;
      * Sturm root counts at rational nodes showing all g roots of h_A and h_B lie in
        (-2*sqrt(q), 2*sqrt(q)) for every prime power q >= q_0.
"""

import json
import math
from pathlib import Path
import sympy as sp

ROOT_DIR = Path(__file__).resolve().parent.parent
DATA_PATH = ROOT_DIR / "data" / "higher_genus_families.json"


def chebyshev_2Tg_half(g, X, q):
    """Returns 2 * q^(g/2) * T_g(X / (2*sqrt(q))) in Z[q, X] (for g >= 1)."""
    prev2 = sp.Integer(2)
    prev1 = X
    for _ in range(2, g + 1):
        curr = sp.expand(X * prev1 - q * prev2)
        prev2, prev1 = prev1, curr
    return prev1


def psi_cyclotomic(d, X, q):
    """
    Monic polynomial Psi_d(X, q) in Z[q][X] of degree phi(d):
      Psi_1 = X - (q + 1), Psi_2 = X + (q + 1),
      Psi_d = Res_z(Phi_d(z), z^2 - X*z + q) for d >= 3.
    Under SymPy's resultant sign convention, sp.resultant(Phi_d(T), P_h(T), T) equals
    ((-1)^g if d == 1 else 1) * sp.resultant(Psi_d(X, q), h(X), X).
    """
    if d == 1:
        return X - (q + 1)
    if d == 2:
        return X + (q + 1)
    z = sp.Symbol("z")
    return sp.Poly(sp.resultant(sp.cyclotomic_poly(d, z), z**2 - X * z + q, z), X).as_expr()


def cross_check_trace_resultant():
    X, T, q = sp.symbols("X T q")
    h_test = X**5 - 2 * X**4 + (q + 1) * X**3 - 3 * q * X + (2 * q - 1)
    ph = sp.Poly(h_test, X)
    P_test = sp.expand(sum(ph.nth(5 - k) * (T**k) * ((T**2 + q) ** (5 - k)) for k in range(6)))
    for d in range(1, 10):
        rt = sp.expand(sp.resultant(sp.cyclotomic_poly(d, T), P_test, T))
        rx = sp.expand(sp.resultant(psi_cyclotomic(d, X, q), h_test, X))
        sgn = (-1) ** 5 if d == 1 else 1
        assert sp.expand(rt - sgn * rx) == 0, f"Trace-resultant mismatch at d={d}"


def verify_thm_4_1():
    X, q, x, s = sp.symbols("X q x s", positive=True)
    for N in [2, 3, 4, 5]:
        D_N = sum(int(sp.totient(d)) for d in range(1, N + 1))
        g = 2 * D_N
        Lambda_N = sp.Integer(1)
        for d in range(1, N + 1):
            Lambda_N = sp.expand(Lambda_N * psi_cyclotomic(d, X, q))
        assert sp.Poly(Lambda_N, X).degree() == D_N

        # Base polynomial h_A(X) = 2*q^(g/2)*T_g(X/(2*sqrt(q))) + q^(g/2) + 1, h_B = h_A + 2*Lambda_N:
        hA = sp.expand(chebyshev_2Tg_half(g, X, q) + q ** (g // 2) + 1)
        hB = sp.expand(hA + 2 * Lambda_N)

        for H in (hA, hB):
            pX = sp.Poly(H, X)
            assert pX.degree() == g and pX.nth(g) == 1
            for k in range(1, g + 1):
                ck = pX.nth(g - k)
                if ck != 0:
                    pq = sp.Poly(ck, q, domain="ZZ")
                    assert pq.degree() <= k // 2

        assert sp.rem(hA.subs(X, 0), q, q) == 1
        assert sp.rem(hB.subs(X, 0), q, q) == -1

        p_hA = sp.Poly(hA, X, domain=sp.ZZ[q])
        p_hB = sp.Poly(hB, X, domain=sp.ZZ[q])
        for d in range(1, N + 1):
            p_psi = sp.Poly(psi_cyclotomic(d, X, q), X, domain=sp.ZZ[q])
            diff_d = sp.expand(sp.resultant(p_psi, p_hB).as_expr() - sp.resultant(p_psi, p_hA).as_expr())
            assert diff_d == 0, f"Thm 4.1 failed at N={N}, d={d}"

        lim_A = sp.Poly(sp.expand(hA.subs({X: x * s, q: s**2})), s).nth(g)
        lim_B = sp.Poly(sp.expand(hB.subs({X: x * s, q: s**2})), s).nth(g)
        target_2Tg = chebyshev_2Tg_half(g, x, 1)
        assert sp.expand(lim_A - (target_2Tg + 1)) == 0
        assert sp.expand(lim_B - (target_2Tg - 1)) == 0
    print(
        "  Theorem 4.1 construction checked for N = 2, 3, 4, 5 (g = 4, 8, 12, 20): "
        "F_1..F_N equal, a_g == +-1 (mod q), and scaled limits 2*T_g(x/2) +- 1."
    )


def is_prime_power(n):
    if n < 2:
        return False
    fac = sp.factorint(n)
    return len(fac) == 1


def check_roots_at_rational_nodes(g, h_expr, X, q, node_den, node_nums, q0, u_inv_bound):
    assert len(node_nums) == g + 1
    for i in range(g):
        assert node_nums[i] < node_nums[i + 1]
    assert node_nums[0] >= -2 * node_den and node_nums[-1] <= 2 * node_den

    K = int(u_inv_bound)
    assert (K - 1) ** 2 < q0 <= K**2

    terms = sp.Poly(h_expr, X, q, domain="ZZ").terms()
    u_sym = sp.Symbol("u", real=True)
    signs0 = []
    for num_nd in node_nums:
        pu = {}
        for (deg_x, deg_q), c in terms:
            pw = g - deg_x - 2 * deg_q
            assert pw >= 0
            pu[pw] = pu.get(pw, 0) + int(c) * (num_nd**deg_x) * (node_den ** (g - deg_x))
        c0 = pu.get(0, 0)
        assert c0 != 0
        signs0.append(1 if c0 > 0 else -1)
        max_m = max(pu.keys())
        err_bound = sum(abs(cm) * (K ** (max_m - m)) for m, cm in pu.items() if m >= 1)
        if err_bound >= abs(c0) * (K**max_m):
            poly_u = sp.Poly(sum(cm * (u_sym**m) for m, cm in pu.items()), u_sym, domain="ZZ")
            assert sp.count_roots(poly_u, 0, sp.Rational(1, K)) == 0

    for i in range(g):
        assert signs0[i] * signs0[i + 1] == -1

    # Check prime powers in the remaining finite interval [q0, K^2) via Sturm root counting:
    for qt in range(q0, K**2):
        if is_prime_power(qt):
            # Rational inner bound rq < 2*sqrt(qt):
            rq = sp.Rational(int(math.isqrt(4 * qt * 10**12 - 1)), 10**6)
            hq = sp.Poly(h_expr.subs(q, qt), X, domain="ZZ")
            assert sp.count_roots(hq, -rq, rq) == g
            assert sp.gcd(hq, hq.diff()).degree() == 0


def verify_thm_4_2():
    data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    X, q = sp.symbols("X q")
    expected_cases = [("15", 15, 6), ("24", 24, 7), ("32", 32, 8)]
    for key, g, N_match in expected_cases:
        entry = data[key]
        assert entry["g"] == g and entry["N"] == N_match
        q0 = int(entry["q0"])
        u_inv = int(entry.get("sturm_u_inv_bound") or entry["triangle_u_inv_bound"])
        var_map = [tuple(p) for p in entry["var_map"]]
        bA_coeffs = entry["bA_coeffs"]
        assert len(var_map) == len(bA_coeffs)
        assert all(isinstance(v, int) for v in bA_coeffs)

        c_dict = {}
        for (k, j), val in zip(var_map, bA_coeffs):
            assert 1 <= k <= g and 0 <= j <= k // 2
            c_dict[(k, j)] = int(val)

        hA = sp.expand(
            X**g
            + sum(
                ((-1) ** k) * sum(c_dict.get((k, j), 0) * (q**j) for j in range(k // 2 + 1)) * (X ** (g - k))
                for k in range(1, g + 1)
            )
        )
        dh = sp.Integer(int(entry["L"])) * (q ** int(entry["q_power_in_dh"]))
        for d in entry["d_list"]:
            dh = sp.expand(dh * psi_cyclotomic(int(d), X, q))
        hB = sp.expand(hA + dh)

        # 1. Ordinariness in every characteristic p >= 2: a_g == +-1 (mod q)
        remA = int(sp.rem(hA.subs(X, 0), q, q))
        remB = int(sp.rem(hB.subs(X, 0), q, q))
        assert abs(remA) == 1 and abs(remB) == 1

        # 2. Cyclotomic norm equality for 1 <= d <= N_match, and separation at d = N_match + 1:
        p_hA = sp.Poly(hA, X, domain=sp.ZZ[q])
        p_hB = sp.Poly(hB, X, domain=sp.ZZ[q])
        for d in range(1, N_match + 1):
            p_psi = sp.Poly(psi_cyclotomic(d, X, q), X, domain=sp.ZZ[q])
            rA = sp.resultant(p_psi, p_hA)
            rB = sp.resultant(p_psi, p_hB)
            assert sp.expand(rB.as_expr() - rA.as_expr()) == 0, f"g={g} failed at d={d}"

        p_psi_next = sp.Poly(psi_cyclotomic(N_match + 1, X, q), X, domain=sp.ZZ[q])
        diff_next = sp.expand(
            sp.resultant(p_psi_next, p_hB).as_expr() - sp.resultant(p_psi_next, p_hA).as_expr()
        )
        assert diff_next != 0
        p_dn = sp.Poly(diff_next, q, domain="ZZ")
        deg_dn = p_dn.degree()
        lead_abs = abs(int(p_dn.nth(deg_dn))) * (q0**deg_dn)
        tail_abs = sum(abs(int(p_dn.nth(j))) * (q0**j) for j in range(deg_dn))
        if lead_abs <= tail_abs:
            assert sp.count_roots(p_dn, q0, sp.oo) == 0

        # 3. Check g distinct real roots in (-2*sqrt(q), 2*sqrt(q)) for prime powers q >= q0:
        node_den = int(entry["node_denominator"])
        node_nums = [int(v) for v in entry["node_numerators"]]
        check_roots_at_rational_nodes(g, hA, X, q, node_den, node_nums, q0, u_inv)
        check_roots_at_rational_nodes(g, hB, X, q, node_den, node_nums, q0, u_inv)

        max_c = max(abs(v) for v in bA_coeffs)
        print(
            f"  Theorem 4.2 (g = {g}): F_1..F_{N_match} equal, F_{N_match + 1} != 0, "
            f"and {g} real roots checked for q >= {q0:,} (max |coeff| = {max_c:,})."
        )


def main():
    print("Section 4: Chebyshev-totient families and higher-genus data (g = 15, 24, 32)")
    cross_check_trace_resultant()
    verify_thm_4_1()
    verify_thm_4_2()


if __name__ == "__main__":
    main()
