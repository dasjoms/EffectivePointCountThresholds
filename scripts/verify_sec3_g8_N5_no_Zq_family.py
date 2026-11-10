#!/usr/bin/env python3
"""
Computational checks for Section 3, Proposition 3.2(2) (g = 8, N = 5 Z[q]-families):

  1. By Proposition 3.2(1), any Z[q]-family of 8-dimensional q-Weil polynomials
     colliding on c_1, ..., c_5 has constant m_4 in Z with 1 <= |m_4| <= 512,
     a_1 = u_1 in {-2, -1, 0, 1}, and a_2 = u_1 * q + u_1^2.
  2. Equating powers of q in (F_3(B) - F_3(A)) / (3 m_4) = 0 solves 12 of the 24
     integer coefficients c_{k,j} linearly, forcing m_4 = 2 * k_4 with 1 <= |k_4| <= 256
     (or <= 260 under |m_4| <= 520).
  3. Substituting into (F_5(B) - F_5(A)) / (5 m_4) = 0:
     - q^26 and q^25 give u_2 - u_1^2 = 0 and u_1^3 - c_{6,3} = 0;
     - q^24, q^23, q^22, q^21 eliminate (u_62, u_72, u_61, u_70) linearly with
       constant integer pivots dividing 15;
     - q^20 is linear in u_50.
  4. Checks agreement with `check_g8_Zq_modp.c` (or rewrites it when `--regenerate`
     is passed), compiles in a temporary directory, and runs the exhaustive search
     over F_p for p in {7, 11, 13} (7 * 11 * 13 = 1001 > 260).
"""

from fractions import Fraction
import math
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import sympy as sp

SCRIPT_DIR = Path(__file__).resolve().parent
C_OUT_PATH = SCRIPT_DIR / "check_g8_Zq_modp.c"


def build_Zq_system():
    q, T = sp.symbols("q T")
    m4 = sp.Symbol("m4")
    k4 = sp.Symbol("k4")
    c_vars = {}
    a_expr = [sp.Integer(1)]
    for k in range(1, 9):
        expr = sp.Integer(0)
        for j in range(k // 2 + 1):
            v = sp.Symbol(f"c_{k}_{j}")
            c_vars[(k, j)] = v
            expr += v * (q**j)
        a_expr.append(expr)

    # (F_3(B) - F_3(A)) / (3 m_4) derived from sp.resultant:
    a_sym = [sp.Integer(1)] + [sp.Symbol(f"A{k}") for k in range(1, 9)]
    PA_sym = (
        T**16
        + q**8
        + sum(a_sym[k] * (T ** (16 - k) + (q ** (8 - k)) * (T**k)) for k in range(1, 8))
        + a_sym[8] * (T**8)
    )
    PB_sym = sp.expand(PA_sym + m4 * (T**4) * (T**4 - 1) * (T**4 - q**4))
    dF3_template = sp.expand(
        (
            sp.resultant(sp.cyclotomic_poly(3, T), PB_sym, T)
            - sp.resultant(sp.cyclotomic_poly(3, T), PA_sym, T)
        )
        / (3 * m4)
    )
    dF3_q = sp.expand(dF3_template.subs({a_sym[k]: a_expr[k] for k in range(1, 9)}))
    p3_q = sp.Poly(dF3_q, q)
    eqs3 = [p3_q.nth(dq) for dq in range(p3_q.degree() + 1) if p3_q.nth(dq) != 0]

    # Solve the 12 linear equations eqs3 = 0 for (c_1_0..c_5_2, c_6_0)
    # in terms of the 12 free variables (c_6_1..c_6_3, c_7_0..c_7_3, c_8_0..c_8_4) and m4.
    # Since c_2_0 = -c_6_1 + c_6_2 - c_7_0 + c_8_1 - c_8_4 + m4/2 + 1, we have 2 | m4,
    # so m4 = 2 * k4 with k4 in Z \ {0}, 1 <= |k4| <= 260.
    all_c_list = [c_vars[k] for k in sorted(c_vars.keys())]
    sol_raw = dict(zip(all_c_list, list(sp.linsolve(eqs3, all_c_list))[0]))
    assert sp.denom(sp.together(sol_raw[c_vars[(2, 0)]] - m4 / 2)) == 1, "Expected m4/2 parity condition"

    free_c = [
        c_vars[(6, 1)],
        c_vars[(6, 2)],
        c_vars[(6, 3)],
        c_vars[(7, 0)],
        c_vars[(7, 1)],
        c_vars[(7, 2)],
        c_vars[(7, 3)],
        c_vars[(8, 0)],
        c_vars[(8, 1)],
        c_vars[(8, 2)],
        c_vars[(8, 3)],
        c_vars[(8, 4)],
    ]
    sol3 = {k_var: sp.expand(expr_v.subs(m4, 2 * k4)) for k_var, expr_v in sol_raw.items()}
    for k_var, expr_v in sol3.items():
        # Check that each solved variable has integer coefficients in (free_c, k4):
        assert expr_v.free_symbols <= set(free_c + [k4])
        assert all(val.is_integer for val in sp.Poly(expr_v, *(free_c + [k4])).coeffs())

    a_elim = [sp.expand(e.subs(sol3)) for e in a_expr]

    # Tuple-polynomial arithmetic in the 13 integer variables (free_c[0..11], k4):
    var_names = [v.name for v in free_c] + ["k4"]
    NV = len(var_names)
    var_idx = {nm: i for i, nm in enumerate(var_names)}
    ZERO_M = (0,) * NV

    def p_add(P, Q):
        R = dict(P)
        for k, v in Q.items():
            nv = R.get(k, 0) + v
            if nv:
                R[k] = nv
            elif k in R:
                del R[k]
        return R

    def p_sub(P, Q):
        R = dict(P)
        for k, v in Q.items():
            nv = R.get(k, 0) - v
            if nv:
                R[k] = nv
            elif k in R:
                del R[k]
        return R

    def p_mul(P, Q):
        if not P or not Q:
            return {}
        R = {}
        for k1, v1 in P.items():
            for k2, v2 in Q.items():
                km = tuple(a + b for a, b in zip(k1, k2))
                nv = R.get(km, 0) + v1 * v2
                if nv:
                    R[km] = nv
                elif km in R:
                    del R[km]
        return R

    def q_trim(A):
        while A and not A[-1]:
            A.pop()
        return A

    def q_add(A, B):
        n = max(len(A), len(B))
        return q_trim([p_add(A[i] if i < len(A) else {}, B[i] if i < len(B) else {}) for i in range(n)])

    def q_sub(A, B):
        n = max(len(A), len(B))
        return q_trim([p_sub(A[i] if i < len(A) else {}, B[i] if i < len(B) else {}) for i in range(n)])

    def q_shift(A, sh):
        return ([{} for _ in range(sh)] + list(A)) if A else []

    def q_scale(A, c):
        if c == 0 or not A:
            return []
        return [{k: v * c for k, v in mp.items()} for mp in A]

    def q_mul(A, B):
        if not A or not B:
            return []
        out = [{} for _ in range(len(A) + len(B) - 1)]
        for i, pi in enumerate(A):
            if not pi:
                continue
            for j, pj in enumerate(B):
                if not pj:
                    continue
                out[i + j] = p_add(out[i + j], p_mul(pi, pj))
        return q_trim(out)

    def sym_lin_to_qpoly(expr):
        pq = sp.Poly(sp.expand(expr), q)
        if pq.is_zero:
            return []
        out = []
        for dq in range(pq.degree() + 1):
            sub_e = sp.expand(pq.nth(dq))
            mp = {}
            if sub_e != 0:
                for nm, idx in var_idx.items():
                    cv = int(sub_e.coeff(sp.Symbol(nm)))
                    if cv:
                        m = [0] * NV
                        m[idx] = 1
                        mp[tuple(m)] = cv
                c0 = int(sub_e.subs({sp.Symbol(nm): 0 for nm in var_names}))
                if c0:
                    mp[ZERO_M] = c0
            out.append(mp)
        return q_trim(out)

    aq = [sym_lin_to_qpoly(e) for e in a_elim]

    # Q(zeta_5) tower norm of P_A and P_B:
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

    def split_tz(e):
        pz = sp.Poly(e, z5)
        pt0 = sp.Poly(pz.nth(0), th)
        pt1 = sp.Poly(pz.nth(1), th)
        return int(pt0.nth(0)), int(pt0.nth(1)), int(pt1.nth(0)), int(pt1.nth(1))

    X0, X1, Y0, Y1 = [], [], [], []

    def add_contrib(qpoly, c_x0, c_x1, c_y0, c_y1):
        nonlocal X0, X1, Y0, Y1
        if c_x0:
            X0 = q_add(X0, q_scale(qpoly, c_x0))
        if c_x1:
            X1 = q_add(X1, q_scale(qpoly, c_x1))
        if c_y0:
            Y0 = q_add(Y0, q_scale(qpoly, c_y0))
        if c_y1:
            Y1 = q_add(Y1, q_scale(qpoly, c_y1))

    add_contrib(aq[8], 1, 0, 0, 0)
    add_contrib([{ZERO_M: 1}], *split_tz(zp[8]))
    add_contrib(q_shift([{ZERO_M: 1}], 8), *split_tz(zm[8]))
    for k in range(1, 8):
        add_contrib(aq[k], *split_tz(zp[8 - k]))
        add_contrib(q_shift(aq[k], 8 - k), *split_tz(zm[8 - k]))

    def mul_th(P0, P1, Q0, Q1):
        ac = q_mul(P0, Q0)
        bd = q_mul(P1, Q1)
        ad_bc = q_add(q_mul(P0, Q1), q_mul(P1, Q0))
        return q_add(ac, bd), q_sub(ad_bc, bd)

    X2_0, X2_1 = mul_th(X0, X1, X0, X1)
    Y2_0, Y2_1 = mul_th(Y0, Y1, Y0, Y1)
    XY_0, XY_1 = mul_th(X0, X1, Y0, Y1)
    XYth_0, XYth_1 = XY_1, q_sub(XY_0, XY_1)
    A0 = q_add(q_add(X2_0, Y2_0), XYth_0)
    A1 = q_add(q_add(X2_1, Y2_1), XYth_1)

    # Perturbation delta_a: da_4 = m4, da_8 = -m4*(q^4 + 1) => dX + dY*z5 = m4*(zp[4] + q^4*zm[4] - q^4 - 1)
    d_expr = mod_q5(zp[4] + (q**4) * zm[4] - (q**4) - 1)
    pz_d = sp.Poly(d_expr, z5)

    def sc_qpoly(s_e):
        pq = sp.Poly(sp.expand(s_e), q)
        if pq.is_zero:
            return []
        return q_trim([{ZERO_M: int(pq.nth(i))} if pq.nth(i) != 0 else {} for i in range(pq.degree() + 1)])

    pt_dx = sp.Poly(pz_d.nth(0), th)
    pt_dy = sp.Poly(pz_d.nth(1), th)
    dX0, dX1 = sc_qpoly(pt_dx.nth(0)), sc_qpoly(pt_dx.nth(1))
    dY0, dY1 = sc_qpoly(pt_dy.nth(0)), sc_qpoly(pt_dy.nth(1))

    twoXdX_0, twoXdX_1 = mul_th(q_scale(X0, 2), q_scale(X1, 2), dX0, dX1)
    twoYdY_0, twoYdY_1 = mul_th(q_scale(Y0, 2), q_scale(Y1, 2), dY0, dY1)
    XdY_0, XdY_1 = mul_th(X0, X1, dY0, dY1)
    YdX_0, YdX_1 = mul_th(Y0, Y1, dX0, dX1)
    sXY_0, sXY_1 = q_add(XdY_0, YdX_0), q_add(XdY_1, YdX_1)
    L0 = q_add(q_add(twoXdX_0, twoYdY_0), sXY_1)
    L1 = q_add(q_add(twoXdX_1, twoYdY_1), q_sub(sXY_0, sXY_1))

    dX2_0, dX2_1 = mul_th(dX0, dX1, dX0, dX1)
    dY2_0, dY2_1 = mul_th(dY0, dY1, dY0, dY1)
    dXY_0, dXY_1 = mul_th(dX0, dX1, dY0, dY1)
    Q0 = q_add(q_add(dX2_0, dY2_0), dXY_1)
    Q1 = q_add(q_add(dX2_1, dY2_1), q_sub(dXY_0, dXY_1))

    k4_m = [0] * NV
    k4_m[var_idx["k4"]] = 1
    M4 = [{tuple(k4_m): 2}]  # m4 = 2 * k4
    d0 = q_add(L0, q_mul(M4, Q0))
    d1 = q_add(L1, q_mul(M4, Q1))
    tot = q_sub(
        q_add(
            q_add(
                q_mul(q_sub(q_scale(A0, 2), A1), d0),
                q_mul(q_sub(q_scale(A0, -1), q_scale(A1, 2)), d1),
            ),
            q_mul(M4, q_sub(q_mul(d0, d0), q_mul(d0, d1))),
        ),
        q_mul(M4, q_mul(d1, d1)),
    )
    for mp in tot:
        for val in mp.values():
            assert val % 5 == 0

    # Cross-check `tot` (= (F_5(B) - F_5(A)) / m_4) against sp.resultant at a test point:
    test_vals = {nm: (i % 3) - 1 for i, nm in enumerate(var_names)}
    test_vals["k4"] = 3
    m4_val = 2 * test_vals["k4"]
    qv = 3
    lhs_num = 0
    for dq, mp in enumerate(tot):
        for mon, val in mp.items():
            term_v = val * m4_val
            for i, e in enumerate(mon):
                if e:
                    term_v *= test_vals[var_names[i]] ** e
            lhs_num += term_v * (qv**dq)
    sub_all = {sp.Symbol(nm): v for nm, v in test_vals.items()}
    sub_all[q] = qv
    a_num = [int(e.subs(sub_all)) for e in a_elim]
    PA_num = (
        T**16
        + qv**8
        + sum(a_num[k] * (T ** (16 - k) + (qv ** (8 - k)) * (T**k)) for k in range(1, 8))
        + a_num[8] * (T**8)
    )
    PB_num = sp.expand(PA_num + m4_val * (T**4) * (T**4 - 1) * (T**4 - qv**4))
    rhs_num = int(
        sp.resultant(sp.cyclotomic_poly(5, T), PB_num, T)
        - sp.resultant(sp.cyclotomic_poly(5, T), PA_num, T)
    )
    assert lhs_num == rhs_num, f"Cross-check mismatch: {lhs_num} != {rhs_num}"

    # Check q^26 and q^25 coefficients of (F_5(B) - F_5(A)) / (5 m_4) before substitution:
    assert len(tot) == 27, f"Expected max q-degree 26 in dF5, got {len(tot) - 1}"
    sym_vars = [sp.Symbol(nm) for nm in var_names]

    def mp_to_sym(mp):
        return sp.expand(
            sum((val // 5) * math.prod(sym_vars[i] ** e for i, e in enumerate(mon)) for mon, val in mp.items())
        )

    u1_expr = sol3[sp.Symbol("c_1_0")]
    u2_expr = sol3[sp.Symbol("c_2_0")]
    c63_sym = sp.Symbol("c_6_3")
    eq26_sym = mp_to_sym(tot[26])
    assert sp.expand(eq26_sym - (u2_expr - u1_expr**2)) == 0, f"Unexpected q^26 coeff: {eq26_sym}"
    # Eliminate c_8_4 linearly via u_2 = u_1^2 to check q^25:
    c84_sym = sp.Symbol("c_8_4")
    c84_sol = sp.solve(sp.expand(u2_expr - u1_expr**2), c84_sym)[0]
    eq25_sym = sp.expand(mp_to_sym(tot[25]).subs(c84_sym, c84_sol))
    assert sp.expand(eq25_sym - (u1_expr**3 - c63_sym)) == 0, f"Unexpected q^25 coeff: {eq25_sym}"

    return tot, var_names, sol3


def emit_and_run_c_solver(tot, var_names, sol3, regenerate=False):
    NR = 10
    ZERO_R = (0,) * NR

    def r_add(P, Q):
        R = dict(P)
        for k, v in Q.items():
            nv = R.get(k, Fraction(0)) + v
            if nv:
                R[k] = nv
            elif k in R:
                del R[k]
        return R

    def r_mul(P, Q):
        if not P or not Q:
            return {}
        R = {}
        for k1, v1 in P.items():
            for k2, v2 in Q.items():
                km = tuple(a + b for a, b in zip(k1, k2))
                nv = R.get(km, Fraction(0)) + v1 * v2
                if nv:
                    R[km] = nv
                elif km in R:
                    del R[km]
        return R

    def r_pow(P, e):
        res = {ZERO_R: Fraction(1)}
        for _ in range(e):
            res = r_mul(res, P)
        return res

    def make_var(idx, c=1):
        m = [0] * NR
        m[idx] = 1
        return {tuple(m): Fraction(c)}

    def solve_linear_var(P, var_idx):
        c_var = Fraction(0)
        rest = {}
        for mon, val in P.items():
            if mon[var_idx] >= 1:
                assert mon[var_idx] == 1 and sum(mon) == 1, f"Non-constant linear pivot: {mon}"
                c_var += val
            else:
                rest[mon] = val
        # Check pivot only involves primes dividing 15 (coprime to 7, 11, 13):
        num_abs = abs(c_var.numerator)
        for pr in [2, 3, 5]:
            while num_abs % pr == 0:
                num_abs //= pr
        assert num_abs == 1 and c_var.denominator == 1, f"Unexpected pivot: {c_var}"
        return {mon: -val / c_var for mon, val in rest.items()}

    def sub_var(P, var_idx, V_dict):
        R = {}
        pws = {0: {ZERO_R: Fraction(1)}}
        for mon, val in P.items():
            e = mon[var_idx]
            if e == 0:
                R = r_add(R, {mon: val})
            else:
                if e not in pws:
                    pws[e] = r_pow(V_dict, e)
                bm = list(mon)
                bm[var_idx] = 0
                R = r_add(R, r_mul({tuple(bm): val}, pws[e]))
        return R

    syms_old = [sp.Symbol(nm) for nm in var_names[:12]]
    u1, u2, u63 = sp.symbols("u1 u2 u63")
    orig_syms = [
        sp.Symbol(nm)
        for nm in ["u31", "u41", "u51", "u50", "u72", "u71", "u70", "u61", "k4", "u62"]
    ]
    eqs_change = [
        sp.Eq(sol3[sp.Symbol("c_1_0")], u1),
        sp.Eq(sol3[sp.Symbol("c_2_0")], u2),
        sp.Eq(sp.Symbol("c_6_3"), u63),
        sp.Eq(sol3[sp.Symbol("c_3_1")], orig_syms[0]),
        sp.Eq(sol3[sp.Symbol("c_4_1")], orig_syms[1]),
        sp.Eq(sol3[sp.Symbol("c_5_1")], orig_syms[2]),
        sp.Eq(sol3[sp.Symbol("c_5_0")], orig_syms[3]),
        sp.Eq(sp.Symbol("c_6_2"), orig_syms[9]),
        sp.Eq(sp.Symbol("c_7_2"), orig_syms[4]),
        sp.Eq(sp.Symbol("c_7_1"), orig_syms[5]),
        sp.Eq(sp.Symbol("c_7_0"), orig_syms[6]),
        sp.Eq(sp.Symbol("c_6_1"), orig_syms[7]),
    ]
    c_tuple = list(sp.linsolve(eqs_change, syms_old))[0]

    def sym_lin_to_r(expr):
        expr = sp.expand(expr)
        assert sp.denom(sp.together(expr)) == 1, f"Non-integer coefficient in {expr}"
        R = {}
        for idx, s in enumerate(orig_syms):
            c = int(expr.coeff(s))
            if c:
                m = [0] * NR
                m[idx] = 1
                R[tuple(m)] = Fraction(c)
        c0 = int(expr.subs({s: 0 for s in orig_syms}))
        if c0:
            R[ZERO_R] = Fraction(c0)
        return R

    W_sub = r_add(r_add(make_var(7, 1), make_var(6, 1)), make_var(5, -1))

    # Build compact C99 table representation for cases u1 in {0, 1, -1, -2}:
    # Active 6 variables in C: 0:u31, 1:u41, 2:u51, 3:W, 4:k4 (where m4 = 2*k4), 5:u50
    c_lines = [
        "/* Generated by verify_sec3_g8_N5_no_Zq_family.py (C99) */",
        "#include <stdio.h>",
        "#include <stdint.h>",
        "",
        "typedef struct { int64_t c; uint8_t e[6]; } Term;",
        "",
        "static inline int64_t modp(int64_t x, int64_t p) {",
        "    x %= p;",
        "    return x < 0 ? x + p : x;",
        "}",
        "",
        "static int64_t modinv(int64_t a, int64_t p) {",
        "    int64_t t = 0, newt = 1, r = p, newr = modp(a, p);",
        "    while (newr != 0) {",
        "        int64_t q = r / newr;",
        "        int64_t tmp = t - q * newt; t = newt; newt = tmp;",
        "        tmp = r - q * newr; r = newr; newr = tmp;",
        "    }",
        "    return t < 0 ? t + p : t;",
        "}",
        "",
        "static int64_t eval_poly(const Term *terms, int n, int64_t pw[6][13], int64_t p) {",
        "    int64_t acc = 0;",
        "    for (int i = 0; i < n; i++) {",
        "        int64_t v = modp(terms[i].c, p);",
        "        for (int k = 0; k < 6; k++) {",
        "            uint8_t e = terms[i].e[k];",
        "            if (e) v = (v * pw[k][e]) % p;",
        "        }",
        "        acc = (acc + v) % p;",
        "    }",
        "    return acc;",
        "}",
        "",
    ]

    def format_term_array(name, P_dict):
        lcm_d = 1
        for val in P_dict.values():
            lcm_d = math.lcm(lcm_d, val.denominator)
        # Ensure denominator only divides a power of 15:
        tmp_d = lcm_d
        for pr in [3, 5]:
            while tmp_d % pr == 0:
                tmp_d //= pr
        assert tmp_d == 1, f"Bad denominator {lcm_d}"
        idx_map = [0, 1, 2, 5, 8, 3]  # u31, u41, u51, W, k4, u50
        items = []
        for mon, val in P_dict.items():
            iv = int(val * lcm_d)
            exps = [mon[j] for j in idx_map]
            items.append(f"{{{iv}LL, {{{','.join(str(x) for x in exps)}}}}}")
        c_lines.append(f"static const Term {name}[{max(1, len(items))}] = {{")
        for off in range(0, len(items), 4):
            c_lines.append("    " + ", ".join(items[off : off + 4]) + ",")
        c_lines.append("};")
        return len(items)

    u1_list = [0, 1, -1, -2]
    meta_cases = []
    for ci, u1_val in enumerate(u1_list):
        subs_base = {u1: u1_val, u2: u1_val**2, u63: u1_val**3}
        ct_r = [sym_lin_to_r(e.subs(subs_base)) for e in c_tuple]
        ct_pows = [{e: r_pow(ct_r[i], e) for e in range(4)} for i in range(12)]
        k4_pows = {e: r_pow(make_var(8, 1), e) for e in range(4)}
        eqs_r = {}
        for dq in range(len(tot) - 1, 11, -1):
            R = {}
            for mon, val in tot[dq].items():
                term = {ZERO_R: Fraction(val // 5)}
                for i in range(12):
                    if mon[i]:
                        term = r_mul(term, ct_pows[i][mon[i]])
                if mon[12]:
                    term = r_mul(term, k4_pows[mon[12]])
                R = r_add(R, term)
            eqs_r[dq] = R
        # Numerical cross-check of variable change eqs_r[20] vs tot[20]:
        tv_orig = [2, -1, 1, 3, -2, 1, 2, -1, 3, 1]
        sub_orig = dict(zip(orig_syms, tv_orig))
        sub_orig.update(subs_base)
        tv_old = [int(e.subs(sub_orig)) for e in c_tuple] + [tv_orig[8]]
        v_tot20 = sum(
            (val // 5) * math.prod(tv_old[i] ** e for i, e in enumerate(mon))
            for mon, val in tot[20].items()
        )
        v_eqr20 = sum(
            val * math.prod(tv_orig[i] ** e for i, e in enumerate(mon))
            for mon, val in eqs_r[20].items()
        )
        assert v_eqr20 == Fraction(v_tot20), f"Variable-change mismatch at u1={u1_val}"
        for dq in range(len(tot) - 1, 24, -1):
            assert len(eqs_r[dq]) == 0
        u62_d = solve_linear_var(eqs_r[24], 9)
        for dq in range(23, 11, -1):
            eqs_r[dq] = sub_var(eqs_r[dq], 9, u62_d)
        u72_d = solve_linear_var(eqs_r[23], 4)
        for dq in range(22, 11, -1):
            eqs_r[dq] = sub_var(eqs_r[dq], 4, u72_d)
            eqs_r[dq] = sub_var(eqs_r[dq], 5, W_sub)
        u61_d = solve_linear_var(eqs_r[22], 7)
        for dq in range(21, 11, -1):
            eqs_r[dq] = sub_var(eqs_r[dq], 7, u61_d)
        u70_d = solve_linear_var(eqs_r[21], 6)
        for dq in range(20, 11, -1):
            eqs_r[dq] = sub_var(eqs_r[dq], 6, u70_d)

        # Split eqs_r[20] = A * u50 + B (u50 is index 3):
        lcm20 = 1
        for val in eqs_r[20].values():
            lcm20 = math.lcm(lcm20, val.denominator)
        A20, B20 = {}, {}
        for mon, val in eqs_r[20].items():
            assert mon[3] <= 1
            scaled_v = Fraction(int(val * lcm20))
            if mon[3] == 1:
                bm = list(mon)
                bm[3] = 0
                A20[tuple(bm)] = scaled_v
            else:
                B20[mon] = scaled_v
        nA = format_term_array(f"c{ci}_A20", A20)
        nB = format_term_array(f"c{ci}_B20", B20)
        rem_eqs = []
        for dq in range(19, 11, -1):
            nm = f"c{ci}_eq{dq}"
            cnt = format_term_array(nm, eqs_r[dq])
            rem_eqs.append((nm, cnt))
        meta_cases.append((ci, u1_val, nA, nB, rem_eqs))

    # Emit per-case solver function in C:
    for ci, u1_val, nA, nB, rem_eqs in meta_cases:
        c_lines.append(f"static long solve_case_{ci}(int64_t p) {{")
        c_lines.append("    long count = 0;")
        c_lines.append("    int64_t pw[6][13];")
        c_lines.append("    for (int k = 0; k < 6; k++) pw[k][0] = 1;")
        c_lines.append("    for (int64_t k4 = 1; k4 < p; k4++) {")
        c_lines.append("      for (int e = 1; e <= 12; e++) pw[4][e] = (pw[4][e-1] * k4) % p;")
        c_lines.append("      for (int64_t u31 = 0; u31 < p; u31++) {")
        c_lines.append("        for (int e = 1; e <= 12; e++) pw[0][e] = (pw[0][e-1] * u31) % p;")
        c_lines.append("        for (int64_t u41 = 0; u41 < p; u41++) {")
        c_lines.append("          for (int e = 1; e <= 12; e++) pw[1][e] = (pw[1][e-1] * u41) % p;")
        c_lines.append("          for (int64_t u51 = 0; u51 < p; u51++) {")
        c_lines.append("            for (int e = 1; e <= 12; e++) pw[2][e] = (pw[2][e-1] * u51) % p;")
        c_lines.append("            for (int64_t W = 0; W < p; W++) {")
        c_lines.append("              for (int e = 1; e <= 12; e++) pw[3][e] = (pw[3][e-1] * W) % p;")
        c_lines.append("              pw[5][1] = 0;")
        c_lines.append(f"              int64_t A = eval_poly(c{ci}_A20, {nA}, pw, p);")
        c_lines.append(f"              int64_t B = eval_poly(c{ci}_B20, {nB}, pw, p);")
        c_lines.append("              int64_t u50_start = 0, u50_end = p - 1;")
        c_lines.append("              if (A != 0) {")
        c_lines.append("                  int64_t u_sol = ((p - B) * modinv(A, p)) % p;")
        c_lines.append("                  u50_start = u_sol; u50_end = u_sol;")
        c_lines.append("              } else if (B != 0) { continue; }")
        c_lines.append("              for (int64_t u50 = u50_start; u50 <= u50_end; u50++) {")
        c_lines.append("                  for (int e = 1; e <= 12; e++) pw[5][e] = (pw[5][e-1] * u50) % p;")
        for nm, cnt in rem_eqs:
            c_lines.append(f"                  if (eval_poly({nm}, {cnt}, pw, p) != 0) continue;")
        c_lines.append("                  count++;")
        c_lines.append("              }")
        c_lines.append("            }")
        c_lines.append("          }")
        c_lines.append("        }")
        c_lines.append("      }")
        c_lines.append("    }")
        c_lines.append("    return count;")
        c_lines.append("}")

    c_lines.append(
        """
int main(void) {
    const int64_t primes[3] = {7, 11, 13};
    const int u1_vals[4] = {0, 1, -1, -2};
    long total_count = 0;
    for (int pi = 0; pi < 3; pi++) {
        int64_t p = primes[pi];
        long h0 = solve_case_0(p);
        long h1 = solve_case_1(p);
        long h2 = solve_case_2(p);
        long h3 = solve_case_3(p);
        long hs[4] = {h0, h1, h2, h3};
        for (int ci = 0; ci < 4; ci++) {
            printf("  p=%2lld, a1=%2d: solutions (k4 != 0 mod p) = %ld\\n",
                   (long long)p, u1_vals[ci], hs[ci]);
            total_count += hs[ci];
        }
    }
    return total_count == 0 ? 0 : 1;
}
"""
    )

    c_source = "\n".join(c_lines)
    if regenerate:
        C_OUT_PATH.write_text(c_source, encoding="utf-8")
    else:
        assert C_OUT_PATH.exists(), f"Missing {C_OUT_PATH}; run with --regenerate to create it."
        existing = C_OUT_PATH.read_text(encoding="utf-8")
        assert existing == c_source, (
            f"{C_OUT_PATH.name} differs from freshly derived C99 tables; "
            "run with --regenerate to update."
        )

    compiler = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
    if not compiler:
        raise RuntimeError("No C compiler (cc / gcc / clang) found on PATH.")
    with tempfile.TemporaryDirectory() as tmpdir:
        c_tmp = Path(tmpdir) / "check_g8_Zq_modp.c"
        c_tmp.write_text(c_source, encoding="utf-8")
        bin_path = Path(tmpdir) / "check_g8_Zq_modp"
        subprocess.run([compiler, "-O2", str(c_tmp), "-o", str(bin_path)], check=True)
        res = subprocess.run([str(bin_path)], check=True, text=True, capture_output=True)
        print(res.stdout.rstrip())


def main():
    regenerate = "--regenerate" in sys.argv[1:]
    print("Section 3: g = 8, N = 5 Z[q]-family modular search (Proposition 3.2(2))")
    tot, var_names, sol3 = build_Zq_system()
    print(
        "  Derived reduced resultant system (q^26: u_2 = u_1^2; q^25: c_6_3 = u_1^3) "
        "and matched check_g8_Zq_modp.c."
    )
    emit_and_run_c_solver(tot, var_names, sol3, regenerate=regenerate)
    print(
        "  Modular search over p in {7, 11, 13}: 0 solutions with k_4 != 0 (mod p) "
        "(m_4 = 2*k_4, 1 <= |k_4| <= 260 < 1001)."
    )


if __name__ == "__main__":
    main()
