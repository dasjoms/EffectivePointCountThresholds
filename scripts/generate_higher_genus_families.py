#!/usr/bin/env python3
"""
Recompute the explicit ordinary Z[q]-families for Theorem 4.2 (g = 15, 24, 32)
via rational RREF, Hermite normal form, and LLL lattice reduction, and write
the output to `data/higher_genus_families.json`.

Requires `python-flint` and `numpy` in addition to `sympy` (whereas
`verify_sec4_chebyshev_asymptotics.py` reads `data/higher_genus_families.json`
using `sympy` alone).
"""

import itertools
import json
import math
from pathlib import Path

import flint
import numpy as np
import sympy as sp

ROOT_DIR = Path(__file__).resolve().parent.parent
DATA_PATH = ROOT_DIR / "data" / "higher_genus_families.json"


def compute_psi_d_table():
    """Return {d: (phi(d), [coeffs_in_q_of_X^(phi(d)-r) for r=0..phi(d)])}."""
    X_s, q_s, T_s = sp.symbols("X q T")
    table = {}
    for d in [1, 2, 5, 7, 8]:
        if d == 1:
            pX = sp.Poly(X_s - (q_s + 1), X_s)
        elif d == 2:
            pX = sp.Poly(X_s + (q_s + 1), X_s)
        else:
            phi_d = sp.cyclotomic_poly(d, T_s)
            res = sp.resultant(phi_d, T_s**2 - X_s * T_s + q_s, T_s)
            pX = sp.Poly(sp.expand(res), X_s)
        assert pX.LC() == 1
        deg = pX.degree()
        coeffs_q = [
            [int(c) for c in sp.Poly(pX.nth(deg - r), q_s).all_coeffs()]
            for r in range(deg + 1)
        ]
        table[d] = (deg, coeffs_q)
    return table


def eval_poly_q(c_list, qv):
    v = 0
    for c in c_list:
        v = v * qv + c
    return v


def poly_mul_int(A, B):
    R = [0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            R[i + j] += a * b
    return R


def eval_F346_linear_row(g, qv, dh_coeffs_at_q):
    """
    Integer coefficients of the three affine-linear hyperplanes
    F_4(B) - F_4(A) = 0, F_3(B) - F_3(A) = 0, F_6(B) - F_6(A) = 0
    in b_1(qv), ..., b_g(qv) for a given perturbation dh(X) at q = qv.
    """
    v = qv - 1
    pow4 = [(1, 0)]
    for _ in range(g):
        re, im = pow4[-1]
        pow4.append((im * v, -re * v))
    dR4 = sum(dh_coeffs_at_q[k] * pow4[g - k][0] for k in range(1, g + 1))
    dM4 = sum(dh_coeffs_at_q[k] * pow4[g - k][1] for k in range(1, g + 1))
    const4 = 2 * dR4 * pow4[g][0] + 2 * dM4 * pow4[g][1] + dR4 * dR4 + dM4 * dM4
    coeff_b4 = [
        2 * dR4 * ((-1) ** k * pow4[g - k][0]) + 2 * dM4 * ((-1) ** k * pow4[g - k][1])
        for k in range(1, g + 1)
    ]

    def norm_w_eq(z_a, z_b):
        pows = [(1, 0)]
        for _ in range(g):
            x, y = pows[-1]
            pows.append((x * z_a - y * z_b, x * z_b + y * z_a - y * z_b))
        dx = sum(dh_coeffs_at_q[k] * pows[g - k][0] for k in range(1, g + 1))
        dy = sum(dh_coeffs_at_q[k] * pows[g - k][1] for k in range(1, g + 1))
        Lx = 2 * dx - dy
        Ly = -dx + 2 * dy
        const_d = Lx * pows[g][0] + Ly * pows[g][1] + (dx * dx - dx * dy + dy * dy)
        cb = [
            Lx * ((-1) ** k * pows[g - k][0]) + Ly * ((-1) ** k * pows[g - k][1])
            for k in range(1, g + 1)
        ]
        return cb, const_d

    cb3, const3 = norm_w_eq(-qv, 1 - qv)
    cb6, const6 = norm_w_eq(1, 1 - qv)
    return (coeff_b4, -const4), (cb3, -const3), (cb6, -const6)


def solve_g15_family(psi_table):
    """Construct the ordinary g=15, N=6, L=24q Chebyshev family."""
    g = 15
    L = 24
    d_list = [1, 2, 5]
    var_map = [(k, j) for k in range(1, g + 1) for j in range(k // 2 + 1)]
    M = len(var_map)
    cheb_even = {
        2 * m: ((-1) ** m) * (g * math.comb(g - m, m)) // (g - m)
        for m in range(1, 8)
    }

    rows, rhs = [], []
    for qv in range(2 * g + 10):
        prod_p = [L * qv]
        for d in d_list:
            _, cq = psi_table[d]
            prod_p = poly_mul_int(prod_p, [eval_poly_q(c, qv) for c in cq])
        dh = [0] * (g + 1)
        for r, val in enumerate(prod_p):
            dh[g - 6 + r] = val
        for cb, rh in eval_F346_linear_row(g, qv, dh):
            rows.append([cb[k - 1] * (qv**j) for (k, j) in var_map])
            rhs.append(rh)

    for m in range(1, 6):
        idx = var_map.index((2 * m, m))
        r = [0] * M
        r[idx] = 1
        rows.append(r)
        rhs.append(cheb_even[2 * m])
    idx15_0 = var_map.index((15, 0))
    r = [0] * M
    r[idx15_0] = 1
    rows.append(r)
    rhs.append(1)

    Aug = flint.fmpq_mat(len(rows), M + 1)
    for i, row in enumerate(rows):
        for j, val in enumerate(row):
            Aug[i, j] = val
        Aug[i, M] = rhs[i]
    R, rk = Aug.rref()
    pivots = [(i, next(j for j in range(M) if R[i, j] != 0)) for i in range(rk)]
    piv_cols = {j for _, j in pivots}
    free_cols = [j for j in range(M) if j not in piv_cols]

    idx12_6 = free_cols.index(var_map.index((12, 6)))
    idx14_7 = free_cols.index(var_map.index((14, 7)))
    other_fcs = [k for k in range(len(free_cols)) if k not in (idx12_6, idx14_7)]

    for tup in itertools.product([0, 1, -1], repeat=len(other_fcs)):
        fvals = [0] * len(free_cols)
        fvals[idx12_6] = cheb_even[12]
        fvals[idx14_7] = cheb_even[14]
        for pos, v in zip(other_fcs, tup):
            fvals[pos] = v
        if all(
            (R[i, M] - sum(R[i, free_cols[k]] * fvals[k] for k in range(len(free_cols)))).q == 1
            for i, _ in pivots
        ):
            x_full = [0] * M
            for k, fc in enumerate(free_cols):
                x_full[fc] = fvals[k]
            for i, j in pivots:
                val = R[i, M] - sum(R[i, free_cols[k]] * fvals[k] for k in range(len(free_cols)))
                x_full[j] = int(val.p)
            node_den = 100000
            node_nums = (
                [-2 * node_den]
                + [round(2 * math.cos(j * math.pi / g) * node_den) for j in range(g - 1, 0, -1)]
                + [2 * node_den]
            )
            return {
                "g": g,
                "N": 6,
                "d_list": d_list,
                "L": L,
                "q_power_in_dh": 1,
                "bgA_mod_q": 1,
                "bgB_mod_q": 1,
                "q0": 1086853,
                "sturm_u_inv_bound": 1043,
                "node_denominator": node_den,
                "node_numerators": node_nums,
                "var_map": [list(p) for p in var_map],
                "bA_coeffs": x_full,
            }
    raise RuntimeError("Failed to find g=15 integer ordinary solution")


def solve_even_lll_family(N_target, g_t, d_list, psi_table):
    """
    Construct the HNF + LLL-reduced ordinary Z[q]-family for even genus g_t
    with q^{-g/2} h_A(x*sqrt(q)) -> 2*T_g(x/2) + 1 and
         q^{-g/2} h_B(x*sqrt(q)) -> 2*T_g(x/2) - 1.
    """
    D_star = sum(psi_table[d][0] for d in d_list)
    var_map = [(k, j) for k in range(1, g_t + 1) for j in range(k // 2 + 1)]
    M = len(var_map)
    cheb_even = {
        2 * m: ((-1) ** m) * (g_t * math.comb(g_t - m, m)) // (g_t - m)
        for m in range(1, g_t // 2 + 1)
    }
    idx_g0 = var_map.index((g_t, 0))
    # Set c_(g, g/2) = 2*(-1)^(g/2) + 1 so that h_A -> 2*T_g(x/2) + 1 and h_B -> 2*T_g(x/2) - 1:
    last_even_val = 2 * ((-1) ** (g_t // 2)) + 1
    L_val = 2

    rows0, rhs = [], []
    for qv in range(2 * g_t + 8):
        prod_p = [L_val]
        for d in d_list:
            _, cq = psi_table[d]
            prod_p = poly_mul_int(prod_p, [eval_poly_q(c, qv) for c in cq])
        dh = [0] * (g_t + 1)
        for r, val in enumerate(prod_p):
            dh[g_t - D_star + r] = val
        for cb, rh in eval_F346_linear_row(g_t, qv, dh):
            rows0.append([cb[k - 1] * (qv**j) for (k, j) in var_map])
            rhs.append(rh)

    for m in range(1, g_t // 2 + 1):
        val_t = cheb_even[2 * m] if 2 * m < g_t else last_even_val
        idx = var_map.index((2 * m, m))
        r = [0] * M
        r[idx] = 1
        rows0.append(r)
        rhs.append(val_t)
    r = [0] * M
    r[idx_g0] = 1
    rows0.append(r)
    rhs.append(1)

    Aug = flint.fmpq_mat(len(rows0), M + 1)
    for i, row in enumerate(rows0):
        for j, val in enumerate(row):
            Aug[i, j] = val
        Aug[i, M] = rhs[i]
    R, rk = Aug.rref()
    pivs = [(i, next(j for j in range(M) if R[i, j] != 0)) for i in range(rk)]
    piv_cols = {j for _, j in pivs}
    free_cols = [j for j in range(M) if j not in piv_cols]
    nf = len(free_cols)

    frac_rows = [
        i
        for i, _ in pivs
        if int(R[i, M].q) > 1 or any(int(R[i, f].q) > 1 for f in free_cols)
    ]
    rf = len(frac_rows)
    d_row = [
        math.lcm(int(R[i, M].q), *(int(R[i, f].q) for f in free_cols))
        for i in frac_rows
    ]
    B_mat = flint.fmpz_mat(nf + rf, rf)
    for fi, fcol in enumerate(free_cols):
        for ri, i in enumerate(frac_rows):
            di = d_row[ri]
            B_mat[fi, ri] = int((R[i, fcol] * di).p) % di
    for ri, di in enumerate(d_row):
        B_mat[nf + ri, ri] = di
    H, U = B_mat.hnf(transform=True)
    H_top = flint.fmpq_mat(rf, rf)
    for r1 in range(rf):
        for r2 in range(rf):
            H_top[r1, r2] = H[r1, r2]
    w_q = flint.fmpq_mat(1, rf)
    for ri, i in enumerate(frac_rows):
        di = d_row[ri]
        w_q[0, ri] = int((R[i, M] * di).p) % di
    u_vec = w_q * H_top.inv()
    assert all(int(u_vec[0, ri].q) == 1 for ri in range(rf))

    x_free0 = [
        sum(int(u_vec[0, ri].p) * int(U[ri, fi]) for ri in range(rf))
        for fi in range(nf)
    ]
    x0 = [0] * M
    for fi, fcol in enumerate(free_cols):
        x0[fcol] = x_free0[fi]
    for i, pcol in pivs:
        val = R[i, M] - sum(R[i, fcol] * x_free0[fi] for fi, fcol in enumerate(free_cols))
        assert int(val.q) == 1
        x0[pcol] = int(val.p)

    # Integer homogeneous kernel basis + LLL + Babai nearest-plane reduction:
    K_basis = []
    for k_idx in range(rf, rf + nf):
        kf = [int(U[k_idx, fi]) for fi in range(nf)]
        xh = [0] * M
        for fi, fcol in enumerate(free_cols):
            xh[fcol] = kf[fi]
        for i, pcol in pivs:
            val = -sum(R[i, fcol] * kf[fi] for fi, fcol in enumerate(free_cols))
            assert int(val.q) == 1
            xh[pcol] = int(val.p)
        K_basis.append(xh)

    L_mat = flint.fmpz_mat(nf, M)
    for r_i in range(nf):
        for c_j in range(M):
            L_mat[r_i, c_j] = K_basis[r_i][c_j]
    L_mat = L_mat.lll()
    B_red = [[int(L_mat[r_i, c_j]) for c_j in range(M)] for r_i in range(nf)]
    Bu = np.array(B_red, dtype=np.float64)
    Qu, Ru = np.linalg.qr(Bu.T, mode="reduced")
    cur = list(x0)
    for _ in range(15):
        vu = np.array(cur, dtype=np.float64)
        ch = False
        for i in range(nf - 1, -1, -1):
            c_i = int(round(float(np.dot(vu, Qu[:, i])) / float(Ru[i, i])))
            if c_i != 0:
                ch = True
                for c_j in range(M):
                    cur[c_j] -= c_i * B_red[i][c_j]
                vu = np.array(cur, dtype=np.float64)
        if not ch:
            break

    # Compute dyadic Chebyshev-node triangle-inequality threshold K_min:
    X_s, q_s, T_s = sp.symbols("X q T")
    c_dict = {var_map[idx]: cur[idx] for idx in range(M)}
    hAt = X_s**g_t + sum(
        ((-1) ** k) * sum(c_dict[(k, j)] * q_s**j for j in range(k // 2 + 1)) * X_s ** (g_t - k)
        for k in range(1, g_t + 1)
    )
    dh_t = sp.Integer(L_val)
    for d in d_list:
        if d == 1:
            dh_t *= X_s - (q_s + 1)
        elif d == 2:
            dh_t *= X_s + (q_s + 1)
        else:
            dh_t *= sp.expand(sp.resultant(sp.cyclotomic_poly(d, T_s), T_s**2 - X_s * T_s + q_s, T_s))
    hBt = sp.expand(hAt + dh_t)

    node_den = 1024
    node_nums = (
        [-2 * node_den]
        + [round(2 * math.cos(j * math.pi / g_t) * node_den) for j in range(g_t - 1, 0, -1)]
        + [2 * node_den]
    )
    all_polys = []
    for h_expr in (hAt, hBt):
        terms = sp.Poly(h_expr, X_s, q_s).terms()
        signs = []
        for num_nd in node_nums:
            pu = {}
            for (deg_x, deg_q), c in terms:
                pw = g_t - deg_x - 2 * deg_q
                pu[pw] = pu.get(pw, 0) + int(c) * (num_nd**deg_x) * (node_den ** (g_t - deg_x))
            signs.append(1 if pu.get(0, 0) > 0 else -1)
            all_polys.append(pu)
        assert all(signs[i] * signs[i + 1] == -1 for i in range(g_t))

    def tri_ok(K_val):
        for pu in all_polys:
            c0 = abs(pu[0])
            mpw = max(pu)
            lhs = sum(abs(v) * (K_val ** (mpw - pw)) for pw, v in pu.items() if pw >= 1)
            if lhs >= c0 * (K_val**mpw):
                return False
        return True

    lo, hi = 1, 10**9
    while lo < hi:
        mid = (lo + hi) // 2
        if tri_ok(mid):
            hi = mid
        else:
            lo = mid + 1

    return {
        "g": g_t,
        "N": N_target,
        "d_list": d_list,
        "L": L_val,
        "q_power_in_dh": 0,
        "bgA_mod_q": 1,
        "bgB_mod_q": -1,
        "q0": lo * lo,
        "triangle_u_inv_bound": lo,
        "node_denominator": node_den,
        "node_numerators": node_nums,
        "var_map": [list(p) for p in var_map],
        "bA_coeffs": cur,
    }


def main():
    psi_table = compute_psi_d_table()
    families = {
        "15": solve_g15_family(psi_table),
        "24": solve_even_lll_family(7, 24, [1, 2, 5, 7], psi_table),
        "32": solve_even_lll_family(8, 32, [1, 2, 5, 7, 8], psi_table),
    }
    DATA_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(DATA_PATH, "w", encoding="utf-8") as f:
        json.dump(families, f, indent=2)
        f.write("\n")
    for gs, info in families.items():
        mc = max(abs(v) for v in info["bA_coeffs"])
        print(
            f"Computed g={gs} (N={info['N']}, L={info['L']}): "
            f"max |coeff| = {mc:,}, q_0 = {info['q0']:,}"
        )
    print(f"Wrote {DATA_PATH}")


if __name__ == "__main__":
    main()
