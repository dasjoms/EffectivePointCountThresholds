# Effective Point-Count Thresholds and Polynomial Zeta-Recovery Bounds for Abelian Varieties over Finite Fields

Note and ancillary computational scripts addressing questions in Section 7 of Shiva Chidambaram and Timo Keller, *Point counts of abelian varieties over finite fields determining their zeta function* ([arXiv:2606.28989v2](https://arxiv.org/abs/2606.28989)).

---

## Overview of Results

| Reference in `arXiv:2606.28989v2` | Result | Script / Data |
|---|---|---|
| **Question 7.8** ($g = 5, 6$) & **$g = 7$** | $N(5) = 4$ ($q \ge 10^5$), $N(6) = 4$ ($q \ge 10^6$), and $N(7) = 5$ (ordinary lower bound for $q \ge 5$; upper bound for $q \ge 10^6$) | `scripts/verify_sec2_small_g_bounds.py`, `scripts/verify_sec2_sec3_explicit_pairs.py` |
| **Remark 7.10** ($g = 8$) | $N(8) \ge 5$ via an explicit ordinary $\mathbf{Z}[q]$-family valid for all prime powers $q \ge 4$ | `scripts/verify_sec2_sec3_explicit_pairs.py` |
| **Genus $8$, $N = 5$ structure** | For $q \ge 10^8$, every collision has $P_B(T) - P_A(T) = m_4 T^4(T^4-1)(T^4-q^4)$ ($1 \le |m_4| \le 512$), with $a_2 = a_1 q + a_1^2$ and $a_1 \in \{-2,-1,0,1\}$ for large $q$; no $\mathbf{Z}[q]$-family of reciprocal $q$-Weil polynomials collides on $c_1,\dots,c_5$ | `scripts/verify_sec3_g8_N5_structure.py`, `scripts/verify_sec3_g8_N5_no_Zq_family.py` |
| **Question 7.9** (Higher genera) | $N(g) \ge \bigl(\frac{\pi}{\sqrt{6}} - o(1)\bigr)\sqrt{g}$ as $g \to \infty$, together with explicit ordinary $\mathbf{Z}[q]$-families giving $N(15) \ge 7$ ($q \ge 1{,}086{,}853$), $N(24) \ge 8$ ($q \ge 3{,}618{,}624{,}025$), and $N(32) \ge 9$ ($q \ge 11{,}921{,}384{,}751{,}788{,}836$) | `scripts/verify_sec4_chebyshev_asymptotics.py`, `data/higher_genus_families.json` |
| **Remark 7.12** (Theorem 1.1 threshold) | Polynomial threshold $Q(g) = (10g)^6 = 10^6 g^6$ in Theorem 1.1 for all $g \ge 2$ (recovering $f_A(T)$ via the algorithm of Chidambaram and Keller without modification) | `scripts/verify_sec5_polynomial_Qg.py` |

Remaining open questions include determining the exact value of $N(8) \in \{5, 6, 7, 8\}$ for sporadic prime powers beyond $\mathbf{Z}[q]$-families, and narrowing the asymptotic gap between $\Omega(\sqrt{g})$ and $g$.

---

## Running the Computational Checks

### Requirements
- **Python $\ge 3.10$** with `sympy` (`pip install -r requirements.txt`)
- A **C99 compiler** (`cc`, `gcc`, or `clang`) on `PATH` (used by `scripts/verify_sec3_g8_N5_no_Zq_family.py` to compile `scripts/check_g8_Zq_modp.c`)

```bash
python3 verify_all.py
```

---

## Files

```text
.
├── README.md                                  # Overview and usage instructions
├── effective_point_count_thresholds.tex       # AMS-LaTeX manuscript
├── effective_point_count_thresholds.pdf       # Compiled PDF manuscript
├── effective_point_count_thresholds.md        # Markdown version of the manuscript
├── requirements.txt                           # Python dependencies (`sympy>=1.12`)
├── verify_all.py                              # Runs the six computational scripts (~50s)
├── data/
│   └── higher_genus_families.json             # Z[q][X] coefficients and rational nodes (g = 15, 24, 32)
└── scripts/
    ├── verify_sec2_small_g_bounds.py          # Section 2 resultant identities and dominance bounds (g = 5, 6, 7)
    ├── verify_sec2_sec3_explicit_pairs.py     # Explicit ordinary Z[q]-families for g = 7 (q >= 5) and g = 8 (q >= 4)
    ├── verify_sec3_g8_N5_structure.py         # Prop. 3.2(1): g = 8, N = 5 elimination (q >= 10^8) and Cauchy-Schwarz
    ├── verify_sec3_g8_N5_no_Zq_family.py      # Prop. 3.2(2): resultant reduction and C99 modular search
    ├── check_g8_Zq_modp.c                     # C99 modular search over F_p (p = 7, 11, 13; --regenerate to rewrite)
    ├── verify_sec4_chebyshev_asymptotics.py   # Section 4 Chebyshev-totient checks (N <= 5) and g = 15, 24, 32 data
    ├── verify_sec5_polynomial_Qg.py           # Section 5 generating-function identities (g <= 4) and constant bounds
    └── generate_higher_genus_families.py      # Optional HNF + LLL script to recompute data/higher_genus_families.json
```

### Recomputing Optional Derived Files

- **Modular C99 source (`scripts/check_g8_Zq_modp.c`)**: `scripts/verify_sec3_g8_N5_no_Zq_family.py` derives the reduced polynomial tables symbolically and compares them with `scripts/check_g8_Zq_modp.c`; pass `--regenerate` to rewrite the C file.
- **Higher-genus polynomial data (`data/higher_genus_families.json`)**: `scripts/verify_sec4_chebyshev_asymptotics.py` checks the saved polynomials using `sympy`. To recompute them via Hermite normal form and LLL reduction:
  ```bash
  pip install python-flint numpy
  python3 scripts/generate_higher_genus_families.py
  ```
