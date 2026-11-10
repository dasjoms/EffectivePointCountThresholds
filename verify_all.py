#!/usr/bin/env python3
"""
Runs the ancillary computational checks for
"Effective Point-Count Thresholds and Polynomial Zeta-Recovery Bounds
for Abelian Varieties over Finite Fields"
(on Section 7 of Chidambaram and Keller, arXiv:2606.28989v2).

Scripts executed:
  1. verify_sec2_small_g_bounds.py        — Section 2 resultant identities and dominance bounds (g = 5, 6, 7)
  2. verify_sec2_sec3_explicit_pairs.py   — Explicit ordinary Z[q]-families for g = 7 (q >= 5) and g = 8 (q >= 4)
  3. verify_sec3_g8_N5_structure.py       — Proposition 3.2(1): g = 8, N = 5 elimination (q >= 10^8) and Cauchy-Schwarz
  4. verify_sec3_g8_N5_no_Zq_family.py    — Proposition 3.2(2): g = 8, N = 5 Z[q]-family modular search (mod 7, 11, 13)
  5. verify_sec4_chebyshev_asymptotics.py — Section 4 Chebyshev-totient checks (N <= 5) and data for g = 15, 24, 32
  6. verify_sec5_polynomial_Qg.py         — Section 5 symbolic identities (g <= 4) and rational constant bounds

Requirements: Python >= 3.10, `sympy`, and a C99 compiler (`cc` / `gcc` / `clang`).
"""

from pathlib import Path
import subprocess
import sys
import time

ROOT_DIR = Path(__file__).resolve().parent
SCRIPTS_DIR = ROOT_DIR / "scripts"

SCRIPTS = [
    ("Section 2 upper bounds (g = 5, 6, 7)", "verify_sec2_small_g_bounds.py"),
    ("Sections 2 & 3 explicit pairs (g = 7, 8)", "verify_sec2_sec3_explicit_pairs.py"),
    ("Proposition 3.2(1) structure (g = 8, N = 5)", "verify_sec3_g8_N5_structure.py"),
    ("Proposition 3.2(2) modular search (g = 8, N = 5)", "verify_sec3_g8_N5_no_Zq_family.py"),
    ("Section 4 Chebyshev families and g = 15, 24, 32 data", "verify_sec4_chebyshev_asymptotics.py"),
    ("Section 5 algebraic identities and constant bounds", "verify_sec5_polynomial_Qg.py"),
]


def main():
    print("=" * 78)
    print("Running computational checks (arXiv:2606.28989v2, Section 7)")
    print("=" * 78, flush=True)
    t_start = time.monotonic()
    timings = []

    for label, script_name in SCRIPTS:
        script_path = SCRIPTS_DIR / script_name
        print(f"\n>>> {script_name} [{label}]", flush=True)
        t0 = time.monotonic()
        proc = subprocess.run([sys.executable, "-B", "-u", str(script_path)], cwd=str(ROOT_DIR))
        dt = time.monotonic() - t0
        if proc.returncode != 0:
            print(f"\nFAILED: {script_name} exited with code {proc.returncode} after {dt:.2f}s.")
            sys.exit(proc.returncode)
        timings.append((script_name, dt))

    total_dt = time.monotonic() - t_start
    print("\n" + "=" * 78)
    print("All 6 scripts completed.")
    print("-" * 78)
    for script_name, dt in timings:
        print(f"  [OK] {script_name:<48s} ({dt:5.2f}s)")
    print("-" * 78)
    print(f"  Total runtime: {total_dt:.2f}s")
    print("=" * 78)


if __name__ == "__main__":
    main()
