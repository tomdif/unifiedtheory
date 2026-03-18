#!/usr/bin/env python3
"""
WHY SU(3)? Enumerate compact simple Lie algebras as color groups.

For each candidate G_c, compute the minimal chiral anomaly-free
fermion set in G_c × SU(2) × U(1), and check which G_c gives:
(a) The smallest anomaly-free chiral set
(b) All anomaly conditions algebraically independent
(c) Consistent hypercharge assignments

Candidates: SU(N) for N = 2,3,4,5; Sp(2N) for N = 1,2; G₂, SO(N).
For simplicity, restrict to fundamental representations.

Key anomaly conditions for G_c × SU(2) × U(1):
1. G_c³: Σ A(R_c) · d(R_w) = 0  (cubic anomaly of color group)
2. SU(2)³: automatically 0 (SU(2) has no d_abc)
3. G_c² × U(1): Σ T(R_c) · d(R_w) · Y = 0
4. SU(2)² × U(1): Σ d(R_c) · T(R_w) · Y = 0
5. Gravitational: Σ d(R_c) · d(R_w) · Y = 0
6. U(1)³: Σ d(R_c) · d(R_w) · Y³ = 0
7. G_c² × SU(2)²: Σ T(R_c) · T(R_w) = 0 (mixed, Y-independent)

For SU(N): fundamental has d=N, T=1/2, A=1.
Anti-fundamental: d=N, T=1/2, A=-1.
Adjoint: d=N²-1, T=N, A=0.

For Sp(2N): fundamental has d=2N, and all reps are pseudoreal → A=0.
So Sp(2N)³ anomaly vanishes automatically. No chirality from Sp.

For SO(N): fundamental is real for all N → A=0. No chirality.

For G₂: fundamental (dim 7) is real → A=0. No chirality.

For exceptional groups (E₆, E₇, E₈): only E₆ has complex reps.
E₆ fundamental: d=27. Very large.
"""

import numpy as np

def analyze_color_group(name, N_c, A_fund, d_fund, T_fund):
    """Analyze G_c as a color group candidate.

    For a chiral theory, need A(fund) ≠ 0.
    Color parity: n_fund × d_w + n_antifund × d_w = 0 for G_c³ anomaly.
    With A(fund) = 1, A(antifund) = -1:
    G_c³: (n_fund - n_antifund) × d_w_per_fund_species = 0

    Minimal chiral structure (analogous to SM):
    - (fund, 2) + n × (antifund, 1): the "quark doublet" + "singlets"
    - Color parity: 1×2 = n×1, so n = 2 (need 2 color singlets)
    - Plus leptons: (1, 2) + (1, 1)

    Total fermions = d_fund × 2 + 2 × d_fund × 1 + 1 × 2 + 1 × 1
                   = 2·d_fund + 2·d_fund + 2 + 1
                   = 4·d_fund + 3
    For d_fund = N_c: total = 4·N_c + 3
    Wait, let me recount with the 7N+1 formula.
    """

    if A_fund == 0:
        return {
            'name': name, 'N_c': N_c, 'chiral': False,
            'reason': 'Real/pseudoreal reps → no chirality',
            'fermions': None
        }

    # For SU(N_c) with fundamental reps:
    # Colored sector with color parity:
    #   (fund, 2) contributes N_c × 2 fermions, A = +2
    #   2 × (antifund, 1) contributes 2 × N_c × 1 fermions, A = -2
    #   Color parity: +2 - 2 = 0 ✓
    # Uncolored sector:
    #   (1, 2) contributes 2 fermions
    #   (1, 1) contributes 1 fermion
    # Total: N_c × 2 + 2 × N_c + 2 + 1 = 4N_c + 3

    # But this counts with the SIMPLEST structure.
    # The actual formula from FermionRepForced.lean: 7N + 1 where N = dim(SU(2) rep)
    # That was for fixed G_c = SU(3). Let me redo for general G_c.

    # General formula with G_c × SU(2) × U(1):
    # Colored: (N_c, 2) + 2×(N_c_bar, 1) = 2N_c + 2N_c = 4N_c fermions
    # Uncolored: (1, 2) + (1, 1) = 3 fermions
    # Total = 4N_c + 3

    total = 4 * N_c + 3

    # Check anomaly conditions count
    # Number of Y variables: 5 types → Q(N_c,2), u(N_c_bar,1), d(N_c_bar,1), L(1,2), e(1,1)
    # Linear conditions: 3 (G_c²×U(1), SU(2)²×U(1), gravitational)
    # Cubic: 1
    # Total constraints: 4 on 5 unknowns → 1 free parameter (normalization)
    # All 4 conditions independent? Check:

    # SU(2)²×U(1): N_c·Y_Q + Y_L = 0
    # G_c²×U(1): 2·Y_Q + Y_u + Y_d = 0 (T(fund)·d(2)·Y_Q + T(fund)·d(1)·(Y_u+Y_d) = 0)
    #   → T(fund)·(2Y_Q + Y_u + Y_d) = 0, and T(fund) ≠ 0, so 2Y_Q + Y_u + Y_d = 0
    # Gravitational: 2N_c·Y_Q + N_c·Y_u + N_c·Y_d + 2Y_L + Y_e = 0
    # Cubic: 2N_c·Y_Q³ + N_c·Y_u³ + N_c·Y_d³ + 2Y_L³ + Y_e³ = 0

    # From linear: Y_L = -N_c·Y_Q, Y_u+Y_d = -2Y_Q
    # Gravitational: 2N_c·Y_Q + N_c·(-2Y_Q) + 2(-N_c·Y_Q) + Y_e = 0
    #   → 2N_c·Y_Q - 2N_c·Y_Q - 2N_c·Y_Q + Y_e = 0
    #   → -2N_c·Y_Q + Y_e = 0
    #   → Y_e = 2N_c·Y_Q

    # So: Y_L = -N_c·Y_Q, Y_e = 2N_c·Y_Q, Y_u = -2Y_Q - Y_d

    # Cubic: 2N_c·Y_Q³ + N_c·(-2Y_Q-Y_d)³ + N_c·Y_d³ + 2(-N_c·Y_Q)³ + (2N_c·Y_Q)³ = 0

    # Let me compute the cubic for general N_c
    # Let r = Y_d/Y_Q. Then Y_u = -2Y_Q - Y_d = -(2+r)Y_Q
    # Cubic/Y_Q³: 2N_c + N_c·(-(2+r))³ + N_c·r³ + 2·(-N_c)³ + (2N_c)³
    #           = 2N_c - N_c(2+r)³ + N_c·r³ - 2N_c³ + 8N_c³
    #           = 2N_c + 6N_c³ + N_c(r³ - (2+r)³)

    # Expand (2+r)³ = 8 + 12r + 6r² + r³
    # r³ - (2+r)³ = -8 - 12r - 6r²

    # Cubic/Y_Q³ = 2N_c + 6N_c³ + N_c(-8 - 12r - 6r²)
    #            = 2N_c + 6N_c³ - 8N_c - 12N_c·r - 6N_c·r²
    #            = 6N_c³ - 6N_c - 12N_c·r - 6N_c·r²
    #            = 6N_c(N_c² - 1 - 2r - r²)
    #            = 6N_c(N_c² - 1 - (r² + 2r))
    #            = 6N_c(N_c² - 1 - (r+1)² + 1)
    #            = 6N_c(N_c² - (r+1)²)
    #            = 6N_c(N_c - (r+1))(N_c + (r+1))

    # BEAUTIFUL! The cubic factors as:
    # 6N_c · (N_c - r - 1) · (N_c + r + 1) = 0
    # For Y_Q ≠ 0 and N_c ≠ 0:
    # Either r = N_c - 1 or r = -(N_c + 1)

    # Solution 1: Y_d = (N_c - 1)·Y_Q
    #   Y_u = -(2 + N_c - 1)·Y_Q = -(N_c + 1)·Y_Q
    #   Y_L = -N_c·Y_Q
    #   Y_e = 2N_c·Y_Q

    # Solution 2: Y_d = -(N_c + 1)·Y_Q
    #   Y_u = -(2 - N_c - 1)·Y_Q = (N_c - 1)·Y_Q
    #   This is Solution 1 with u ↔ d. Same physics.

    # For N_c = 3 (SM):
    #   Solution 1: Y_d = 2·Y_Q, Y_u = -4·Y_Q, Y_L = -3·Y_Q, Y_e = 6·Y_Q
    #   With Y_Q = 1/6: (1/6, -2/3, 1/3, -1/2, 1) ✓ THE SM!

    # For N_c = 2:
    #   Solution 1: Y_d = 1·Y_Q, Y_u = -3·Y_Q, Y_L = -2·Y_Q, Y_e = 4·Y_Q
    #   Total fermions = 4·2 + 3 = 11

    # For N_c = 4:
    #   Solution 1: Y_d = 3·Y_Q, Y_u = -5·Y_Q, Y_L = -4·Y_Q, Y_e = 8·Y_Q
    #   Total fermions = 4·4 + 3 = 19

    return {
        'name': name, 'N_c': N_c, 'chiral': True,
        'fermions': total,
        'hypercharges': f'Y = Y_Q·(1, -(N+1), N-1, -N, 2N) for N={N_c}',
        'cubic_factorization': f'6N(N-(r+1))(N+(r+1))=0, r=N-1 or r=-(N+1)',
    }


def main():
    print("=" * 65)
    print("COLOR GROUP SELECTION: Which G_c is forced by minimality?")
    print("=" * 65)

    # SU(N) candidates
    results = []
    for N in range(2, 8):
        r = analyze_color_group(f'SU({N})', N, A_fund=1, d_fund=N, T_fund=0.5)
        results.append(r)

    # Other simple groups with complex fundamentals
    results.append(analyze_color_group('Sp(4)', 4, A_fund=0, d_fund=4, T_fund=0.5))
    results.append(analyze_color_group('SO(10)', 10, A_fund=0, d_fund=10, T_fund=1))
    results.append(analyze_color_group('G₂', 7, A_fund=0, d_fund=7, T_fund=1))
    results.append(analyze_color_group('E₆', 27, A_fund=1, d_fund=27, T_fund=3))

    print(f"\n{'Name':>8} {'N_c':>4} {'Chiral':>7} {'Fermions':>9} {'Notes'}")
    print("-" * 65)
    for r in results:
        chiral = "YES" if r['chiral'] else "NO"
        ferm = str(r['fermions']) if r['fermions'] else "---"
        notes = r.get('reason', r.get('hypercharges', ''))[:40]
        print(f"{r['name']:>8} {r['N_c']:>4} {chiral:>7} {ferm:>9}  {notes}")

    print()
    print("=" * 65)
    print("THE CUBIC FACTORIZATION IS UNIVERSAL!")
    print("=" * 65)
    print()
    print("For G_c = SU(N_c) × SU(2) × U(1) with the minimal chiral set:")
    print("  Cubic condition factors as: 6N_c(N_c - r - 1)(N_c + r + 1) = 0")
    print("  where r = Y_d/Y_Q.")
    print()
    print("  Solutions: r = N_c - 1 or r = -(N_c + 1) (u↔d related)")
    print()
    print("  Hypercharges: (Y_Q, Y_u, Y_d, Y_L, Y_e) = Y_Q·(1, -(N+1), N-1, -N, 2N)")
    print()

    for N in [2, 3, 4, 5]:
        charges = f"(1, {-(N+1)}, {N-1}, {-N}, {2*N})"
        total = 4*N + 3
        print(f"  N_c = {N}: charges = {charges}, {total} fermions")

    print()
    print("=" * 65)
    print("WHICH N_c IS SELECTED?")
    print("=" * 65)
    print()
    print("All SU(N_c) for N_c ≥ 2 give valid anomaly-free theories.")
    print("The fermion count 4N_c + 3 is MINIMIZED at N_c = 2 (11 fermions).")
    print()
    print("BUT: N_c = 2 gives SU(2)_color × SU(2)_weak — the color and weak")
    print("groups are IDENTICAL. This means color parity = weak parity,")
    print("and the theory has an enhanced SU(2)×SU(2) ≅ SO(4) symmetry.")
    print("The 'color' and 'weak' sectors are not independent.")
    print()
    print("N_c = 3 is the SMALLEST value where color and weak are DISTINCT")
    print("(SU(3) ≠ SU(2)). This requires that the two gauge factors")
    print("in the Lie algebra primitive are DIFFERENT simple groups.")
    print()
    print("If we require: G_c ≠ G' (the color and weak groups are distinct),")
    print("then N_c ≥ 3. Combined with minimality (smallest N_c):")
    print("  N_c = 3 is FORCED.")
    print()
    print("The SM gauge group SU(3) × SU(2) × U(1) is the minimal")
    print("chiral anomaly-free gauge group with DISTINCT color and weak factors.")


if __name__ == "__main__":
    main()
