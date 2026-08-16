# The Hamiltonian of the quantized growth law (built 2026-08-15)

## Construction

Gudder (1409.3770 §3) builds, per binary parent, the double-down
unitary V₂ = [[c⁰,c¹],[c¹,c⁰]] and defines the Hamiltonian K by
V = e^{iK}; the energies are the coupling phases (his Lemma 3.2:
eigenvalues 1 and e^{2iθ}).  His construction requires binary
branching (the circulant is unitary automatically only at k = 2).

Generalization to the full downset tree.  Spectrally, Gudder's
V₂ = P_coh + e^{2iθ}P_⊥, where P_coh projects on the coherent
(uniform) direction and e^{2iθ} is the phase of the amplitude
column's non-coherent component.  On the full tree the canonical,
ordering-free, class-symmetric completion is the PHASE-DIAGONAL
unitary in the child basis:

    V_p |D⟩ = e^{iφ·gap(D)} |D⟩,        H_p = φ · Ĝ_p,

Ĝ = the gap (action-increment) operator, diagonal on children.
Justification:
  (a) it is canonical — gap values are intrinsic to the causal
      structure (no child ordering needed), and V commutes with all
      within-class permutations (the law's symmetry);
  (b) it generates the amplitude phases: the step isometry
      factorizes as U = V · U₊ with U₊ the nonnegative-amplitude
      (classical spreading) column — evolution = phase clock ×
      magnitude flow;
  (c) at binary nodes it reproduces Gudder's spectrum up to a
      constant shift: root gaps ±1 give levels ±π/4 (spacing π/2),
      his give {0, 2θ} = {0, π/2} at θ = π/4 — same spacings, and
      energies are defined modulo an additive constant;
  (d) physically it is the de Broglie/Feynman reading: with Δt = 1
      per growth step, the phase advance per step is φ·gap, so
      energy ≡ φ·gap.

## Immediate structural consequences (all inherited from §§23–26)

  - ENERGY QUANTIZATION: E ∈ (π/4)·ℤ; as a clock (mod 2π) there
    are exactly EIGHT levels: e^{iH} has order 8 (`octant_period`).
  - WIDTH IS ENERGY: gap = 1 − width + interior (`gap_splits_width`)
    ⟹ each unit of causal in-degree lowers the level by one octant.
    The expansion law reads: widening costs energy octants, and the
    Born rule only pays in full circles.
  - The coherent mode is the zero-mode analogue: the two
    conservation laws are the statements ⟨w|e^{iH/φ·(...)}|x⟩-type
    moment constraints of §26 — feasibility = octant coverage of
    the SPECTRUM of H_p.  A parent is growable iff its Hamiltonian
    spectrum covers the octants adequately: DYNAMICS EXISTS IFF THE
    ENERGY SPECTRUM IS RICH ENOUGH.  (New reading of the walls.)

## Observables computed (hamiltonian_spectrum.py, registered)

  1. DENSITY OF STATES: Born-weighted occupation O_n(k) of the 8
     levels k = gap mod 8, per depth n — does the level occupation
     converge (a stationary spectral state of the universe)?
  2. VACUUM: the maximally-occupied level and its drift.
  3. BAND STRUCTURE: distribution of raw gap values (unfolded E).
  4. WIDTH–LEVEL correlation: joint (gap mod 8, width) — the meter
     seen spectrally.
READINGS: (i) occupations converge to a nontrivial stationary
profile (the law has an equilibrium spectral state; report it);
(ii) occupations drift/concentrate on one level (spectral
freeze-out); (iii) neither stabilizes by n≈18 (report trend).

## RESULTS (same day, n=22 run + invariance tests)

1. SPECTRUM SETTLES (reading i, strengthened): occupations at n=21
   converge to (0.279, 0.219, 0.217, 0.285) on levels (1,3,5,7) -
   the E <-> -E conjugation symmetry becomes exact within errors:
   asymptotic profile ~ (0.28, 0.22 | 0.22, 0.28).  Mean energy
   STOPS drifting: <E> fluctuates around +1.1 octants (n=16..21)
   - a finite positive stationary energy rate, not growth.
2. FULL ACTION INVARIANCE (stronger than telescoping): 40 random
   linear extensions of a grown causet all give the SAME raw
   integer action (29), not merely the same value mod 8.  Reason,
   then verified: at insertion of e, the count k_y equals the size
   of the interval (y,e) in the FINAL causet - order-independent -
   so the cumulative action has the closed form
       A(C) = (n-1) - 2*N0 + 4*N1 - 2*N2
   (N_k = k-element interval abundances), checked EXACTLY on 30
   causets.  This is the Benincasa-Dowker 2D discrete
   Einstein-Hilbert functional form - BY CONSTRUCTION (the W2 gap
   weights (2,-4,2) are the BD coefficients); the new content is
   the verified exact telescoping and the closed form.
3. PROBE B CORRECTED: the earlier "action is historical" reading
   (iii) is RETRACTED - the action is a geometric functional after
   all; the regression failed because the right invariants are the
   INTERVAL ABUNDANCES N0, N1, N2, not the six coarse ones tested.
4. THE UPGRADE: H = phi x (BD-action increment).  The phase clock
   ticks at the discrete Einstein-Hilbert rate: ENERGY = CURVATURE.
   The quadrature levels are curvature quanta; the stationary
   occupation is a curvature-quantum distribution; <E> ~ +1.1
   octants is a positive stationary mean curvature rate (a
   discrete cosmological-constant-flavored observable); and the
   width-energy meter reads: WIDENING SPACE COSTS CURVATURE QUANTA,
   which is what the Born rule rations (the expansion law).
