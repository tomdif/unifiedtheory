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
