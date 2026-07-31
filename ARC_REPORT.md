# The full arc, intact — findings, caveats, program state

This file restates, without truncation, the material previously
delivered only in chat.  Companion files: DEFINITIONS.md,
PAPER1_DICHOTOMY.md, PAPER2_LANDSCAPE.md, PAPER3_SELECTION.md,
VR_GATE_REPORT.md, QUANTUM_GATE_REPORT.md, PI4_CERTIFICATE.md.

## Chronology of results (tags in the repository)

1. Commensurability check; lazy tower; root determinism
   (commensurability-era commits).
2. Classical gate vs Varadarajan–Rideout: deterministic brooms only
   (vr-gate-2026-07-30).
3. Two-child induction promoted to Lean; n ≤ 6 census; neutral-
   extension theorem; OEIS-novel sequence 1, 2, 6, 22, 105, 634
   (twochild-lean-2026-07-30, seam-sewn-2026-07-30).
4. Quantum factored gate at b = 9: quantum broom only; collision table
   (quantum-gate-2026-07-30); era-seed sweep closes the boundary caveat
   and the collision integers become Lean theorems
   (collision-lean-2026-07-30).
5. Non-factored gate: wave equation; downward closure; 4D mod-9 null
   web (door-closed-2026-07-31).
6. 2D collision table; parity theorem; dimensional inversion
   (collision-2d-2026-07-31); 2D wave gate passes maximally; π/4
   anomaly (wave2d-pass-2026-07-31); depth-7 persistence + parity in
   Lean (depth7-parity-2026-07-31).
7. Selection gates: Bell dead both forms; π/4 death rigorous
   (bell-dead-2026-07-31); cluster dead in all three forms with the
   orbit-form exact certificate (cluster-gate-2026-07-31,
   cluster-dead-2026-07-31).
8. Continuum selection: manifold confinement exactly free
   (continuum-select-2026-07-31); depth-8: no reach-back ever;
   landscape confirmed (depth8-2026-07-31).
9. Self-similarity gate; couplings-must-age theorem; Minkowski
   steering (selfsim-2026-08-01); positivity-exact ranges and the
   exclusion (this commit).

## The caveat list (complete)

- All computations are at depth n ≤ 8 (n ≤ 7 for the selection
  polytopes); every "always"/"never" is scoped to checked depth unless
  tagged [LEAN].
- The results characterize the literal ansatz class (transition
  amplitudes ρ·e^{iΔS/ℏ}, ρ ≥ 0, Markov sum rule): a different phase
  assignment or complex-modulus generalization is a different theory.
- Amplitude-level covariance is imposed; measure-level covariance is
  strictly weaker and unexplored except where noted.
- ψ²/|Ψ|² statistics are pre-decoherence proxies, not the physical
  measure; no decoherence functional of the self-similar member has
  been computed yet.
- "Manifoldlike" at these sizes means order dimension ≤ 2; it is a
  compatibility criterion, not a geometry test.
- One-step self-similarity is a finite-n proxy for an asymptotic RG
  property; exact semigroup invariance is infeasible at this depth and
  the gap is a finite-size statement.
- Phases: generic-phase results were verified at several rational and
  irrational values; only π/4 (2D) is proven dead among nondegenerate
  phases; a continuous-φ theorem is open.
- The labeled-vs-orbit counting convention (whether birth order is
  physical) is an unresolved axiom; every kill mechanism runs through
  multiplicities, so results could shift under a different convention —
  where both conventions were tested (cluster), both died.
- LP/rank computations are float-based (HiGHS/numpy); certificates
  extracted by hand are exact; Lean theorems are kernel-checked.
- The withdrawn interim pinning 0.32–0.35 (penalty-era) is superseded
  by the LP interval [0.2533, 0.4639]; the repository history preserves
  the correction sequence.

## Program state

Formal: 18 axiom-clean Lean theorems in
KFCausalSetActionNeutralExtension.lean plus the quantum-measure file;
root build green throughout (8749 jobs).  Mechanical: every gate is a
committed exit-0 script with validated enumeration (A000112 through
16999).  Certificates: seven hand-checkable (chain-tower gcd; parity
obstruction; π/4 multiplicity; collision integers; Λ-in-N cascade;
stationarity two-phasor; L-equation 2 = 1).  New combinatorial objects:
the neutral-extension census (OEIS-novel), the collision table, the
null web, the aging theorem, the exclusion interval.  Papers: three
drafts in repository.  Data-facing thread: epoch-dependent couplings ↔
everpresent-Λ phenomenology (the program's earlier DESI bounds).

## Open problems, ordered by leverage

1. Depth growth of the self-similar sup r (the falsification target).
2. The ψ²-weighted supremum over the self-similar polytope (weighting-
   independence of the exclusion).
3. Decoherence functional of a self-similar member; which events
   decohere; the physical measure's r.
4. The 2-order-closure conjecture (would make Paper 2's confinement
   exact at all n).
5. The counting-convention axiom (a symmetrization postulate for
   histories).
6. Menu-comparison master lemma in Lean (compresses five kills to one).
7. The ℏ-window theorem for general integer-spectrum covariant
   theories.
8. The aging–Λ bridge: derive everpresent-Λ statistics from forced
   epoch dependence.
