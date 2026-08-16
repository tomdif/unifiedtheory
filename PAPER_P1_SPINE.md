# P1 — Quantum mechanics from a monotone probability, lossless time,
# gauge, and one interference event (machine-checked)

Status: SPINE (2026-08-15).  Every numbered result is a compiled
axiom-clean Lean theorem in `KFCausalUniquenessLeg.lean` (58
theorems total; axioms = propext / Classical.choice / Quot.sound).
This document fixes the paper's skeleton, the theorem-to-section
map, and the claims at their earned tier.  Prose is to be expanded;
mathematics is done.

## Abstract (draft)

We prove a reconstruction of quantum mechanics whose hypotheses
contain no Hilbert space, no amplitudes, no power law, no linearity,
no complex structure, and no continuity.  From (i) a monotone notion
of probability, (ii) a dynamics that is a bare surjective map of
states preserving total measure and pairwise distinguishability and
commuting with a global phase, and (iii) a single lossless
interference event with a tunable phase, we derive that the measure
is the Born rule f(x) = x² and the dynamics is unitary.  The measure
function, linearity, complex structure, and unitarity are all
conclusions.  The central mechanism is new: a complex-phase probe of
one interference event sweeps the measured quantity over a continuous
interval at fixed input, and overlapping intervals chain to force
Pythagorean additivity with no regularity assumption.  The entire
development is machine-checked in Lean 4.

## 1. Introduction

- The reconstruction program (Hardy; CDP; Masanes–Müller; Barnum;
  Wilce): axioms → QM.  Position of this work: the WEAKEST measured
  input we know of — monotone order, not a norm; a set-map, not a
  linear operator — plus ONE interference event.
- Novelty flags to defend (prior-art sweep, §7): the phase-continuum
  additivity mechanism; monotone-only (no continuity/convexity)
  throughout; the "one event" economy; full formalization.
- Honest antecedent: the p=2-among-ℓᵖ folklore (Aaronson, "Island
  in Theoryspace"; Lamperti isometry theory) — we generalize it out
  of the power family entirely and machine-check it.
- REQUIRED ATTRIBUTION (2026-08-15 deep-read, PRIOR_ART_GUDDER.md):
  the double-conservation pair (coherent + Born per branching) is
  Gudder's "unitary transition amplitude" (arXiv:1409.3770, 2014),
  stated on binary c-causets where it is always satisfiable with a
  free phase continuum; our π/4 root solution is the SYMMETRIC
  POINT of his Theorem 2.1 continuum, selected by the action-phase
  ansatz.  The program's novel core relative to Gudder: the
  selection principle, the feasibility geometry on the full downset
  tree (walls, expansion law, octant meter), the uniqueness leg,
  and the falsifiable λ-observable.  P2/P3 must lead with this.

## 2. Setup and the four physical postulates

  P1 MONOTONE PROBABILITY.  A measure Σᵢ f(‖xᵢ‖), f: [0,∞)→[0,∞)
     nondecreasing, f(0)=0, f not identically 0.  [monotone, that's
     all — no power law, no continuity, no convexity]
  P2 LOSSLESS TIME.  The step F is a surjection of state space
     preserving the total measure and the pairwise measure-distance.
  P3 GAUGE.  F commutes with the global quarter-turn phase.
  P4 ONE INTERFERENCE EVENT.  A lossless step S acting on two
     coordinates as a rotation-form gate with a tunable input phase.

## 3. The phase-continuum additivity mechanism (the engine)

- Lemma (`phase_interval_additivity`, §23): probing one block with
  s·e₁ + t·e^{iψ}·e₂ fixes the input measure and sweeps the output
  argument over [(cs−σt)², (cs+σt)²]; overlapping level intervals
  chain (explicit finite ladder, step μ*=4PQ/(P+Q)²) → g additive.
  No continuity, monotonicity, or density used.
- Master form (`master_chaining`, §25): two functions tied by the
  exchange are forced equal and linear (increment law + x=0 probe).

## 4. The Born rule

- Theorem (`complex_mixing_block_forces_born`, §23): any monotone
  measure lossless under ONE rotation-form mixing block (any angle,
  unnormalized) is exactly f(x)=x²f(1).  Supersedes the four earlier
  partial routes (§§18–21: balanced FE; dense-splitter rigidity with
  derived continuity; irrational-orbit density, formalized; exchange-
  transport continuity) — retained as independent real-probe results.
- Corollary (`master_chaining`): HOMOGENIZATION — one interference
  event forces two sectors onto the SAME measure function (not just
  exponent).  Physics hook: BMV-type gravitational interference would
  force gravity into matter's Born calculus; measure-dualism dies.

## 5. Linearity, complex structure, unitarity — all derived

- Once f=x² is known the measure is ℓ², a genuine metric.
- `lossless_bijection_is_real_linear` (§14, Mazur–Ulam): the set-map
  is real-linear — RETROACTIVELY, from the derived metric.
- `phase_covariant_real_linear_is_complex_linear` (§17): gauge
  upgrades to ℂ-linear.
- `l2_lossless_columns_orthogonal` (§9): orthonormal columns.

## 6. The terminal theorem

- `quantum_mechanics_from_a_beam_splitter` (§24): P1–P4 ⟹ Born rule
  (f=x²f(1), f(1)>0) AND unitary dynamics.  One statement; the whole
  chain internal; everything the textbook assumes is a conclusion.
- Slogan: *A monotone notion of probability, lossless time, gauge,
  and one interference event are quantum mechanics.*

## 7. Scope, prior art, and what is NOT claimed

- NOT claimed: that these postulates are the unique route; that the
  causal-set origin is required (P1–P4 are substrate-free).
- Registered open (paper-proved, formalization pending): general
  two-overlap columns (Born-or-trivial without rotation form);
  ≥3-overlap; any-angle stability constant.
- Prior-art sweep: reconstruction literature (as above);
  Lamperti/Orlicz isometry theory (we exit the power family);
  Gleason/Busch (we do not assume frames or POVMs); Wigner (gauge
  replaces the antiunitary dichotomy — see the divisible-time /
  half-step route §11–13 for the alternate assembly).

## 8. Formalization

- Lean 4 + Mathlib v4.28; 58 theorems; axiom-clean; per-theorem
  `#print axioms`.  Companion repo `bi-normalized-causal-growth`
  (self-contained, Mathlib-only).
- Two independent assembly routes to unitarity: (A) the beam-splitter
  terminal theorem (§24, this paper's spine); (B) the divisible-time
  route (§11–17: no interference axiom at all — time-divisibility +
  gauge + change).  Report both; (A) has the weaker interference
  input, (B) has no interference input.

## Theorem → section map (all compiled)

  phase_interval_additivity ........... engine, §3
  master_chaining ..................... homogenization, §3/§4
  complex_mixing_block_forces_born .... Born, §4
  lossless_bijection_is_real_linear ... linearity, §5
  phase_covariant_..._complex_linear .. complex structure, §5
  l2_lossless_columns_orthogonal ...... unitarity, §5
  quantum_mechanics_from_a_beam_splitter  terminal, §6
  change_and_divisibility_force_born .. route B, §8
  quantum_mechanics_from_time_alone ... route B full, §8

## Figures (planned)

  F1  the phase-probe interval sweep (fixed input, moving output).
  F2  the interval-chaining ladder across a level.
  F3  the assembly DAG: postulates → Born → metric → linear → unitary.
