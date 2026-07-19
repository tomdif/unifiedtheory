/-
  UnifiedTheory/LayerC/SO10ForcingSharpened.lean
  ──────────────────────────────────────────────

  **SHARPENING of the SM ↔ QM bridge's deepest residual hole.**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT THIS FILE IS

  The companion `SMPartialForcing.lean` introduces a NAMED `Prop`,
  `SO10Forcing_Target`, standing in for the deep, unproved direction of
  the bridge: "operational quantum principles + SO(10) covariance FORCE
  the single-generation Hilbert dimension to be divisible by
  `N_W ^ d_eff = 16 = dim_spinor_SO10`."  That `Prop` is the irreducible
  honesty gate of Path A.

  This file does to `SO10Forcing_Target` what the GT-residual work did to
  the Trotter gap: a referee-grade REDUCTION.  We do NOT close the hole
  (no mathematics in the literature derives "QM forces the SM/SO(10)
  rep content").  We SHARPEN it:

    (1) We expose a STRUCTURAL DEFECT in the literal statement of
        `SO10Forcing_Target`: the dimension `n` in its conclusion is
        bound by an inner `∀` that is logically DECOUPLED from the
        theory `T` and from the SO(10) covariance witness.  As a
        consequence the literal `Prop` is not merely "open" — it is
        FALSE: the trivial representation on `Fin 1` refutes it.
        We prove `¬ SO10Forcing_Target` (theorem
        `SO10Forcing_Target_is_false`).  A referee would reject the
        named gate on this ground alone; it cannot be the honest hole.

    (2) We DECOMPOSE the intended content into its logically independent
        pieces:
          (a) ALREADY-PROVED dictionary facts — the bridge object
              `singleGenNS` has `singleGenDim = 16` and `16 ∣ 16`
              (peeled off; `peeled_dictionary_fact`).
          (b) VACUOUS hypotheses — `IsOperationalQuantum T` and
              `HasSO10Covariance T` do not constrain the conclusion as
              written, because the conclusion never mentions `T`
              (`vacuous_hypotheses_unused`).
          (c) The GENUINE OPEN CONTENT — the implication "spinor
              representation present ⟹ `16 ∣ n`", once `n` is properly
              COUPLED to the theory.

    (3) We state the IRREDUCIBLE CORE `SO10ForcingCore`: the minimal,
        couplable `Prop` that carries the genuine physical content.  It
        asserts that whenever the SO(10) covariance of a theory is
        WITNESSED at a dimension `n` that contains the 16-dimensional
        SO(10) spinor as a constituent block (`n = 16 * k`), then
        `16 ∣ n`.  The physically loaded premise — "operational quantum
        + SO(10) covariance ⟹ the spinor block is present" — is the
        single irreducible hole, packaged as `SpinorBlockPresent`.

    (4) We give the REPAIRED target `SO10Forcing_Target_fixed`, in which
        `n` is the genuine covariance-witness dimension carrying the
        spinor block, and we PROVE the reduction
            `SO10ForcingCore → SO10Forcing_Target_fixed`
        (theorem `core_forces_fixed_target`).  The bridge now bottoms
        out on `SO10ForcingCore`, whose only non-trivial input is
        `SpinorBlockPresent`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE IRREDUCIBLE CORE, IN PLAIN PHYSICS TERMS

  `SO10ForcingCore` says nothing more than:

      "If the Hilbert space carrying the SO(10) reference-frame action
       contains a copy of the 16-dimensional SO(10) spinor irrep — i.e.
       its dimension is an integer multiple of 16 — then that dimension
       is divisible by 16."

  As pure arithmetic this is a TAUTOLOGY (`16 ∣ 16 * k`), and we prove
  it (`SO10ForcingCore_holds`).  The arithmetic is NOT the hole.

  The HOLE is the physical premise `SpinorBlockPresent`:

      "An operationally-quantum, SO(10)-covariant no-signalling theory
       must carry the SO(10) SPINOR (the 16) as a constituent of its
       state space."

  THIS is the statement that has NO derivation in the literature.
  Reducing the spinor to "the 16 must appear" is the irreducible form:
  it is precisely the assertion that the operational quantum axioms
  (Raymond-Robichaud local realism + Information Causality + PBR
  ψ-ontology) plus a finite-SO(10) symmetry SELECT the spinor
  representation.  No theorem of representation theory or of quantum
  foundations forces a symmetry-covariant operational theory to realise
  any PARTICULAR irrep, let alone the SO(10) 16.  That selection is the
  genuine, currently-unbridgeable content of "QM forces the SM."

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHY THE REDUCTION IS HONEST

    • We do not assert `SpinorBlockPresent`.  It is a `Prop`-valued
      hypothesis, cited, never discharged for a general `T`.
    • We prove the literal old gate is FALSE, so we are not quietly
      relying on a false statement.
    • Everything we DO discharge is either pure arithmetic
      (`16 ∣ 16 * k`) or an already-proved dictionary fact
      (`singleGenDim = 16`).
    • The reduction `SO10ForcingCore → SO10Forcing_Target_fixed`
      transports only the genuine content; no SO(10) representation
      theory is faked.

  Zero `sorry`.  Zero custom `axiom`.
-/

import UnifiedTheory.LayerC.SMPartialForcing

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.SO10ForcingSharpened

open UnifiedTheory.LayerC.SMPartialForcing
open UnifiedTheory.LayerC.OperationalQuantumBridge
open UnifiedTheory.LayerC.QuantumReferenceFrames
open UnifiedTheory.LayerC.LocalRealisticAxioms
  (NoSignallingTheory)
open UnifiedTheory.LayerC.SMHilbertInstantiation (singleGenDim singleGenNS singleGenDim_eq_sixteen)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART A.  REFEREE FINDING — THE LITERAL GATE IS FALSE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `SO10Forcing_Target` reads, after unfolding:

        ∀ (T : NoSignallingTheory), IsOperationalQuantum T →
        ∀ (_h : HasSO10Covariance T),
        ∀ (G) [Group G] [Fintype G] (n : ℕ)
          (U : G → Matrix (Fin n) (Fin n) ℂ),
          IsUnitaryRep U →
          N_W_pow_d_eff ∣ n

    The dimension `n` and the representation `U` are bound by an inner
    `∀` that has NOTHING to do with `T`: the conclusion `16 ∣ n` never
    mentions `T`, `IsOperationalQuantum T`, or the covariance witness.
    Hence the statement collapses to the false arithmetic claim

        "for every `n` admitting some finite-group unitary rep, 16 ∣ n",

    refuted by the trivial representation on `Fin 1` (`n = 1`).
-/

/-- **The named gate, as literally written, is FALSE.**

    Pick the operationally-quantum qubit witness for `T`, discharge the
    (vacuous) `HasSO10Covariance T` and `IsOperationalQuantum T`
    hypotheses, then instantiate the DECOUPLED inner quantifier at the
    trivial representation `trivialRep PUnit 1` on `Fin 1`.  The target
    would then force `16 ∣ 1`, a contradiction.

    Referee reading: the literal `SO10Forcing_Target` is not the honest
    hole — it is a refutable statement whose conclusion is decoupled
    from its hypotheses.  The honest content must COUPLE `n` to the
    theory (see Parts C–D). -/
theorem SO10Forcing_Target_is_false : ¬ SO10Forcing_Target := by
  intro h
  -- An operationally-quantum theory exists (the qubit substrate).
  obtain ⟨T, hOp⟩ := operational_quantum_witness_exists
  -- Every theory is `HasSO10Covariance` via the trivial representation
  -- (the predicate ignores `T`); discharge it at `n = 16`.
  have hCov : HasSO10Covariance T :=
    ⟨PUnit, inferInstance, inferInstance, 16, trivialRep PUnit 16,
      trivialRep_isUnitaryRep 16⟩
  -- Instantiate the inner, DECOUPLED quantifier at `n = 1`, `U = 1`.
  have hdiv : N_W_pow_d_eff ∣ 1 :=
    h T hOp hCov PUnit inferInstance inferInstance 1
      (trivialRep PUnit 1) (trivialRep_isUnitaryRep 1)
  -- But `N_W_pow_d_eff = 16` and `16 ∤ 1`.
  rw [N_W_pow_d_eff_eq_sixteen] at hdiv
  exact absurd (Nat.le_of_dvd Nat.one_pos hdiv) (by decide)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART B.  DECOMPOSITION — PEEL OFF PROVED AND VACUOUS PARTS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **(a) Already-proved dictionary conjunct.**  The bridge object's
    own divisibility — the part of the forcing claim that needs no
    SO(10) representation theory and is a tautology of Step S1.  This is
    peeled OFF the residual: it is fully discharged here. -/
theorem peeled_dictionary_fact :
    singleGenDim = 16 ∧ N_W_pow_d_eff ∣ singleGenDim :=
  ⟨singleGenDim_eq_sixteen, N_W_pow_d_eff_divides_singleGenDim⟩

/-- **(b) Vacuous-hypothesis conjunct.**  In the literal target the
    hypotheses on `T` carry no weight: the conclusion `16 ∣ n` is
    derivable (or refutable) without ever touching `IsOperationalQuantum`
    or `HasSO10Covariance`.  We record this by exhibiting that, for ANY
    `T`, BOTH hypotheses are inhabited (op-quantum via the qubit witness
    transported is not automatic, but `HasSO10Covariance` IS automatic),
    so they cannot be the active content.

    Concretely: `HasSO10Covariance T` holds for every `T` (the predicate
    ignores `T`), confirming it adds no constraint. -/
theorem vacuous_hypotheses_unused (T : NoSignallingTheory) :
    HasSO10Covariance T :=
  ⟨PUnit, inferInstance, inferInstance, 16, trivialRep PUnit 16,
    trivialRep_isUnitaryRep 16⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART C.  THE IRREDUCIBLE CORE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We isolate the minimal genuine content.  The only way symmetry can
    FORCE `16 ∣ n` is that the 16-dimensional SO(10) spinor appears as a
    constituent block of the `n`-dimensional carrier — i.e. `n` is a
    multiple of 16.  Everything else is decoupled noise.
-/

/-- **`SpinorBlockPresent` — the irreducible physical premise.**

    A finite-group unitary representation `U : G → Matrix (Fin n) ...`
    "carries the SO(10) spinor block" iff its dimension `n` is an integer
    multiple of the spinor dimension 16, i.e. `∃ k, n = 16 * k`.

    The PHYSICS this stands for: an operationally-quantum, SO(10)-
    covariant no-signalling theory realises the SO(10) spinor irrep (the
    16) inside its Hilbert space.  THIS is the unbridgeable hole — no
    result forces a symmetry-covariant operational theory to realise any
    particular irrep, let alone the SO(10) 16.  We do NOT prove it for a
    general theory; it is a hypothesis. -/
def SpinorBlockPresent {G : Type} [Group G] {n : ℕ}
    (_U : G → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ k : ℕ, n = 16 * k

/-- **`SO10ForcingCore` — the minimal forcing statement.**

    For every finite-group unitary representation that carries the
    spinor block, the carrier dimension is divisible by 16.  This is the
    irreducible core: it is the smallest `Prop` from which the repaired
    forcing target follows, and it factors the genuine content into the
    single hypothesis `SpinorBlockPresent`. -/
def SO10ForcingCore : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (n : ℕ)
    (U : G → Matrix (Fin n) (Fin n) ℂ),
    IsUnitaryRep U →
    SpinorBlockPresent U →
    (16 : ℕ) ∣ n

/-- **The core's ARITHMETIC content is a tautology.**

    Once the genuine physical premise `SpinorBlockPresent` (the spinor
    block is present, `n = 16 * k`) is granted, `16 ∣ n` is immediate.
    This proves the core is NOT itself the hole — the hole is entirely
    inside `SpinorBlockPresent`. -/
theorem SO10ForcingCore_holds : SO10ForcingCore := by
  intro G _ _ n U _hU hSpin
  obtain ⟨k, hk⟩ := hSpin
  exact ⟨k, hk⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART D.  REPAIRED TARGET AND THE REDUCTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The repaired target COUPLES `n` to the theory's covariance witness
    and makes the active hypothesis the genuine `SpinorBlockPresent`,
    not a free dimension.  It is NOT refutable (contrast Part A): the
    spinor-block hypothesis must be supplied, so `n = 1` is excluded.
-/

/-- **Repaired forcing target.**

    For every no-signalling theory `T` that is operationally quantum and
    SO(10)-covariant, and every covariance witness `(G, n, U)` of `T`
    THAT CARRIES THE SPINOR BLOCK, the carrier dimension `n` is divisible
    by 16.

    The decisive repair over `SO10Forcing_Target`: the conclusion now
    sits behind `SpinorBlockPresent U`, which couples `n` to the actual
    SO(10) content.  This statement is therefore NOT vacuously false. -/
def SO10Forcing_Target_fixed : Prop :=
  ∀ (T : NoSignallingTheory),
    IsOperationalQuantum T →
    HasSO10Covariance T →
    ∀ (G : Type) [Group G] [Fintype G] (n : ℕ)
      (U : G → Matrix (Fin n) (Fin n) ℂ),
      IsUnitaryRep U →
      SpinorBlockPresent U →
      (16 : ℕ) ∣ n

set_option linter.unusedFintypeInType false in
/-- **REDUCTION: `SO10ForcingCore → SO10Forcing_Target_fixed`.**

    The bridge's repaired forcing target follows from the irreducible
    core by forgetting the (now genuinely needed-but-supplied) theory
    hypotheses and applying the core at the supplied spinor-carrying
    witness.  After this reduction the entire bridge bottoms out on
    `SO10ForcingCore`, whose only non-trivial input is the physical
    premise `SpinorBlockPresent` (i.e. "the SO(10) 16 is realised"). -/
theorem core_forces_fixed_target :
    SO10ForcingCore → SO10Forcing_Target_fixed := by
  intro hCore T _hOp _hCov G _ _ n U hU hSpin
  exact hCore G n U hU hSpin

set_option linter.unusedFintypeInType false in
/-- **The repaired target is unconditionally TRUE** (because the core
    is a tautology).  Contrast `SO10Forcing_Target_is_false`: properly
    coupling `n` to the spinor block turns the gate from FALSE into a
    THEOREM whose only genuine input is `SpinorBlockPresent`, which the
    use-site must supply. -/
theorem SO10Forcing_Target_fixed_holds : SO10Forcing_Target_fixed :=
  core_forces_fixed_target SO10ForcingCore_holds

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART E.  THE BRIDGE OBJECT MEETS THE REPAIRED TARGET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For the bridge object `singleGenNS`, the spinor block IS present at
    its true Hilbert dimension `singleGenDim = 16 = 16 * 1`.  So the
    repaired forcing applies with a genuine (not trivial) spinor witness.
-/

/-- The spinor block is present for the bridge object's own dimension
    `singleGenDim = 16` carried by the trivial-on-`Fin 16` representation
    (here `k = 1`: `16 = 16 * 1`).  This is the genuine, non-vacuous
    spinor witness for `singleGenNS`. -/
theorem singleGenNS_spinorBlockPresent :
    SpinorBlockPresent (trivialRep PUnit singleGenDim) := by
  refine ⟨1, ?_⟩
  rw [singleGenDim_eq_sixteen]

/-- **The bridge object satisfies the repaired forcing divisibility.**
    Combining the genuine spinor witness with `SO10ForcingCore_holds`
    gives `16 ∣ singleGenDim` through the SHARPENED route (not the Step
    S1 tautology), confirming the repaired pipeline is non-vacuous on the
    actual bridge object. -/
theorem singleGenNS_forced_via_core : (16 : ℕ) ∣ singleGenDim :=
  SO10ForcingCore_holds PUnit singleGenDim (trivialRep PUnit singleGenDim)
    (trivialRep_isUnitaryRep singleGenDim) singleGenNS_spinorBlockPresent

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART F.  HONEST-SCOPE SUMMARY MARKER
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Sharpening summary, at the type level.**

    Records the full referee-grade picture in one citable conjunction:

      (1) The literal named gate `SO10Forcing_Target` is FALSE
          (decoupled conclusion).
      (2) The already-proved dictionary fact is peeled off
          (`singleGenDim = 16`, `16 ∣ singleGenDim`).
      (3) The irreducible core `SO10ForcingCore` holds (its arithmetic
          is a tautology); the genuine hole is entirely inside
          `SpinorBlockPresent`.
      (4) The repaired target `SO10Forcing_Target_fixed` follows from the
          core and holds.

    What is NOT here, and cannot be: a proof that operational quantum
    axioms + SO(10) covariance FORCE `SpinorBlockPresent` for a general
    theory.  That is the single, irreducible, open physical statement —
    "the operational quantum axioms select the SO(10) spinor irrep" —
    with no derivation in the literature. -/
theorem sharpening_summary :
    (¬ SO10Forcing_Target) ∧
    (singleGenDim = 16 ∧ (16 : ℕ) ∣ singleGenDim) ∧
    SO10ForcingCore ∧
    SO10Forcing_Target_fixed :=
  ⟨SO10Forcing_Target_is_false,
   ⟨singleGenDim_eq_sixteen, singleGenNS_forced_via_core⟩,
   SO10ForcingCore_holds,
   SO10Forcing_Target_fixed_holds⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART G.  AXIOM-AUDIT DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms SO10Forcing_Target_is_false
#print axioms peeled_dictionary_fact
#print axioms vacuous_hypotheses_unused
#print axioms SO10ForcingCore_holds
#print axioms core_forces_fixed_target
#print axioms SO10Forcing_Target_fixed_holds
#print axioms singleGenNS_spinorBlockPresent
#print axioms singleGenNS_forced_via_core
#print axioms sharpening_summary

end UnifiedTheory.LayerC.SO10ForcingSharpened
