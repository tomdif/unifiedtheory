/-
  UnifiedTheory/LayerC/BipartiteFullPostulatesQubit.lean
  ──────────────────────────────────────────────────────

  **Unconditional discharge of `BipartiteFullPostulates 2 2
  bipartiteAnalyticCore_2_2`.**

  The file `BipartiteUnitaryQM.lean` ships the bipartite phase-quotient
  unitary QM theory as a `NoSignallingTheory` conditional on the analytic
  core; the file `BipartiteNoSignallingAnalyticCoreDischarge.lean`
  discharges that core unconditionally.  Both upstream files leave the
  five-postulate bundle (`BipartiteFullPostulates`) as a hypothesis.

  Here we discharge the full bundle for every `n_A, n_B ≥ 1` with
  `[NeZero n_A] [NeZero n_B]`, including the qubit case n_A = n_B = 2,
  and upgrade the headline theorems
  `bipartiteQubitUnitaryQM_has_localRealisticModel` and
  `bipartite_qubit_shadow_concrete_Bell_content` to unconditional
  versions.

  ## Architecture

  All five postulates reduce by case analysis on the BipartiteSys
  lattice `Bool × Bool` plus reuse of the single-system unconditional
  results:

    * `bipartite_invertibleDynamics`  — already proved in BipartiteUnitaryQM.
    * `bipartite_separationPostulate` — 16-case match; nontrivial cases
      use injectivity of `(·, ·) : PhaseQuotient × PhaseQuotient`.
    * `bipartite_iAtimesCompat`       — case match on `A ≤ B`.
    * `bipartite_transProductActionPostulate` — uses bipartite product
      structure of T.Trans ⊤.
    * `bipartite_phenomenalFaithfulness` — reduces to single-system
      `phaseFaithfulnessAnalyticCore_general` via the analytic-core's
      `no_signalling_left/_right` on the (A=⊤) case.

  ## Standing constraint

  Zero `sorry`. Zero custom `axiom`.
-/

import UnifiedTheory.LayerC.BipartiteNoSignallingAnalyticCoreDischarge
import UnifiedTheory.LayerC.BipartiteQubitCHSH

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.LocalRealisticAxioms

open Matrix
open scoped Kronecker
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.UnitaryInvariance
open UnifiedTheory.LayerB.PartialTrace
open UnitaryQuantum

variable {n_A n_B : ℕ}

/-! ## 1.  SeparationPostulate for the bipartite theory.

  16-case match on `(A, B) : BipartiteSys × BipartiteSys`.  All
  pairs involving `⊤` on either side, AND non-disjoint pairs, are
  excluded by `hd`.  The remaining cases either trivially reduce
  by structural equality (one of A, B is ⊥) or use `Prod.mk.inj`
  on the joint `T.Trans ⊤ = PhaseQuotient n_A × PhaseQuotient n_B`
  to force the witness. -/

/-- **SeparationPostulate** for the bipartite phase-quotient theory. -/
theorem bipartite_separationPostulate
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B) :
    (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).SeparationPostulate := by
  intro A B hd V_Ac V_Bc hEq
  obtain ⟨a1, a2⟩ := A
  obtain ⟨b1, b2⟩ := B
  -- 16-case explicit match.
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2
  -- Case (⊥, ⊥)
  · exact ⟨V_Ac, rfl⟩
  -- Case (⊥, (F,T))
  · exact ⟨V_Bc, hEq⟩
  -- Case (⊥, (T,F))
  · exact ⟨V_Bc, hEq⟩
  -- Case (⊥, ⊤)
  · refine ⟨PUnit.unit, ?_⟩
    cases V_Bc
    exact hEq
  -- Case ((F,T), ⊥)
  · exact ⟨V_Ac, rfl⟩
  -- Case ((F,T), (F,T)) — non-disjoint
  · exact absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  -- Case ((F,T), (T,F)) — disjoint, A ⊔ B = ⊤
  · -- A = (F,T), Aᶜ = (T,F), V_Ac : PhaseQuotient n_A.
    -- B = (T,F), Bᶜ = (F,T), V_Bc : PhaseQuotient n_B.
    -- IAtimes (F,T) V_Ac = (V_Ac, 1); IAtimes (T,F) V_Bc = (1, V_Bc).
    -- hEq : (V_Ac, 1) = (1, V_Bc).
    refine ⟨PUnit.unit, ?_⟩
    have h_inj : ((V_Ac, (1 : PhaseQuotient n_B)) : PhaseQuotient n_A × PhaseQuotient n_B)
               = ((1, V_Bc) : PhaseQuotient n_A × PhaseQuotient n_B) := hEq
    have hVA : V_Ac = (1 : PhaseQuotient n_A) := (Prod.mk.inj h_inj).1
    -- Goal: IAtimes (F,T) V_Ac = IAtimes ⊤ PUnit.unit.
    -- Both equal (1, 1) = 1.
    show ((V_Ac, (1 : PhaseQuotient n_B)) : PhaseQuotient n_A × PhaseQuotient n_B)
        = (1 : PhaseQuotient n_A × PhaseQuotient n_B)
    rw [hVA]; rfl
  -- Case ((F,T), ⊤) — non-disjoint
  · exact absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  -- Case ((T,F), ⊥)
  · exact ⟨V_Ac, rfl⟩
  -- Case ((T,F), (F,T)) — disjoint, A ⊔ B = ⊤
  · refine ⟨PUnit.unit, ?_⟩
    have h_inj : (((1 : PhaseQuotient n_A), V_Ac) : PhaseQuotient n_A × PhaseQuotient n_B)
               = ((V_Bc, 1) : PhaseQuotient n_A × PhaseQuotient n_B) := hEq
    have hVA : V_Ac = (1 : PhaseQuotient n_B) := (Prod.mk.inj h_inj).2
    show (((1 : PhaseQuotient n_A), V_Ac) : PhaseQuotient n_A × PhaseQuotient n_B)
        = (1 : PhaseQuotient n_A × PhaseQuotient n_B)
    rw [hVA]; rfl
  -- Case ((T,F), (T,F)) — non-disjoint
  · exact absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  -- Case ((T,F), ⊤) — non-disjoint
  · exact absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  -- Case (⊤, ⊥)
  · refine ⟨PUnit.unit, ?_⟩
    cases V_Ac
    rfl
  -- Case (⊤, (F,T)) — non-disjoint
  · exact absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  -- Case (⊤, (T,F)) — non-disjoint
  · exact absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  -- Case (⊤, ⊤) — non-disjoint
  · exact absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true

/-! ## 2.  IAtimesCompat for the bipartite theory.

  Case split on `(A, B)` with `A ≤ B` in `BipartiteSys = Bool × Bool`. -/

/-- **IAtimesCompat** for the bipartite phase-quotient theory. -/
theorem bipartite_iAtimesCompat
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B) :
    (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).IAtimesCompat := by
  intro A B h V
  obtain ⟨a1, a2⟩ := A
  obtain ⟨b1, b2⟩ := B
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2
  -- A = ⊥, B = ⊥
  · exact ⟨V, rfl⟩
  -- A = ⊥, B = (F,T)
  · -- V : T.Trans (F,T)ᶜ = T.Trans (T,F) = PhaseQuotient n_A.
    -- IAtimes (F,T) V = (V, 1) : T.Trans ⊤.
    -- Aᶜ = ⊤; V' : T.Trans ⊤.  Take V' = (V, 1).
    refine ⟨((V, 1) : PhaseQuotient n_A × PhaseQuotient n_B), ?_⟩
    rfl
  -- A = ⊥, B = (T,F)
  · refine ⟨((1, V) : PhaseQuotient n_A × PhaseQuotient n_B), ?_⟩
    rfl
  -- A = ⊥, B = ⊤
  · refine ⟨(1 : PhaseQuotient n_A × PhaseQuotient n_B), ?_⟩
    cases V
    rfl
  -- A = (F,T), B = ⊥ — impossible by h
  · exact absurd h.2 not_true_le_false
  -- A = (F,T), B = (F,T)
  · exact ⟨V, rfl⟩
  -- A = (F,T), B = (T,F) — impossible
  · exact absurd h.2 not_true_le_false
  -- A = (F,T), B = ⊤
  · -- V : T.Trans ⊥ = PUnit.  IAtimes ⊤ V = 1.
    -- Aᶜ = (T,F); V' : PhaseQuotient n_A. Take 1.
    refine ⟨(1 : PhaseQuotient n_A), ?_⟩
    cases V
    rfl
  -- A = (T,F), B = ⊥ — impossible
  · exact absurd h.1 not_true_le_false
  -- A = (T,F), B = (F,T) — impossible
  · exact absurd h.1 not_true_le_false
  -- A = (T,F), B = (T,F)
  · exact ⟨V, rfl⟩
  -- A = (T,F), B = ⊤
  · refine ⟨(1 : PhaseQuotient n_B), ?_⟩
    cases V
    rfl
  -- A = ⊤, B = ⊥ — impossible
  · exact absurd h.1 not_true_le_false
  -- A = ⊤, B = (F,T) — impossible
  · exact absurd h.1 not_true_le_false
  -- A = ⊤, B = (T,F) — impossible
  · exact absurd h.2 not_true_le_false
  -- A = ⊤, B = ⊤
  · exact ⟨V, rfl⟩

/-! ## 3.  TransProductActionPostulate for the bipartite theory.

  In `BipartiteSys`, disjoint pairs are restricted enough that the
  postulate reduces to direct algebraic identities on the joint
  transformations `(U_A, U_B) : PhaseQuotient n_A × PhaseQuotient n_B`. -/

/-- Helper computations for the bipartite `UliftA` and `IAtimes`. -/

private lemma bipartite_uliftA_TF
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B)
    (U : PhaseQuotient n_A) :
    HardDirection.UliftA (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore)
        ((true, false) : BipartiteSys) U
      = ((U, 1) : PhaseQuotient n_A × PhaseQuotient n_B) := rfl

private lemma bipartite_uliftA_FT
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B)
    (U : PhaseQuotient n_B) :
    HardDirection.UliftA (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore)
        ((false, true) : BipartiteSys) U
      = ((1, U) : PhaseQuotient n_A × PhaseQuotient n_B) := rfl

private lemma bipartite_uliftA_TT
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B)
    (U : PhaseQuotient n_A × PhaseQuotient n_B) :
    HardDirection.UliftA (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore)
        ((true, true) : BipartiteSys) U
      = U := rfl

private lemma bipartite_uliftA_FF
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B)
    (U : PUnit) :
    HardDirection.UliftA (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore)
        ((false, false) : BipartiteSys) U
      = (1 : PhaseQuotient n_A × PhaseQuotient n_B) := rfl

private lemma bipartite_iAtimes_FF
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B)
    (V : PhaseQuotient n_A × PhaseQuotient n_B) :
    (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).IAtimes
        ((false, false) : BipartiteSys) V = V := rfl

private lemma bipartite_iAtimes_TF
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B)
    (V : PhaseQuotient n_B) :
    (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).IAtimes
        ((true, false) : BipartiteSys) V
      = ((1, V) : PhaseQuotient n_A × PhaseQuotient n_B) := rfl

private lemma bipartite_iAtimes_FT
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B)
    (V : PhaseQuotient n_A) :
    (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).IAtimes
        ((false, true) : BipartiteSys) V
      = ((V, 1) : PhaseQuotient n_A × PhaseQuotient n_B) := rfl

/-- **TransProductActionPostulate** for the bipartite phase-quotient theory. -/
theorem bipartite_transProductActionPostulate
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B) :
    (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).TransProductActionPostulate := by
  intro A B hd U V W
  obtain ⟨a1, a2⟩ := A
  obtain ⟨b1, b2⟩ := B
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2
  -- A = ⊥, B = ⊥
  · exact ⟨HardDirection.TransfEquivRel.refl _ _ _,
          HardDirection.TransfEquivRel.refl _ _ _⟩
  -- A = ⊥, B = (F,T)
  · -- transProduct ⊥ (F,T) U V = V (where V : PhaseQuotient n_B).
    -- UliftA (⊥ ⊔ (F,T)) V = UliftA (F,T) V = (1, V).
    -- UliftA ⊥ U = 1; UliftA (F,T) V = (1, V).
    refine ⟨?_, HardDirection.TransfEquivRel.refl _ _ _⟩
    refine ⟨((1, V) : PhaseQuotient n_A × PhaseQuotient n_B), ?_⟩
    rw [bipartite_iAtimes_FF, bipartite_uliftA_FF, one_mul]
    rfl
  -- A = ⊥, B = (T,F)
  · refine ⟨?_, HardDirection.TransfEquivRel.refl _ _ _⟩
    refine ⟨((V, 1) : PhaseQuotient n_A × PhaseQuotient n_B), ?_⟩
    rw [bipartite_iAtimes_FF, bipartite_uliftA_FF, one_mul]
    rfl
  -- A = ⊥, B = ⊤
  · refine ⟨?_, HardDirection.TransfEquivRel.refl _ _ _⟩
    refine ⟨V, ?_⟩
    rw [bipartite_iAtimes_FF, bipartite_uliftA_FF, one_mul]
    rfl
  -- A = (F,T), B = ⊥
  · refine ⟨HardDirection.TransfEquivRel.refl _ _ _, ?_⟩
    refine ⟨((1, U) : PhaseQuotient n_A × PhaseQuotient n_B), ?_⟩
    rw [bipartite_iAtimes_FF, bipartite_uliftA_FF, one_mul]
    rfl
  -- A = (F,T), B = (F,T) — impossible
  · exact absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  -- A = (F,T), B = (T,F) — disjoint, A ⊔ B = ⊤
  · -- U : PhaseQuotient n_B, V : PhaseQuotient n_A.
    -- transProduct (F,T)(T,F) U V = (V, U) : PhaseQuotient n_A × PhaseQuotient n_B.
    set W' : PhaseQuotient n_A × PhaseQuotient n_B := W with hW'
    refine ⟨?_, ?_⟩
    · refine ⟨V, ?_⟩
      show ((V, U) : PhaseQuotient n_A × PhaseQuotient n_B) * W'
          = ((V, 1) : PhaseQuotient n_A × PhaseQuotient n_B)
              * (((1, U) : PhaseQuotient n_A × PhaseQuotient n_B) * W')
      rw [← mul_assoc]
      congr 1
      ext <;> simp
    · refine ⟨U, ?_⟩
      show ((V, U) : PhaseQuotient n_A × PhaseQuotient n_B) * W'
          = ((1, U) : PhaseQuotient n_A × PhaseQuotient n_B)
              * (((V, 1) : PhaseQuotient n_A × PhaseQuotient n_B) * W')
      rw [← mul_assoc]
      congr 1
      ext <;> simp
  -- A = (F,T), B = ⊤ — impossible
  · exact absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  -- A = (T,F), B = ⊥
  · refine ⟨HardDirection.TransfEquivRel.refl _ _ _, ?_⟩
    refine ⟨((U, 1) : PhaseQuotient n_A × PhaseQuotient n_B), ?_⟩
    rw [bipartite_iAtimes_FF, bipartite_uliftA_FF, one_mul]
    rfl
  -- A = (T,F), B = (F,T) — disjoint, A ⊔ B = ⊤
  · -- U : PhaseQuotient n_A, V : PhaseQuotient n_B.
    set W' : PhaseQuotient n_A × PhaseQuotient n_B := W with hW'
    refine ⟨?_, ?_⟩
    · refine ⟨V, ?_⟩
      show ((U, V) : PhaseQuotient n_A × PhaseQuotient n_B) * W'
          = ((1, V) : PhaseQuotient n_A × PhaseQuotient n_B)
              * (((U, 1) : PhaseQuotient n_A × PhaseQuotient n_B) * W')
      rw [← mul_assoc]
      congr 1
      ext <;> simp
    · refine ⟨U, ?_⟩
      show ((U, V) : PhaseQuotient n_A × PhaseQuotient n_B) * W'
          = ((U, 1) : PhaseQuotient n_A × PhaseQuotient n_B)
              * (((1, V) : PhaseQuotient n_A × PhaseQuotient n_B) * W')
      rw [← mul_assoc]
      congr 1
      ext <;> simp
  -- A = (T,F), B = (T,F) — impossible
  · exact absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  -- A = (T,F), B = ⊤ — impossible
  · exact absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  -- A = ⊤, B = ⊥
  · refine ⟨HardDirection.TransfEquivRel.refl _ _ _, ?_⟩
    refine ⟨U, ?_⟩
    rw [bipartite_iAtimes_FF, bipartite_uliftA_FF, one_mul]
    rfl
  -- A = ⊤, B = (F,T) — impossible
  · exact absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  -- A = ⊤, B = (T,F) — impossible
  · exact absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  -- A = ⊤, B = ⊤ — impossible
  · exact absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true

/-! ## 4.  PhenomenalFaithfulness for the bipartite theory.

  Case split on `A : BipartiteSys`.  The non-trivial cases reduce to
  the single-system `phaseFaithfulnessAnalyticCore_general`. -/

/-- Helper: the bipartite phenomenal action at A=(T,F), B=(F,F) on a
    quotient class.  Both the lattice join `(T,F) ⊔ (F,F) = (T,F)` and the
    `1 : PUnit` form arise from the discharge of `hAct` at `B := (F,F)`. -/
private lemma bipartite_phenAction_TF_FF_mk
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B)
    (U' : Matrix.unitaryGroup (Fin n_A) ℂ)
    (ρ : ComplexDensityMatrix n_A) :
    ((bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).phenomenalAction
        (((true, false) : BipartiteSys) ⊔ ((false, false) : BipartiteSys))).act
        ((bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).transProduct
          (disjoint_bot_right : Disjoint ((true, false) : BipartiteSys)
                                          ((false, false) : BipartiteSys))
          (Quotient.mk _ U' : PhaseQuotient n_A)
          (1 : (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).Trans
                ((false, false) : BipartiteSys))) ρ
      = unitaryConjugate U' ρ := rfl

/-- Helper: the bipartite phenomenal action at A=(F,T), B=(F,F). -/
private lemma bipartite_phenAction_FT_FF_mk
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B)
    (U' : Matrix.unitaryGroup (Fin n_B) ℂ)
    (ρ : ComplexDensityMatrix n_B) :
    ((bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).phenomenalAction
        (((false, true) : BipartiteSys) ⊔ ((false, false) : BipartiteSys))).act
        ((bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).transProduct
          (disjoint_bot_right : Disjoint ((false, true) : BipartiteSys)
                                          ((false, false) : BipartiteSys))
          (Quotient.mk _ U' : PhaseQuotient n_B)
          (1 : (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).Trans
                ((false, false) : BipartiteSys))) ρ
      = unitaryConjugate U' ρ := rfl

/-- Helper: the bipartite phenomenal action at A=⊤, B=(F,F). -/
private lemma bipartite_phenAction_TT_FF_mk
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B)
    (U_A : Matrix.unitaryGroup (Fin n_A) ℂ)
    (U_B : Matrix.unitaryGroup (Fin n_B) ℂ)
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    ((bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).phenomenalAction
        (((true, true) : BipartiteSys) ⊔ ((false, false) : BipartiteSys))).act
        ((bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).transProduct
          (disjoint_bot_right : Disjoint ((true, true) : BipartiteSys)
                                          ((false, false) : BipartiteSys))
          ((Quotient.mk _ U_A : PhaseQuotient n_A),
           (Quotient.mk _ U_B : PhaseQuotient n_B))
          (1 : (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).Trans
                ((false, false) : BipartiteSys))) ρ
      = kroneckerConjugate U_A U_B ρ := rfl

/-- **PhenomenalFaithfulness** for the bipartite phase-quotient theory.

    Reduces to the single-system phase-faithfulness analytic core
    (which holds unconditionally for every dimension `n` by
    `phaseFaithfulnessAnalyticCore_general n`). -/
theorem bipartite_phenomenalFaithfulness
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B) :
    (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).PhenomenalFaithfulness := by
  intro A U V hAct
  obtain ⟨a1, a2⟩ := A
  cases a1 <;> cases a2
  -- A = ⊥
  · cases U; cases V; rfl
  -- A = (F, T)
  · -- T.Trans (F,T) = PhaseQuotient n_B.
    induction U, V using Quotient.inductionOn₂ with
    | _ U' V' =>
      have hd : Disjoint ((false, true) : BipartiteSys) ((false, false) : BipartiteSys) :=
        disjoint_bot_right
      have hPhen : ∀ ρ : ComplexDensityMatrix n_B,
          unitaryConjugate U' ρ = unitaryConjugate V' ρ := by
        intro ρ
        have h := hAct (B := ((false, false) : BipartiteSys)) hd ρ
        rw [bipartite_phenAction_FT_FF_mk, bipartite_phenAction_FT_FF_mk] at h
        exact h
      exact Quotient.sound (phaseFaithfulnessAnalyticCore_general n_B U' V' hPhen)
  -- A = (T, F)
  · -- T.Trans (T,F) = PhaseQuotient n_A.
    induction U, V using Quotient.inductionOn₂ with
    | _ U' V' =>
      have hd : Disjoint ((true, false) : BipartiteSys) ((false, false) : BipartiteSys) :=
        disjoint_bot_right
      have hPhen : ∀ ρ : ComplexDensityMatrix n_A,
          unitaryConjugate U' ρ = unitaryConjugate V' ρ := by
        intro ρ
        have h := hAct (B := ((false, false) : BipartiteSys)) hd ρ
        rw [bipartite_phenAction_TF_FF_mk, bipartite_phenAction_TF_FF_mk] at h
        exact h
      exact Quotient.sound (phaseFaithfulnessAnalyticCore_general n_A U' V' hPhen)
  -- A = ⊤
  · -- T.Trans ⊤ = PhaseQuotient n_A × PhaseQuotient n_B.
    obtain ⟨U_Aq, U_Bq⟩ := U
    obtain ⟨V_Aq, V_Bq⟩ := V
    induction U_Aq, V_Aq using Quotient.inductionOn₂ with
    | _ U_A V_A =>
      induction U_Bq, V_Bq using Quotient.inductionOn₂ with
      | _ U_B V_B =>
        have hd : Disjoint ((true, true) : BipartiteSys) ((false, false) : BipartiteSys) :=
          disjoint_bot_right
        have hKron : ∀ ρ_AB : ComplexDensityMatrix (n_A * n_B),
            kroneckerConjugate U_A U_B ρ_AB
              = kroneckerConjugate V_A V_B ρ_AB := by
          intro ρ_AB
          have h := hAct (B := ((false, false) : BipartiteSys)) hd ρ_AB
          rw [bipartite_phenAction_TT_FF_mk, bipartite_phenAction_TT_FF_mk] at h
          exact h
        -- Reduce to single-system phase-faithfulness on each side via
        -- partial-trace surjectivity + no-signalling.
        have hPhenA : ∀ σ_A : ComplexDensityMatrix n_A,
            unitaryConjugate U_A σ_A = unitaryConjugate V_A σ_A := by
          intro σ_A
          obtain ⟨ρ_AB, hρ⟩ := hCore.phenomenalProj_left_surjective σ_A
          have h := hKron ρ_AB
          have h_apply :
              densityPartialTrace_rightDM n_A n_B
                  (kroneckerConjugate U_A U_B ρ_AB)
                = densityPartialTrace_rightDM n_A n_B
                    (kroneckerConjugate V_A V_B ρ_AB) := by
            rw [h]
          rw [hCore.no_signalling_left, hCore.no_signalling_left] at h_apply
          rw [hρ] at h_apply
          exact h_apply
        have hPhenB : ∀ σ_B : ComplexDensityMatrix n_B,
            unitaryConjugate U_B σ_B = unitaryConjugate V_B σ_B := by
          intro σ_B
          obtain ⟨ρ_AB, hρ⟩ := hCore.phenomenalProj_right_surjective σ_B
          have h := hKron ρ_AB
          have h_apply :
              densityPartialTrace_leftDM n_A n_B
                  (kroneckerConjugate U_A U_B ρ_AB)
                = densityPartialTrace_leftDM n_A n_B
                    (kroneckerConjugate V_A V_B ρ_AB) := by
            rw [h]
          rw [hCore.no_signalling_right, hCore.no_signalling_right] at h_apply
          rw [hρ] at h_apply
          exact h_apply
        have hA : Quotient.mk (phaseEquivSetoid n_A) U_A
                  = Quotient.mk (phaseEquivSetoid n_A) V_A :=
          Quotient.sound (phaseFaithfulnessAnalyticCore_general n_A U_A V_A hPhenA)
        have hB : Quotient.mk (phaseEquivSetoid n_B) U_B
                  = Quotient.mk (phaseEquivSetoid n_B) V_B :=
          Quotient.sound (phaseFaithfulnessAnalyticCore_general n_B U_B V_B hPhenB)
        show ((Quotient.mk _ U_A : PhaseQuotient n_A),
              (Quotient.mk _ U_B : PhaseQuotient n_B))
            = ((Quotient.mk _ V_A : PhaseQuotient n_A),
               (Quotient.mk _ V_B : PhaseQuotient n_B))
        rw [hA, hB]

/-! ## 5.  Packaging — the full bundle of all five postulates,
        unconditional in the analytic core. -/

/-- **All five paper-5.1 postulates hold for the bipartite
    phase-quotient theory**, unconditionally in the analytic core. -/
theorem bipartiteFullPostulates_of_core
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B) :
    BipartiteFullPostulates n_A n_B hCore := {
  invertible    := bipartite_invertibleDynamics n_A n_B hCore
  separation    := bipartite_separationPostulate n_A n_B hCore
  phenomenal    := bipartite_phenomenalFaithfulness n_A n_B hCore
  iAtimesCompat := bipartite_iAtimesCompat n_A n_B hCore
  transProdAct  := bipartite_transProductActionPostulate n_A n_B hCore
}

/-- **All five paper-5.1 postulates hold unconditionally for the
    bipartite qubit substrate.** -/
theorem bipartiteFullPostulates_qubit :
    BipartiteFullPostulates 2 2 bipartiteAnalyticCore_2_2 :=
  bipartiteFullPostulates_of_core 2 2 bipartiteAnalyticCore_2_2

/-! ## 6.  THE UNCONDITIONAL HEADLINES. -/

/-- **THE UNCONDITIONAL BIPARTITE HEADLINE (any dimension).**

    Bipartite phase-quotient unitary QM admits a local-realistic shadow,
    for every `n_A, n_B ≥ 1`, with NO hypotheses. -/
theorem bipartiteUnitaryQM_has_localRealisticModel_unconditional
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B] :
    ∃ L : LocalRealisticTheory,
      L.IsNoSignallingShadow
        (bipartiteUnitaryQuantumNoSignalling n_A n_B
          (bipartiteAnalyticCore n_A n_B)) :=
  bipartiteUnitaryQM_has_localRealisticModel n_A n_B
    (bipartiteFullPostulates_of_core n_A n_B (bipartiteAnalyticCore n_A n_B))

/-- **THE UNCONDITIONAL BIPARTITE-QUBIT HEADLINE.** -/
theorem bipartiteQubitUnitaryQM_has_localRealisticModel_unconditional :
    ∃ L : LocalRealisticTheory,
      L.IsNoSignallingShadow bipartiteQubitUnitaryQuantumNoSignalling :=
  bipartiteQubitUnitaryQM_has_localRealisticModel bipartiteFullPostulates_qubit

/-- **THE UNCONDITIONAL CONCRETE BELL CONTENT.**

    Three properties of the bipartite-qubit phase-quotient unitary
    substrate, in one statement, with NO hypotheses:

      1. The substrate admits a local-realistic shadow (Raymond-Robichaud).
      2. The singlet density matrix with equator observables reproduces
         the Bell correlation `E(θa, θb) = -cos(θa - θb)`.
      3. CHSH saturates `|S| = 2√2` at the standard angles. -/
theorem bipartite_qubit_shadow_concrete_Bell_content_unconditional :
    (∃ L : LocalRealisticTheory,
        L.IsNoSignallingShadow bipartiteQubitUnitaryQuantumNoSignalling)
  ∧ (∀ θa θb : ℝ,
        UnifiedTheory.LayerC.BipartiteQubitCHSH.correlation
          UnifiedTheory.LayerC.BipartiteQubitCHSH.singletCDM
          (UnifiedTheory.LayerC.BipartiteQubitCHSH.equatorObservable θa)
          (UnifiedTheory.LayerC.BipartiteQubitCHSH.equatorObservable θb)
          = -Real.cos (θa - θb))
  ∧ (let E := fun a b : ℝ =>
        UnifiedTheory.LayerC.BipartiteQubitCHSH.correlation
          UnifiedTheory.LayerC.BipartiteQubitCHSH.singletCDM
          (UnifiedTheory.LayerC.BipartiteQubitCHSH.equatorObservable a)
          (UnifiedTheory.LayerC.BipartiteQubitCHSH.equatorObservable b)
     |E 0 (Real.pi/4) + E 0 (-(Real.pi/4)) + E (Real.pi/2) (Real.pi/4)
        - E (Real.pi/2) (-(Real.pi/4))| = 2 * Real.sqrt 2) :=
  UnifiedTheory.LayerC.BipartiteQubitCHSH.bipartite_qubit_shadow_concrete_Bell_content
    bipartiteFullPostulates_qubit

/-! ## 7.  Axiom-check diagnostics. -/

#print axioms bipartiteFullPostulates_qubit
#print axioms bipartiteQubitUnitaryQM_has_localRealisticModel_unconditional
#print axioms bipartite_qubit_shadow_concrete_Bell_content_unconditional

end UnifiedTheory.LayerC.LocalRealisticAxioms
