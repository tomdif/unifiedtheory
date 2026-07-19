/-
  UnifiedTheory/LayerC/BipartiteUnitaryQM.lean
  ──────────────────────────────────────────────

  **Bipartite phase-quotient unitary quantum theory** as a
  `NoSignallingTheory` on a 4-element Boolean lattice.

  This file converts the single-system, Bool-lattice headline
  theorem `phaseQuotientUnitaryQM_has_localRealisticModel` (proved
  unconditionally in `PhaseFaithfulnessAllN.lean`) into the
  explicit **bipartite (two-party) scenario** that underlies all
  Bell / EPR / CHSH formulations.

  ## What is shipped

  ### Tier 1 — Bipartite lattice

  The lattice of systems is `Bool × Bool`, with
  `⊥ = (false, false)`, `⊤ = (true, true)`, and the two single-
  party systems `A = (true, false)`, `B = (false, true)`.

  ### Tier 2 — Bipartite phenomenal-transformation data

    * `BipartitePhenomenalSpace n_A n_B` — at `⊥`: `PUnit`; at
      `A`: `ComplexDensityMatrix n_A`; at `B`:
      `ComplexDensityMatrix n_B`; at `⊤`:
      `ComplexDensityMatrix (n_A * n_B)`.
    * `BipartiteTransSpace n_A n_B` — at `⊥`: `PUnit`; at `A`:
      `PhaseQuotient n_A`; at `B`: `PhaseQuotient n_B`; at `⊤`:
      `PhaseQuotient n_A × PhaseQuotient n_B` (local unitaries).
    * Monoid instance on every `BipartiteTransSpace`.

  ### Tier 3 — Kronecker conjugation action

  * `kroneckerUnitary U_A U_B` is `U_A ⊗ U_B` reindexed to
    `Fin (n_A * n_B)`.
  * `kroneckerConjugate U_A U_B ρ` is `(U_A ⊗ U_B) ρ (U_A ⊗ U_B)†`.
  * Both descend through the phase quotient on each factor.

  ### Tier 4 — Bipartite NoSignallingTheory bundle (conditional)

  The bipartite analytic core
  `BipartiteNoSignallingAnalyticCore n_A n_B` packages the four
  truly-bipartite analytic obligations:

  * `phenomenalProj_left_surjective` — surjectivity of
    `densityPartialTrace_rightDM` (partial-trace projection
    from joint to Alice).
  * `phenomenalProj_right_surjective` — symmetric.
  * `no_signalling_left` — `πA((U_A ⊗ U_B) ρ (U_A ⊗ U_B)†)
    = U_A πA(ρ) U_A†`.
  * `no_signalling_right` — symmetric.

  Given the core, the file ships the bipartite
  `NoSignallingTheory` instance
  `bipartiteUnitaryQuantumNoSignalling`.

  ### THE BIPARTITE HEADLINE (conditional)

      theorem bipartiteUnitaryQM_has_localRealisticModel_of_core
          (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
          (hCore : BipartiteNoSignallingAnalyticCore n_A n_B)
          (hPost : BipartiteFullPostulates n_A n_B hCore) :
        ∃ L : LocalRealisticTheory,
          L.IsNoSignallingShadow
            (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore)

  Per honest scoping (paper Section 4 indicates 4.6.2-style
  associativity content beyond our `NoSignallingTheory`
  axiomatisation), the standard five-postulate bundle for the
  bipartite theory is exposed as a hypothesis — exactly as in
  the single-system case for `PhaseFaithfulnessAnalyticCore`.

  ## Standing constraint

  Zero `sorry`, zero custom `axiom`.
-/

import UnifiedTheory.LayerC.PhaseFaithfulnessAllN
import UnifiedTheory.LayerB.PartialTrace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic

set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.LayerC.LocalRealisticAxioms

open Matrix
open scoped Kronecker
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.UnitaryInvariance
open UnifiedTheory.LayerB.PartialTrace
open UnitaryQuantum

/-! ## 1.  The bipartite lattice `Bool × Bool` -/

/-- The bipartite lattice of systems.

    * `(false, false) = ⊥` — the empty system.
    * `(true,  false) = A` — Alice's system.
    * `(false, true ) = B` — Bob's system.
    * `(true,  true ) = ⊤` — the joint system. -/
abbrev BipartiteSys : Type := Bool × Bool

/-! ## 2.  Bipartite phenomenal + transformation spaces -/

/-- Phenomenal state space, indexed by `BipartiteSys`. -/
def BipartitePhenomenalSpace (n_A n_B : ℕ) : BipartiteSys → Type
  | (false, false) => PUnit
  | (true,  false) => ComplexDensityMatrix n_A
  | (false, true ) => ComplexDensityMatrix n_B
  | (true,  true ) => ComplexDensityMatrix (n_A * n_B)

/-- Transformation set, indexed by `BipartiteSys`.

    On the joint system `⊤` we take **local** unitaries (pairs of
    PhaseQuotients on each subsystem), which captures the
    Bell-scenario-relevant subset of joint transformations. -/
def BipartiteTransSpace (n_A n_B : ℕ) : BipartiteSys → Type
  | (false, false) => PUnit
  | (true,  false) => PhaseQuotient n_A
  | (false, true ) => PhaseQuotient n_B
  | (true,  true ) => PhaseQuotient n_A × PhaseQuotient n_B

instance instMonoidBipartiteTrans (n_A n_B : ℕ) :
    ∀ s : BipartiteSys, Monoid (BipartiteTransSpace n_A n_B s)
  | (false, false) => inferInstanceAs (Monoid PUnit)
  | (true,  false) => inferInstanceAs (Monoid (PhaseQuotient n_A))
  | (false, true ) => inferInstanceAs (Monoid (PhaseQuotient n_B))
  | (true,  true ) =>
      inferInstanceAs (Monoid (PhaseQuotient n_A × PhaseQuotient n_B))

/-- For each `s : BipartiteSys`, an inverse-with-cancellation
    package, providing the data `InvertibleDynamics` needs. -/
def bipartiteInvPair (n_A n_B : ℕ) :
    ∀ {s : BipartiteSys} (U : BipartiteTransSpace n_A n_B s),
      { V : BipartiteTransSpace n_A n_B s // V * U = 1 ∧ U * V = 1 }
  | (false, false), _ =>
      ⟨PUnit.unit, rfl, rfl⟩
  | (true,  false), U =>
      let U' : PhaseQuotient n_A := U
      ⟨(U'⁻¹ : PhaseQuotient n_A),
        inv_mul_cancel U', mul_inv_cancel U'⟩
  | (false, true ), U =>
      let U' : PhaseQuotient n_B := U
      ⟨(U'⁻¹ : PhaseQuotient n_B),
        inv_mul_cancel U', mul_inv_cancel U'⟩
  | (true,  true ), U =>
      let U' : PhaseQuotient n_A × PhaseQuotient n_B := U
      ⟨(U'⁻¹ : PhaseQuotient n_A × PhaseQuotient n_B),
        inv_mul_cancel U', mul_inv_cancel U'⟩

instance instPhenomNonempty_bipartite
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B] :
    ∀ s : BipartiteSys, Nonempty (BipartitePhenomenalSpace n_A n_B s)
  | (false, false) => ⟨PUnit.unit⟩
  | (true,  false) => ⟨basisDensityMatrix n_A⟩
  | (false, true ) => ⟨basisDensityMatrix n_B⟩
  | (true,  true ) =>
      haveI : NeZero (n_A * n_B) :=
        ⟨Nat.mul_ne_zero (NeZero.ne n_A) (NeZero.ne n_B)⟩
      ⟨basisDensityMatrix (n_A * n_B)⟩

/-! ## 3.  Kronecker unitary and conjugation -/

/-- The Kronecker product `U_A ⊗ U_B` reindexed from
    `Fin n_A × Fin n_B` to `Fin (n_A * n_B)`. -/
noncomputable def kroneckerUnitary
    {n_A n_B : ℕ} (U_A : Matrix.unitaryGroup (Fin n_A) ℂ)
    (U_B : Matrix.unitaryGroup (Fin n_B) ℂ) :
    Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ :=
  (U_A.val ⊗ₖ U_B.val).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- Star of a submatrix is the submatrix of the star. -/
private lemma star_submatrix
    {n_A n_B : ℕ} (M : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ) :
    star (M.submatrix finProdFinEquiv.symm finProdFinEquiv.symm)
      = (star M).submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
  ext i j
  simp [Matrix.submatrix_apply, Matrix.star_apply,
        Matrix.conjTranspose_apply]

/-- The Kronecker product of two unitaries is unitary
    (right identity `W * W† = 1`). -/
lemma kroneckerUnitary_mul_star
    {n_A n_B : ℕ} (U_A : Matrix.unitaryGroup (Fin n_A) ℂ)
    (U_B : Matrix.unitaryGroup (Fin n_B) ℂ) :
    (kroneckerUnitary U_A U_B) * star (kroneckerUnitary U_A U_B) = 1 := by
  unfold kroneckerUnitary
  rw [star_submatrix]
  rw [Matrix.submatrix_mul_equiv (U_A.val ⊗ₖ U_B.val)
        (star (U_A.val ⊗ₖ U_B.val))
        finProdFinEquiv.symm finProdFinEquiv.symm finProdFinEquiv.symm]
  have h_star_kron :
      star (U_A.val ⊗ₖ U_B.val) = (star U_A.val) ⊗ₖ (star U_B.val) := by
    show (U_A.val ⊗ₖ U_B.val)ᴴ = U_A.valᴴ ⊗ₖ U_B.valᴴ
    exact Matrix.conjTranspose_kronecker U_A.val U_B.val
  rw [h_star_kron]
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.mem_unitaryGroup_iff.mp U_A.property,
      Matrix.mem_unitaryGroup_iff.mp U_B.property]
  rw [Matrix.one_kronecker_one]
  -- 1.submatrix e e = 1 when e is bijective.
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.submatrix_apply, Matrix.one_apply_eq]
  · have h' : finProdFinEquiv.symm i ≠ finProdFinEquiv.symm j := by
      intro he
      apply h
      exact finProdFinEquiv.symm.injective he
    show (1 : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ)
            (finProdFinEquiv.symm i) (finProdFinEquiv.symm j)
        = (1 : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ) i j
    rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h']

/-- `unitaryGroup`-wrapped Kronecker unitary. -/
noncomputable def kroneckerUnitaryGrp
    {n_A n_B : ℕ} (U_A : Matrix.unitaryGroup (Fin n_A) ℂ)
    (U_B : Matrix.unitaryGroup (Fin n_B) ℂ) :
    Matrix.unitaryGroup (Fin (n_A * n_B)) ℂ :=
  ⟨kroneckerUnitary U_A U_B,
    Matrix.mem_unitaryGroup_iff.mpr (kroneckerUnitary_mul_star U_A U_B)⟩

/-- Kronecker conjugation packaged as a density matrix on
    `Fin (n_A * n_B)`. -/
noncomputable def kroneckerConjugate
    {n_A n_B : ℕ} (U_A : Matrix.unitaryGroup (Fin n_A) ℂ)
    (U_B : Matrix.unitaryGroup (Fin n_B) ℂ)
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    ComplexDensityMatrix (n_A * n_B) :=
  unitaryConjugate (kroneckerUnitaryGrp U_A U_B) ρ

/-- `kroneckerUnitaryGrp` is multiplicative. -/
lemma kroneckerUnitaryGrp_mul
    {n_A n_B : ℕ} (U_A V_A : Matrix.unitaryGroup (Fin n_A) ℂ)
    (U_B V_B : Matrix.unitaryGroup (Fin n_B) ℂ) :
    (kroneckerUnitaryGrp U_A U_B) * (kroneckerUnitaryGrp V_A V_B)
      = kroneckerUnitaryGrp (U_A * V_A) (U_B * V_B) := by
  apply Subtype.ext
  show kroneckerUnitary U_A U_B * kroneckerUnitary V_A V_B
      = kroneckerUnitary (U_A * V_A) (U_B * V_B)
  unfold kroneckerUnitary
  rw [Matrix.submatrix_mul_equiv (U_A.val ⊗ₖ U_B.val) (V_A.val ⊗ₖ V_B.val)
        finProdFinEquiv.symm finProdFinEquiv.symm finProdFinEquiv.symm]
  have h_kr :
      (U_A * V_A).val ⊗ₖ (U_B * V_B).val
        = (U_A.val ⊗ₖ U_B.val) * (V_A.val ⊗ₖ V_B.val) := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul]
    exact Matrix.mul_kronecker_mul U_A.val V_A.val U_B.val V_B.val
  rw [h_kr]

/-- `kroneckerUnitaryGrp 1 1 = 1`. -/
lemma kroneckerUnitaryGrp_one
    (n_A n_B : ℕ) :
    kroneckerUnitaryGrp (1 : Matrix.unitaryGroup (Fin n_A) ℂ)
                        (1 : Matrix.unitaryGroup (Fin n_B) ℂ)
      = 1 := by
  apply Subtype.ext
  show kroneckerUnitary
        (1 : Matrix.unitaryGroup (Fin n_A) ℂ)
        (1 : Matrix.unitaryGroup (Fin n_B) ℂ)
      = (1 : Matrix.unitaryGroup (Fin (n_A * n_B)) ℂ).val
  unfold kroneckerUnitary
  have h_one_val_A :
      (1 : Matrix.unitaryGroup (Fin n_A) ℂ).val
        = (1 : Matrix (Fin n_A) (Fin n_A) ℂ) := rfl
  have h_one_val_B :
      (1 : Matrix.unitaryGroup (Fin n_B) ℂ).val
        = (1 : Matrix (Fin n_B) (Fin n_B) ℂ) := rfl
  rw [h_one_val_A, h_one_val_B, Matrix.one_kronecker_one]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.submatrix_apply, Matrix.one_apply_eq]
  · have h' : finProdFinEquiv.symm i ≠ finProdFinEquiv.symm j := by
      intro he
      apply h
      exact finProdFinEquiv.symm.injective he
    show (1 : Matrix (Fin n_A × Fin n_B) (Fin n_A × Fin n_B) ℂ)
            (finProdFinEquiv.symm i) (finProdFinEquiv.symm j)
        = (1 : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ) i j
    rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h']

/-- A helper: `‖z‖² = 1` in ℂ for `z : Circle`. -/
private lemma star_circle_mul_self (z : Circle) :
    (star (z : ℂ)) * (z : ℂ) = 1 := by
  have h2 : (starRingEnd ℂ) (z : ℂ) * (z : ℂ)
              = ((Complex.normSq (z : ℂ)) : ℂ) :=
    Complex.normSq_eq_conj_mul_self.symm
  have h3 : Complex.normSq (z : ℂ) = ‖(z : ℂ)‖ ^ 2 :=
    Complex.normSq_eq_norm_sq _
  have h4 : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
  have h5 : (star (z : ℂ)) = (starRingEnd ℂ) (z : ℂ) := rfl
  rw [h5, h2, h3, h4]; simp

/-- Multiplying `U_A` by a phase `z` doesn't change the conjugation. -/
lemma kroneckerConjugate_smul_left
    {n_A n_B : ℕ} (U_A V_A : Matrix.unitaryGroup (Fin n_A) ℂ)
    (U_B : Matrix.unitaryGroup (Fin n_B) ℂ) (z : Circle)
    (hV : V_A.val = (z : ℂ) • U_A.val)
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    kroneckerConjugate V_A U_B ρ = kroneckerConjugate U_A U_B ρ := by
  rw [UnitaryQuantum.ComplexDensityMatrix.ext_iff_M]
  show kroneckerUnitary V_A U_B * ρ.M * star (kroneckerUnitary V_A U_B)
      = kroneckerUnitary U_A U_B * ρ.M * star (kroneckerUnitary U_A U_B)
  have h_eq :
      kroneckerUnitary V_A U_B = (z : ℂ) • kroneckerUnitary U_A U_B := by
    unfold kroneckerUnitary
    ext i j
    rw [Matrix.smul_apply, Matrix.submatrix_apply, Matrix.submatrix_apply,
        Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply]
    have h_val : V_A.val (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
                  = (z : ℂ) * U_A.val (finProdFinEquiv.symm i).1
                                      (finProdFinEquiv.symm j).1 := by
      have := congrFun (congrFun hV (finProdFinEquiv.symm i).1)
                       (finProdFinEquiv.symm j).1
      simpa [Matrix.smul_apply, smul_eq_mul] using this
    rw [h_val, smul_eq_mul]
    ring
  rw [h_eq, star_smul, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
      smul_smul]
  rw [star_circle_mul_self z, one_smul]

lemma kroneckerConjugate_smul_right
    {n_A n_B : ℕ} (U_A : Matrix.unitaryGroup (Fin n_A) ℂ)
    (U_B V_B : Matrix.unitaryGroup (Fin n_B) ℂ) (z : Circle)
    (hV : V_B.val = (z : ℂ) • U_B.val)
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    kroneckerConjugate U_A V_B ρ = kroneckerConjugate U_A U_B ρ := by
  rw [UnitaryQuantum.ComplexDensityMatrix.ext_iff_M]
  show kroneckerUnitary U_A V_B * ρ.M * star (kroneckerUnitary U_A V_B)
      = kroneckerUnitary U_A U_B * ρ.M * star (kroneckerUnitary U_A U_B)
  have h_eq :
      kroneckerUnitary U_A V_B = (z : ℂ) • kroneckerUnitary U_A U_B := by
    unfold kroneckerUnitary
    ext i j
    rw [Matrix.smul_apply, Matrix.submatrix_apply, Matrix.submatrix_apply,
        Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply]
    have h_val : V_B.val (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2
                  = (z : ℂ) * U_B.val (finProdFinEquiv.symm i).2
                                      (finProdFinEquiv.symm j).2 := by
      have := congrFun (congrFun hV (finProdFinEquiv.symm i).2)
                       (finProdFinEquiv.symm j).2
      simpa [Matrix.smul_apply, smul_eq_mul] using this
    rw [h_val, smul_eq_mul]
    ring
  rw [h_eq, star_smul, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
      smul_smul]
  rw [star_circle_mul_self z, one_smul]

/-- The joint action descends through the phase quotients on each
    factor. -/
noncomputable def actJoint
    (n_A n_B : ℕ) :
    PhaseQuotient n_A × PhaseQuotient n_B
      → ComplexDensityMatrix (n_A * n_B) → ComplexDensityMatrix (n_A * n_B) :=
  fun q ρ =>
    Quotient.liftOn₂ q.1 q.2
      (fun U_A U_B => kroneckerConjugate U_A U_B ρ)
      (fun U_A U_B U_A' U_B' hA hB => by
        rcases hA with ⟨zA, hzA⟩
        rcases hB with ⟨zB, hzB⟩
        -- U_A' = zA • U_A, U_B' = zB • U_B.
        have step1 : kroneckerConjugate U_A' U_B ρ = kroneckerConjugate U_A U_B ρ :=
          kroneckerConjugate_smul_left U_A U_A' U_B zA hzA ρ
        have step2 : kroneckerConjugate U_A' U_B' ρ = kroneckerConjugate U_A' U_B ρ :=
          kroneckerConjugate_smul_right U_A' U_B U_B' zB hzB ρ
        change kroneckerConjugate U_A U_B ρ = kroneckerConjugate U_A' U_B' ρ
        rw [step2, step1])

@[simp] lemma actJoint_mk (n_A n_B : ℕ)
    (U_A : Matrix.unitaryGroup (Fin n_A) ℂ)
    (U_B : Matrix.unitaryGroup (Fin n_B) ℂ)
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    actJoint n_A n_B
        (Quotient.mk _ U_A, Quotient.mk _ U_B) ρ
      = kroneckerConjugate U_A U_B ρ := rfl

/-- The joint action is a `MonoidAction`. -/
noncomputable def bipartiteActionTop
    (n_A n_B : ℕ) :
    MonoidAction (PhaseQuotient n_A × PhaseQuotient n_B)
                 (ComplexDensityMatrix (n_A * n_B)) where
  act := actJoint n_A n_B
  act_mul := by
    intro q1 q2 ρ
    obtain ⟨q1A, q1B⟩ := q1
    obtain ⟨q2A, q2B⟩ := q2
    refine Quotient.inductionOn₂ q1A q1B (fun U1A U1B => ?_)
    refine Quotient.inductionOn₂ q2A q2B (fun U2A U2B => ?_)
    show actJoint n_A n_B
            ((Quotient.mk _ U1A, Quotient.mk _ U1B) *
              (Quotient.mk _ U2A, Quotient.mk _ U2B)) ρ
          = actJoint n_A n_B (Quotient.mk _ U1A, Quotient.mk _ U1B)
              (actJoint n_A n_B (Quotient.mk _ U2A, Quotient.mk _ U2B) ρ)
    show actJoint n_A n_B
            (Quotient.mk _ U1A * Quotient.mk _ U2A,
             Quotient.mk _ U1B * Quotient.mk _ U2B) ρ
          = actJoint n_A n_B (Quotient.mk _ U1A, Quotient.mk _ U1B)
              (actJoint n_A n_B (Quotient.mk _ U2A, Quotient.mk _ U2B) ρ)
    simp only [mk_mul]
    rw [actJoint_mk, actJoint_mk, actJoint_mk]
    rw [UnitaryQuantum.ComplexDensityMatrix.ext_iff_M]
    show kroneckerUnitary (U1A * U2A) (U1B * U2B) * ρ.M
            * star (kroneckerUnitary (U1A * U2A) (U1B * U2B))
        = kroneckerUnitary U1A U1B
            * (kroneckerUnitary U2A U2B * ρ.M
                * star (kroneckerUnitary U2A U2B))
            * star (kroneckerUnitary U1A U1B)
    have h_mul :
        kroneckerUnitary (U1A * U2A) (U1B * U2B)
          = kroneckerUnitary U1A U1B * kroneckerUnitary U2A U2B := by
      have := kroneckerUnitaryGrp_mul U1A U2A U1B U2B
      have h := congrArg Subtype.val this
      show kroneckerUnitary (U1A * U2A) (U1B * U2B)
          = kroneckerUnitary U1A U1B * kroneckerUnitary U2A U2B
      have h_lhs : (kroneckerUnitaryGrp (U1A * U2A) (U1B * U2B)).val
                    = kroneckerUnitary (U1A * U2A) (U1B * U2B) := rfl
      have h_rhs : ((kroneckerUnitaryGrp U1A U1B) *
                    (kroneckerUnitaryGrp U2A U2B)).val
                    = kroneckerUnitary U1A U1B *
                      kroneckerUnitary U2A U2B := rfl
      rw [← h_lhs, ← h_rhs, h]
    rw [h_mul]
    rw [Matrix.star_mul]
    simp only [Matrix.mul_assoc]
  act_one := by
    intro ρ
    show actJoint n_A n_B (1, 1) ρ = ρ
    -- 1 in product = ⟨1, 1⟩
    show actJoint n_A n_B
            ((1 : PhaseQuotient n_A), (1 : PhaseQuotient n_B)) ρ = ρ
    show actJoint n_A n_B
            (Quotient.mk _ (1 : Matrix.unitaryGroup (Fin n_A) ℂ),
             Quotient.mk _ (1 : Matrix.unitaryGroup (Fin n_B) ℂ)) ρ = ρ
    rw [actJoint_mk]
    rw [UnitaryQuantum.ComplexDensityMatrix.ext_iff_M]
    show kroneckerUnitary
            (1 : Matrix.unitaryGroup (Fin n_A) ℂ)
            (1 : Matrix.unitaryGroup (Fin n_B) ℂ) * ρ.M
          * star (kroneckerUnitary
                    (1 : Matrix.unitaryGroup (Fin n_A) ℂ)
                    (1 : Matrix.unitaryGroup (Fin n_B) ℂ))
        = ρ.M
    have h_one :
        kroneckerUnitary
          (1 : Matrix.unitaryGroup (Fin n_A) ℂ)
          (1 : Matrix.unitaryGroup (Fin n_B) ℂ)
          = (1 : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ) := by
      have h := kroneckerUnitaryGrp_one n_A n_B
      have hv := congrArg Subtype.val h
      show kroneckerUnitary
            (1 : Matrix.unitaryGroup (Fin n_A) ℂ)
            (1 : Matrix.unitaryGroup (Fin n_B) ℂ)
          = (1 : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ)
      have h_lhs : (kroneckerUnitaryGrp
                    (1 : Matrix.unitaryGroup (Fin n_A) ℂ)
                    (1 : Matrix.unitaryGroup (Fin n_B) ℂ)).val
                    = kroneckerUnitary
                        (1 : Matrix.unitaryGroup (Fin n_A) ℂ)
                        (1 : Matrix.unitaryGroup (Fin n_B) ℂ) := rfl
      have h_rhs : (1 : Matrix.unitaryGroup (Fin (n_A * n_B)) ℂ).val
                    = (1 : Matrix (Fin (n_A * n_B)) (Fin (n_A * n_B)) ℂ) :=
        rfl
      rw [← h_lhs, ← h_rhs, hv]
    rw [h_one, star_one, Matrix.one_mul, Matrix.mul_one]

/-! ## 4.  Density-matrix bridge for partial trace. -/

/-- `densityPartialTrace_right` packaged as a `ComplexDensityMatrix`. -/
noncomputable def densityPartialTrace_rightDM
    (n_A n_B : ℕ) (ρ : ComplexDensityMatrix (n_A * n_B)) :
    ComplexDensityMatrix n_A where
  M := densityPartialTrace_right ρ
  hHerm := densityPartialTrace_right_isHermitian ρ
  hTrace := densityPartialTrace_right_trace ρ
  hTracePSD := by
    intro X
    have h_psd : (densityPartialTrace_right ρ).PosSemidef :=
      densityPartialTrace_right_posSemidef ρ
    have h_cyc : Matrix.trace (densityPartialTrace_right ρ
                                * X.conjTranspose * X)
                = Matrix.trace (X * densityPartialTrace_right ρ
                                  * X.conjTranspose) := by
      rw [Matrix.trace_mul_comm
            (densityPartialTrace_right ρ * X.conjTranspose) X]
      rw [Matrix.mul_assoc]
    rw [h_cyc]
    have h_psd_X : Matrix.PosSemidef
                    (X * densityPartialTrace_right ρ * X.conjTranspose) :=
      h_psd.mul_mul_conjTranspose_same X
    have h_nn : 0 ≤ Matrix.trace
                  (X * densityPartialTrace_right ρ * X.conjTranspose) :=
      h_psd_X.trace_nonneg
    exact (Complex.nonneg_iff.mp h_nn).1

/-- `densityPartialTrace_left` packaged as a `ComplexDensityMatrix`. -/
noncomputable def densityPartialTrace_leftDM
    (n_A n_B : ℕ) (ρ : ComplexDensityMatrix (n_A * n_B)) :
    ComplexDensityMatrix n_B where
  M := densityPartialTrace_left ρ
  hHerm := densityPartialTrace_left_isHermitian ρ
  hTrace := densityPartialTrace_left_trace ρ
  hTracePSD := by
    intro X
    have h_psd : (densityPartialTrace_left ρ).PosSemidef :=
      densityPartialTrace_left_posSemidef ρ
    have h_cyc : Matrix.trace (densityPartialTrace_left ρ
                                * X.conjTranspose * X)
                = Matrix.trace (X * densityPartialTrace_left ρ
                                  * X.conjTranspose) := by
      rw [Matrix.trace_mul_comm
            (densityPartialTrace_left ρ * X.conjTranspose) X]
      rw [Matrix.mul_assoc]
    rw [h_cyc]
    have h_psd_X : Matrix.PosSemidef
                    (X * densityPartialTrace_left ρ * X.conjTranspose) :=
      h_psd.mul_mul_conjTranspose_same X
    have h_nn : 0 ≤ Matrix.trace
                  (X * densityPartialTrace_left ρ * X.conjTranspose) :=
      h_psd_X.trace_nonneg
    exact (Complex.nonneg_iff.mp h_nn).1

/-! ## 5.  Naming the bipartite analytic obligations -/

/-- The bipartite analytic obligations bundle.

    The first two fields ensure the phenomenal projector
    `densityPartialTrace_{right,left}DM` is surjective from the
    joint system to each subsystem.  The latter two encode the
    deep Kronecker–partial-trace identity (paper Axiom 4.6.1 in
    the truly bipartite form). -/
structure BipartiteNoSignallingAnalyticCore
    (n_A n_B : ℕ) : Prop where
  /-- Every Alice-density-matrix is the right partial trace of
      some joint density matrix. -/
  phenomenalProj_left_surjective :
    ∀ ρ_A : ComplexDensityMatrix n_A,
      ∃ ρ_AB : ComplexDensityMatrix (n_A * n_B),
        densityPartialTrace_rightDM n_A n_B ρ_AB = ρ_A
  /-- Every Bob-density-matrix is the left partial trace of some
      joint density matrix. -/
  phenomenalProj_right_surjective :
    ∀ ρ_B : ComplexDensityMatrix n_B,
      ∃ ρ_AB : ComplexDensityMatrix (n_A * n_B),
        densityPartialTrace_leftDM n_A n_B ρ_AB = ρ_B
  /-- (NS-L): Tracing out Bob commutes with conjugation by `(U_A ⊗ U_B)`
      on Alice. -/
  no_signalling_left :
    ∀ (U_A : Matrix.unitaryGroup (Fin n_A) ℂ)
      (U_B : Matrix.unitaryGroup (Fin n_B) ℂ)
      (ρ : ComplexDensityMatrix (n_A * n_B)),
      densityPartialTrace_rightDM n_A n_B
          (kroneckerConjugate U_A U_B ρ)
        = unitaryConjugate U_A (densityPartialTrace_rightDM n_A n_B ρ)
  /-- (NS-R): Tracing out Alice commutes with conjugation by
      `(U_A ⊗ U_B)` on Bob. -/
  no_signalling_right :
    ∀ (U_A : Matrix.unitaryGroup (Fin n_A) ℂ)
      (U_B : Matrix.unitaryGroup (Fin n_B) ℂ)
      (ρ : ComplexDensityMatrix (n_A * n_B)),
      densityPartialTrace_leftDM n_A n_B
          (kroneckerConjugate U_A U_B ρ)
        = unitaryConjugate U_B (densityPartialTrace_leftDM n_A n_B ρ)

/-! ## 6.  Bipartite phenomenal action -/

/-- The full phenomenal action across `BipartiteSys`. -/
noncomputable def bipartitePhenomenalAction
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B] :
    ∀ s : BipartiteSys,
      MonoidAction (BipartiteTransSpace n_A n_B s)
                   (BipartitePhenomenalSpace n_A n_B s)
  | (false, false) =>
    { act := fun _ _ => PUnit.unit
      act_mul := fun _ _ _ => rfl
      act_one := fun ρ => by cases ρ; rfl }
  | (true,  false) => phaseQuotientPhenomenalAction_true n_A
  | (false, true ) => phaseQuotientPhenomenalAction_true n_B
  | (true,  true ) => bipartiteActionTop n_A n_B

/-! ## 7.  Bipartite phenomenal projector -/

/-- The bipartite phenomenal projector, defined by case-analysis on
    `Bool × Bool`. -/
noncomputable def bipartitePhenomenalProj
    (n_A n_B : ℕ) :
    ∀ {a b : BipartiteSys}, a ≤ b →
      BipartitePhenomenalSpace n_A n_B b → BipartitePhenomenalSpace n_A n_B a
  | (false, false), (false, false), _, _ => PUnit.unit
  | (false, false), (true,  false), _, _ => PUnit.unit
  | (false, false), (false, true ), _, _ => PUnit.unit
  | (false, false), (true,  true ), _, _ => PUnit.unit
  | (true,  false), (true,  false), _, ρ => ρ
  | (false, true ), (false, true ), _, ρ => ρ
  | (true,  false), (true,  true ), _, ρ => densityPartialTrace_rightDM n_A n_B ρ
  | (false, true ), (true,  true ), _, ρ => densityPartialTrace_leftDM n_A n_B ρ
  | (true,  true ), (true,  true ), _, ρ => ρ
  | (true,  false), (false, false), h, _ => absurd h.1 not_true_le_false
  | (true,  false), (false, true ), h, _ => absurd h.1 not_true_le_false
  | (false, true ), (false, false), h, _ => absurd h.2 not_true_le_false
  | (false, true ), (true,  false), h, _ => absurd h.2 not_true_le_false
  | (true,  true ), (false, false), h, _ => absurd h.1 not_true_le_false
  | (true,  true ), (true,  false), h, _ => absurd h.2 not_true_le_false
  | (true,  true ), (false, true ), h, _ => absurd h.1 not_true_le_false

/-- Projector composition is structural (rfl in every reachable case). -/
lemma bipartitePhenomenalProj_comp
    (n_A n_B : ℕ) :
    ∀ {a b c : BipartiteSys} (hab : a ≤ b) (hbc : b ≤ c)
      (ρ : BipartitePhenomenalSpace n_A n_B c),
      bipartitePhenomenalProj n_A n_B hab
          (bipartitePhenomenalProj n_A n_B hbc ρ)
        = bipartitePhenomenalProj n_A n_B (hab.trans hbc) ρ
  | (false, false), (false, false), (false, false), _, _, _ => rfl
  | (false, false), (false, false), (true,  false), _, _, _ => rfl
  | (false, false), (false, false), (false, true ), _, _, _ => rfl
  | (false, false), (false, false), (true,  true ), _, _, _ => rfl
  | (false, false), (true,  false), (true,  false), _, _, _ => rfl
  | (false, false), (true,  false), (true,  true ), _, _, _ => rfl
  | (false, false), (false, true ), (false, true ), _, _, _ => rfl
  | (false, false), (false, true ), (true,  true ), _, _, _ => rfl
  | (false, false), (true,  true ), (true,  true ), _, _, _ => rfl
  | (true,  false), (true,  false), (true,  false), _, _, _ => rfl
  | (true,  false), (true,  false), (true,  true ), _, _, _ => rfl
  | (true,  false), (true,  true ), (true,  true ), _, _, _ => rfl
  | (false, true ), (false, true ), (false, true ), _, _, _ => rfl
  | (false, true ), (false, true ), (true,  true ), _, _, _ => rfl
  | (false, true ), (true,  true ), (true,  true ), _, _, _ => rfl
  | (true,  true ), (true,  true ), (true,  true ), _, _, _ => rfl
  -- impossible cases on hab:
  | (true,  false), (false, false), _, h, _, _ => absurd h.1 not_true_le_false
  | (true,  false), (false, true ), _, h, _, _ => absurd h.1 not_true_le_false
  | (false, true ), (false, false), _, h, _, _ => absurd h.2 not_true_le_false
  | (false, true ), (true,  false), _, h, _, _ => absurd h.2 not_true_le_false
  | (true,  true ), (false, false), _, h, _, _ => absurd h.1 not_true_le_false
  | (true,  true ), (true,  false), _, h, _, _ => absurd h.2 not_true_le_false
  | (true,  true ), (false, true ), _, h, _, _ => absurd h.1 not_true_le_false
  -- impossible cases on hbc:
  | _, (true,  false), (false, false), _, h, _ => absurd h.1 not_true_le_false
  | _, (true,  false), (false, true ), _, h, _ => absurd h.1 not_true_le_false
  | _, (false, true ), (false, false), _, h, _ => absurd h.2 not_true_le_false
  | _, (false, true ), (true,  false), _, h, _ => absurd h.2 not_true_le_false
  | _, (true,  true ), (false, false), _, h, _ => absurd h.1 not_true_le_false
  | _, (true,  true ), (true,  false), _, h, _ => absurd h.2 not_true_le_false
  | _, (true,  true ), (false, true ), _, h, _ => absurd h.1 not_true_le_false

/-- Surjectivity of the bipartite phenomenal projector, given the
    bipartite analytic core. -/
lemma bipartitePhenomenalProj_surjective_of_core
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B) :
    ∀ {a b : BipartiteSys} (h : a ≤ b),
      Function.Surjective (bipartitePhenomenalProj n_A n_B h)
  | (false, false), (false, false), _ => fun _ => ⟨PUnit.unit, rfl⟩
  | (false, false), (true,  false), _ => fun _ => ⟨basisDensityMatrix n_A, rfl⟩
  | (false, false), (false, true ), _ => fun _ => ⟨basisDensityMatrix n_B, rfl⟩
  | (false, false), (true,  true ), _ => fun _ =>
      haveI : NeZero (n_A * n_B) :=
        ⟨Nat.mul_ne_zero (NeZero.ne n_A) (NeZero.ne n_B)⟩
      ⟨basisDensityMatrix (n_A * n_B), rfl⟩
  | (true,  false), (true,  false), _ => fun ρ => ⟨ρ, rfl⟩
  | (false, true ), (false, true ), _ => fun ρ => ⟨ρ, rfl⟩
  | (true,  true ), (true,  true ), _ => fun ρ => ⟨ρ, rfl⟩
  | (true,  false), (true,  true ), _ => fun ρ_A =>
      hCore.phenomenalProj_left_surjective ρ_A
  | (false, true ), (true,  true ), _ => fun ρ_B =>
      hCore.phenomenalProj_right_surjective ρ_B
  | (true,  false), (false, false), h => absurd h.1 not_true_le_false
  | (true,  false), (false, true ), h => absurd h.1 not_true_le_false
  | (false, true ), (false, false), h => absurd h.2 not_true_le_false
  | (false, true ), (true,  false), h => absurd h.2 not_true_le_false
  | (true,  true ), (false, false), h => absurd h.1 not_true_le_false
  | (true,  true ), (true,  false), h => absurd h.2 not_true_le_false
  | (true,  true ), (false, true ), h => absurd h.1 not_true_le_false

/-! ## 8.  Bipartite transformation product. -/

/-- Bipartite transformation product. -/
def bipartiteTransProduct (n_A n_B : ℕ) :
    ∀ {a b : BipartiteSys}, Disjoint a b →
      BipartiteTransSpace n_A n_B a → BipartiteTransSpace n_A n_B b
      → BipartiteTransSpace n_A n_B (a ⊔ b)
  | (false, false), (false, false), _, _, _ => PUnit.unit
  | (false, false), (true,  false), _, _, U => U
  | (false, false), (false, true ), _, _, U => U
  | (false, false), (true,  true ), _, _, U => U
  | (true,  false), (false, false), _, U, _ => U
  | (false, true ), (false, false), _, U, _ => U
  | (true,  true ), (false, false), _, U, _ => U
  | (true,  false), (false, true ), _, U_A, U_B => (U_A, U_B)
  | (false, true ), (true,  false), _, U_B, U_A => (U_A, U_B)
  | (true,  false), (true,  false), hd, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (true,  false), (true,  true ), hd, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (false, true ), (false, true ), hd, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (false, true ), (true,  true ), hd, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (true,  true ), (true,  false), hd, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (true,  true ), (false, true ), hd, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (true,  true ), (true,  true ), hd, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true

/-! ## 9.  Bipartite no-signalling laws (4.6.1) — discharged via the core. -/

lemma bipartite_no_signalling
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B) :
    ∀ {a b : BipartiteSys} (hd : Disjoint a b)
      (U : BipartiteTransSpace n_A n_B a) (V : BipartiteTransSpace n_A n_B b)
      (ρ : BipartitePhenomenalSpace n_A n_B (a ⊔ b)),
      bipartitePhenomenalProj n_A n_B (le_sup_left : a ≤ a ⊔ b)
          ((bipartitePhenomenalAction n_A n_B (a ⊔ b)).act
              (bipartiteTransProduct n_A n_B hd U V) ρ)
        = (bipartitePhenomenalAction n_A n_B a).act U
            (bipartitePhenomenalProj n_A n_B
              (le_sup_left : a ≤ a ⊔ b) ρ)
  | (false, false), (false, false), _, _, _, _ => rfl
  | (false, false), (true,  false), _, _, _, _ => rfl
  | (false, false), (false, true ), _, _, _, _ => rfl
  | (false, false), (true,  true ), _, _, _, _ => rfl
  | (true,  false), (false, false), _, _, _, _ => rfl
  | (false, true ), (false, false), _, _, _, _ => rfl
  | (true,  true ), (false, false), _, _, _, _ => rfl
  | (true,  false), (false, true ), _, U_A, U_B, ρ_AB => by
      -- a ⊔ b = (true, true).
      refine Quotient.inductionOn₂ U_A U_B (fun U_Ar U_Br => ?_)
      change densityPartialTrace_rightDM n_A n_B
              (actJoint n_A n_B
                  (Quotient.mk _ U_Ar, Quotient.mk _ U_Br) ρ_AB)
            = phaseQuotientAct n_A (Quotient.mk _ U_Ar)
                (densityPartialTrace_rightDM n_A n_B ρ_AB)
      rw [actJoint_mk, phaseQuotientAct_mk]
      exact hCore.no_signalling_left U_Ar U_Br ρ_AB
  | (false, true ), (true,  false), _, U_B, U_A, ρ_AB => by
      -- Here a = (false,true) is Bob, b = (true,false) is Alice.
      -- The le_sup_left here is (false,true) ≤ (true,true),
      -- so the projector is densityPartialTrace_leftDM.
      refine Quotient.inductionOn₂ U_B U_A (fun U_Br U_Ar => ?_)
      change densityPartialTrace_leftDM n_A n_B
              (actJoint n_A n_B
                  (Quotient.mk _ U_Ar, Quotient.mk _ U_Br) ρ_AB)
            = phaseQuotientAct n_B (Quotient.mk _ U_Br)
                (densityPartialTrace_leftDM n_A n_B ρ_AB)
      rw [actJoint_mk, phaseQuotientAct_mk]
      exact hCore.no_signalling_right U_Ar U_Br ρ_AB
  | (true,  false), (true,  false), hd, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (true,  false), (true,  true ), hd, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (false, true ), (false, true ), hd, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (false, true ), (true,  true ), hd, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (true,  true ), (true,  false), hd, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (true,  true ), (false, true ), hd, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (true,  true ), (true,  true ), hd, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true

lemma bipartite_no_signalling_right
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B) :
    ∀ {a b : BipartiteSys} (hd : Disjoint a b)
      (U : BipartiteTransSpace n_A n_B a) (V : BipartiteTransSpace n_A n_B b)
      (ρ : BipartitePhenomenalSpace n_A n_B (a ⊔ b)),
      bipartitePhenomenalProj n_A n_B (le_sup_right : b ≤ a ⊔ b)
          ((bipartitePhenomenalAction n_A n_B (a ⊔ b)).act
              (bipartiteTransProduct n_A n_B hd U V) ρ)
        = (bipartitePhenomenalAction n_A n_B b).act V
            (bipartitePhenomenalProj n_A n_B
              (le_sup_right : b ≤ a ⊔ b) ρ)
  | (false, false), (false, false), _, _, _, _ => rfl
  | (false, false), (true,  false), _, _, _, _ => rfl
  | (false, false), (false, true ), _, _, _, _ => rfl
  | (false, false), (true,  true ), _, _, _, _ => rfl
  | (true,  false), (false, false), _, _, _, _ => rfl
  | (false, true ), (false, false), _, _, _, _ => rfl
  | (true,  true ), (false, false), _, _, _, _ => rfl
  | (true,  false), (false, true ), _, U_A, U_B, ρ_AB => by
      refine Quotient.inductionOn₂ U_A U_B (fun U_Ar U_Br => ?_)
      change densityPartialTrace_leftDM n_A n_B
              (actJoint n_A n_B
                  (Quotient.mk _ U_Ar, Quotient.mk _ U_Br) ρ_AB)
            = phaseQuotientAct n_B (Quotient.mk _ U_Br)
                (densityPartialTrace_leftDM n_A n_B ρ_AB)
      rw [actJoint_mk, phaseQuotientAct_mk]
      exact hCore.no_signalling_right U_Ar U_Br ρ_AB
  | (false, true ), (true,  false), _, U_B, U_A, ρ_AB => by
      refine Quotient.inductionOn₂ U_B U_A (fun U_Br U_Ar => ?_)
      change densityPartialTrace_rightDM n_A n_B
              (actJoint n_A n_B
                  (Quotient.mk _ U_Ar, Quotient.mk _ U_Br) ρ_AB)
            = phaseQuotientAct n_A (Quotient.mk _ U_Ar)
                (densityPartialTrace_rightDM n_A n_B ρ_AB)
      rw [actJoint_mk, phaseQuotientAct_mk]
      exact hCore.no_signalling_left U_Ar U_Br ρ_AB
  | (true,  false), (true,  false), hd, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (true,  false), (true,  true ), hd, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (false, true ), (false, true ), hd, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (false, true ), (true,  true ), hd, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (true,  true ), (true,  false), hd, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (true,  true ), (false, true ), hd, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (true,  true ), (true,  true ), hd, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true

lemma bipartite_transProduct_mul
    (n_A n_B : ℕ) :
    ∀ {a b : BipartiteSys} (hd : Disjoint a b)
      (U₁ V₁ : BipartiteTransSpace n_A n_B a)
      (U₂ V₂ : BipartiteTransSpace n_A n_B b),
      bipartiteTransProduct n_A n_B hd V₁ V₂
        * bipartiteTransProduct n_A n_B hd U₁ U₂
        = bipartiteTransProduct n_A n_B hd (V₁ * U₁) (V₂ * U₂)
  | (false, false), (false, false), _, _, _, _, _ => rfl
  | (false, false), (true,  false), _, _, _, _, _ => rfl
  | (false, false), (false, true ), _, _, _, _, _ => rfl
  | (false, false), (true,  true ), _, _, _, _, _ => rfl
  | (true,  false), (false, false), _, _, _, _, _ => rfl
  | (false, true ), (false, false), _, _, _, _, _ => rfl
  | (true,  true ), (false, false), _, _, _, _, _ => rfl
  | (true,  false), (false, true ), _, _, _, _, _ => rfl
  | (false, true ), (true,  false), _, _, _, _, _ => rfl
  | (true,  false), (true,  false), hd, _, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (true,  false), (true,  true ), hd, _, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (false, true ), (false, true ), hd, _, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (false, true ), (true,  true ), hd, _, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (true,  true ), (true,  false), hd, _, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (true,  true ), (false, true ), hd, _, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (true,  true ), (true,  true ), hd, _, _, _, _ =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true

lemma bipartite_transProduct_one
    (n_A n_B : ℕ) :
    ∀ {a b : BipartiteSys} (hd : Disjoint a b),
      bipartiteTransProduct n_A n_B hd
          (1 : BipartiteTransSpace n_A n_B a)
          (1 : BipartiteTransSpace n_A n_B b)
        = (1 : BipartiteTransSpace n_A n_B (a ⊔ b))
  | (false, false), (false, false), _ => rfl
  | (false, false), (true,  false), _ => rfl
  | (false, false), (false, true ), _ => rfl
  | (false, false), (true,  true ), _ => rfl
  | (true,  false), (false, false), _ => rfl
  | (false, true ), (false, false), _ => rfl
  | (true,  true ), (false, false), _ => rfl
  | (true,  false), (false, true ), _ => rfl
  | (false, true ), (true,  false), _ => rfl
  | (true,  false), (true,  false), hd =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (true,  false), (true,  true ), hd =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (false, true ), (false, true ), hd =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (false, true ), (true,  true ), hd =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (true,  true ), (true,  false), hd =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true
  | (true,  true ), (false, true ), hd =>
      absurd (Prod.disjoint_iff.mp hd).2 not_disjoint_true_true
  | (true,  true ), (true,  true ), hd =>
      absurd (Prod.disjoint_iff.mp hd).1 not_disjoint_true_true

/-! ## 10.  The bipartite `NoSignallingTheory` instance (conditional on the core). -/

/-- **Bipartite phase-quotient unitary quantum theory** as a
    `NoSignallingTheory`, given the bipartite analytic core. -/
noncomputable def bipartiteUnitaryQuantumNoSignalling
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B) :
    NoSignallingTheory where
  Sys := BipartiteSys
  latticeSys := inferInstance
  Phenomenal := BipartitePhenomenalSpace n_A n_B
  phenomenal_nonempty := instPhenomNonempty_bipartite n_A n_B
  Trans := BipartiteTransSpace n_A n_B
  monoidTrans := instMonoidBipartiteTrans n_A n_B
  phenomenalAction := bipartitePhenomenalAction n_A n_B
  phenomenalProj := fun {_ _} h => bipartitePhenomenalProj n_A n_B h
  phenomenalProj_surjective :=
    fun {_ _} h => bipartitePhenomenalProj_surjective_of_core n_A n_B hCore h
  phenomenalProj_comp := fun {_ _ _} hab hbc =>
    bipartitePhenomenalProj_comp n_A n_B hab hbc
  transProduct := fun {_ _} hd => bipartiteTransProduct n_A n_B hd
  no_signalling := fun {_ _} hd => bipartite_no_signalling n_A n_B hCore hd
  no_signalling_right := fun {_ _} hd =>
    bipartite_no_signalling_right n_A n_B hCore hd
  transProduct_mul := fun {_ _} hd =>
    bipartite_transProduct_mul n_A n_B hd
  transProduct_one := fun {_ _} hd =>
    bipartite_transProduct_one n_A n_B hd

/-! ## 11.  Invertible dynamics for the bipartite theory. -/

theorem bipartite_invertibleDynamics
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B) :
    (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).InvertibleDynamics := by
  intro s U
  obtain ⟨V, hVU, hUV⟩ := bipartiteInvPair n_A n_B U
  exact ⟨V, hVU, hUV⟩

/-! ## 12.  The headline theorem (conditional on the core + the
        standard five-postulate bundle). -/

/-- **Bipartite full-postulates bundle.** -/
def BipartiteFullPostulates
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B) : Prop :=
  HardDirection.FullPostulates
    (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore)

/-- **THE BIPARTITE CONDITIONAL HEADLINE.**

    Bipartite phase-quotient unitary quantum mechanics admits a
    local-realistic model in the Raymond-Robichaud sense, modulo
    (i) the bipartite analytic core
    `BipartiteNoSignallingAnalyticCore n_A n_B` (the deep
    Kronecker-partial-trace identities and partial-trace surjectivity),
    and (ii) the **bundle** of the standard five postulates for the
    resulting `NoSignallingTheory` (which are verifiable
    case-by-case from the bipartite structure, just as in the
    single-system case). -/
theorem bipartiteUnitaryQM_has_localRealisticModel_of_core
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B)
    (hPost : BipartiteFullPostulates n_A n_B hCore) :
    ∃ L : LocalRealisticTheory,
      L.IsNoSignallingShadow
        (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore) :=
  NoSignallingTheory.hasLocalRealisticModelStrong_holds _ hPost

/-! ## 13.  Diagnostic checks. -/

noncomputable example (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B) :
    NoSignallingTheory :=
  bipartiteUnitaryQuantumNoSignalling n_A n_B hCore

example (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : BipartiteNoSignallingAnalyticCore n_A n_B) :
    (bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).InvertibleDynamics :=
  bipartite_invertibleDynamics n_A n_B hCore

end UnifiedTheory.LayerC.LocalRealisticAxioms
