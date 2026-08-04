/-
  Audit/KFCausalBornGrowthFreshModes.lean

  FRESH BATH MODES FROM SEQUENTIAL-GROWTH RANK

  The previous collision model used one fresh carrier-valued vacuum mode at
  every birth.  Here that mode tower is derived from structure already present
  in causal sequential growth:

  * a depth-n history contains exactly n birth slots;
  * a one-element extension embeds the old slots by `Fin.castSucc` and reserves
    `Fin.last n` for the newborn;
  * `Fin.last n` is the unique slot outside the image of every old slot;
  * the corresponding standard Hilbert basis vectors are orthonormal;
  * the recursive path representation itself factors the next history as old
    prefix times one new branch.

  Consequently the minimal record bath at depth n is the carrier-valued
  function space `Fin n -> E`.  A birth appends a zero mode at the unique new
  slot and rotates the system defect into that slot.  Old record modes are
  unchanged, the update is reversible on its image, and the exact norm of the
  full growing bath records all exported defect energy.  Iteration reproduces
  the established causal Born trajectory.

  What is derived is the fresh orthogonal mode *kinematics* from birth rank.
  The choice to couple the Born defect to that record tower, the rotation
  coefficient, and any protected tensor factor remain dynamical structure.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalBornCarrierRepeatedInteraction
import UnifiedTheory.Audit.KFCausalSetSequentialGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornGrowthFreshModes

noncomputable section

open scoped BigOperators InnerProductSpace
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornShellRelaxationDynamics
open UnifiedTheory.Audit.KFCausalBornRateAndDilation
open UnifiedTheory.Audit.KFCausalBornCarrierRepeatedInteraction
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth

universe u

/-! ## 1. Sequential growth supplies one canonical new slot -/

/-- Birth-record slots present after `depth` sequential births. -/
abbrev CausalBirthMode (depth : ℕ) := Fin depth

/-- The slot created by the next one-element birth.  This is the same final
coordinate used for the newborn in `IsLabeledOneElementExtension`. -/
def newbornCausalBirthMode (depth : ℕ) : CausalBirthMode (depth + 1) :=
  Fin.last depth

/-- No old birth slot is the newborn slot. -/
theorem newbornCausalBirthMode_ne_old (depth : ℕ)
    (old : CausalBirthMode depth) :
    newbornCausalBirthMode depth ≠ old.castSucc := by
  exact (Fin.castSucc_lt_last old).ne'

/-- Every enlarged mode is either an old slot or the unique newborn slot. -/
theorem causalBirthMode_old_or_new (depth : ℕ)
    (mode : CausalBirthMode (depth + 1)) :
    (∃ old : CausalBirthMode depth, mode = old.castSucc) ∨
      mode = newbornCausalBirthMode depth := by
  refine Fin.lastCases (Or.inr rfl) (fun old => Or.inl ⟨old, rfl⟩) mode

/-- The newborn is characterized intrinsically as the only enlarged slot not
coming from the old record carrier. -/
theorem eq_newbornCausalBirthMode_of_ne_old (depth : ℕ)
    (mode : CausalBirthMode (depth + 1))
    (hFresh : ∀ old : CausalBirthMode depth, mode ≠ old.castSucc) :
    mode = newbornCausalBirthMode depth := by
  rcases causalBirthMode_old_or_new depth mode with ⟨old, hOld⟩ | hNew
  · exact (hFresh old hOld).elim
  · exact hNew

/-- Every physical unlabeled one-element transition therefore comes with the
same unique process-time record slot.  This slot uses the rank, not a labeling
of the causal-set events. -/
theorem physicalCausalGrowthStep_has_unique_fresh_mode
    (depth : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch depth)
    (child : CausalSetGrowthBranch depth)
    (hPhysical : IsPhysicalCausalGrowthStep depth pathPrefix child) :
    IsPhysicalCausalGrowthStep depth pathPrefix child ∧
      ∃! mode : CausalBirthMode (depth + 1),
        ∀ old : CausalBirthMode depth, mode ≠ old.castSucc := by
  refine ⟨hPhysical, newbornCausalBirthMode depth, ?_, ?_⟩
  · exact newbornCausalBirthMode_ne_old depth
  · intro mode hMode
    exact eq_newbornCausalBirthMode_of_ne_old depth mode hMode

/-- The recursive ranked-history representation adds exactly one new branch
factor at the same step that the mode tower adds its new slot. -/
theorem rankedGrowthPath_succ_factorization
    (Branch : ℕ → Type u) (depth : ℕ) :
    RankedGrowthPath Branch (depth + 1) =
      (RankedGrowthPath Branch depth × Branch depth) := rfl

/-! ## 2. The birth slots are genuinely orthogonal modes -/

/-- Scalar Hilbert carrier of the birth clock at a fixed depth. -/
abbrev CausalBirthModeHilbert (depth : ℕ) :=
  EuclideanSpace ℝ (CausalBirthMode depth)

/-- Unit ket carried by one birth slot. -/
def causalBirthModeKet {depth : ℕ} (mode : CausalBirthMode depth) :
    CausalBirthModeHilbert depth :=
  EuclideanSpace.single mode 1

/-- The complete family of birth-slot kets is orthonormal. -/
theorem causalBirthModeKet_orthonormal (depth : ℕ) :
    Orthonormal ℝ
      (fun mode : CausalBirthMode depth => causalBirthModeKet mode) := by
  simpa [causalBirthModeKet] using
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ)
      (ι := CausalBirthMode depth))

/-- In particular the new birth mode is orthogonal to every prior mode after
the canonical old-slot embedding. -/
theorem newbornCausalBirthModeKet_orthogonal_old (depth : ℕ)
    (old : CausalBirthMode depth) :
    ⟪causalBirthModeKet (newbornCausalBirthMode depth),
        causalBirthModeKet (old.castSucc)⟫_ℝ = 0 := by
  unfold causalBirthModeKet
  rw [EuclideanSpace.inner_single_left]
  simp [newbornCausalBirthMode,
    (Fin.castSucc_lt_last old).ne']

/-- Every birth mode has unit norm. -/
theorem causalBirthModeKet_norm {depth : ℕ}
    (mode : CausalBirthMode depth) :
    ‖causalBirthModeKet mode‖ = 1 := by
  simp [causalBirthModeKet]

/-! ## 3. A growing carrier-valued bath with no reset -/

/-- Minimal carrier-valued record bath after `depth` births: one copy of the
system defect carrier for each process-time birth slot. -/
abbrev CausalGrowthBath (E : Type u) (depth : ℕ) :=
  CausalBirthMode depth → E

/-- Append one new record while preserving every old bath mode. -/
def appendCausalGrowthBathMode
    {E : Type u} {depth : ℕ}
    (oldBath : CausalGrowthBath E depth) (newRecord : E) :
    CausalGrowthBath E (depth + 1) :=
  Fin.lastCases newRecord oldBath

@[simp]
theorem appendCausalGrowthBathMode_newborn
    {E : Type u} {depth : ℕ}
    (oldBath : CausalGrowthBath E depth) (newRecord : E) :
    appendCausalGrowthBathMode oldBath newRecord
      (newbornCausalBirthMode depth) = newRecord := by
  simp [appendCausalGrowthBathMode, newbornCausalBirthMode]

@[simp]
theorem appendCausalGrowthBathMode_old
    {E : Type u} {depth : ℕ}
    (oldBath : CausalGrowthBath E depth) (newRecord : E)
    (old : CausalBirthMode depth) :
    appendCausalGrowthBathMode oldBath newRecord old.castSucc =
      oldBath old := by
  simp [appendCausalGrowthBathMode]

/-- Before the coupling, growth supplies the new slot in its vacuum state;
all earlier records remain present. -/
def appendFreshVacuumMode
    {E : Type u} [Zero E] {depth : ℕ}
    (oldBath : CausalGrowthBath E depth) :
    CausalGrowthBath E (depth + 1) :=
  appendCausalGrowthBathMode oldBath 0

@[simp]
theorem appendFreshVacuumMode_newborn
    {E : Type u} [Zero E] {depth : ℕ}
    (oldBath : CausalGrowthBath E depth) :
    appendFreshVacuumMode oldBath (newbornCausalBirthMode depth) = 0 := by
  simp [appendFreshVacuumMode]

@[simp]
theorem appendFreshVacuumMode_old
    {E : Type u} [Zero E] {depth : ℕ}
    (oldBath : CausalGrowthBath E depth) (old : CausalBirthMode depth) :
    appendFreshVacuumMode oldBath old.castSucc = oldBath old := by
  simp [appendFreshVacuumMode]

/-- Couple the system only to the slot created by the present birth.  Earlier
bath modes are records and are never reused. -/
def causalGrowthFreshModeCollision
    {E : Type u} [AddCommGroup E] [Module ℝ E] {depth : ℕ}
    (cosine sine : ℝ) (state : E × CausalGrowthBath E depth) :
    E × CausalGrowthBath E (depth + 1) :=
  let rotated := carrierBathRotation cosine sine (state.1, 0)
  (rotated.1, appendCausalGrowthBathMode state.2 rotated.2)

@[simp]
theorem causalGrowthFreshModeCollision_system
    {E : Type u} [AddCommGroup E] [Module ℝ E] {depth : ℕ}
    (cosine sine : ℝ) (state : E × CausalGrowthBath E depth) :
    (causalGrowthFreshModeCollision cosine sine state).1 =
      cosine • state.1 := by
  simp [causalGrowthFreshModeCollision, carrierBathRotation]

@[simp]
theorem causalGrowthFreshModeCollision_old_record
    {E : Type u} [AddCommGroup E] [Module ℝ E] {depth : ℕ}
    (cosine sine : ℝ) (state : E × CausalGrowthBath E depth)
    (old : CausalBirthMode depth) :
    (causalGrowthFreshModeCollision cosine sine state).2 old.castSucc =
      state.2 old := by
  simp [causalGrowthFreshModeCollision]

@[simp]
theorem causalGrowthFreshModeCollision_new_record
    {E : Type u} [AddCommGroup E] [Module ℝ E] {depth : ℕ}
    (cosine sine : ℝ) (state : E × CausalGrowthBath E depth) :
    (causalGrowthFreshModeCollision cosine sine state).2
        (newbornCausalBirthMode depth) =
      (-sine) • state.1 := by
  simp [causalGrowthFreshModeCollision, carrierBathRotation]

/-- Read back the old system and bath from a state in the image of one fresh
collision.  The newest record supplies the second rotation coordinate. -/
def undoCausalGrowthFreshModeCollision
    {E : Type u} [AddCommGroup E] [Module ℝ E] {depth : ℕ}
    (cosine sine : ℝ) (state : E × CausalGrowthBath E (depth + 1)) :
    E × CausalGrowthBath E depth :=
  ((carrierBathRotation cosine (-sine)
      (state.1, state.2 (newbornCausalBirthMode depth))).1,
    fun old => state.2 old.castSucc)

/-- A growth collision loses no information on its image.  Irreversibility
appears only after the growing record bath is discarded. -/
theorem undoCausalGrowthFreshModeCollision_apply
    {E : Type u} [AddCommGroup E] [Module ℝ E] {depth : ℕ}
    (cosine sine : ℝ) (hCircle : cosine ^ 2 + sine ^ 2 = 1)
    (state : E × CausalGrowthBath E depth) :
    undoCausalGrowthFreshModeCollision cosine sine
      (causalGrowthFreshModeCollision cosine sine state) = state := by
  rcases state with ⟨system, oldBath⟩
  apply Prod.ext
  · have hInverse := congrArg Prod.fst
      (carrierBathRotation_inverse cosine sine hCircle (system, 0))
    simpa [undoCausalGrowthFreshModeCollision,
      causalGrowthFreshModeCollision, appendCausalGrowthBathMode,
      newbornCausalBirthMode] using hInverse
  · funext old
    simp [undoCausalGrowthFreshModeCollision,
      causalGrowthFreshModeCollision, appendCausalGrowthBathMode]

/-! ## 4. The growing bath stores the exact exported energy -/

/-- Squared norm of all carrier records written so far. -/
def causalGrowthBathEnergy
    {E : Type u} [NormedAddCommGroup E] (depth : ℕ)
    (bath : CausalGrowthBath E depth) : ℝ :=
  ∑ mode, ‖bath mode‖ ^ 2

/-- Appending one record adds precisely its squared norm to bath energy. -/
theorem causalGrowthBathEnergy_append
    {E : Type u} [NormedAddCommGroup E] {depth : ℕ}
    (oldBath : CausalGrowthBath E depth) (newRecord : E) :
    causalGrowthBathEnergy (depth + 1)
        (appendCausalGrowthBathMode oldBath newRecord) =
      causalGrowthBathEnergy depth oldBath + ‖newRecord‖ ^ 2 := by
  classical
  unfold causalGrowthBathEnergy
  rw [Fin.sum_univ_castSucc]
  simp [appendCausalGrowthBathMode]

/-- One growth-created mode collision exactly conserves system plus complete
record-bath energy. -/
theorem causalGrowthFreshModeCollision_total_energy
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {depth : ℕ}
    (cosine sine : ℝ) (hCircle : cosine ^ 2 + sine ^ 2 = 1)
    (state : E × CausalGrowthBath E depth) :
    ‖(causalGrowthFreshModeCollision cosine sine state).1‖ ^ 2 +
        causalGrowthBathEnergy (depth + 1)
          (causalGrowthFreshModeCollision cosine sine state).2 =
      ‖state.1‖ ^ 2 + causalGrowthBathEnergy depth state.2 := by
  simp only [causalGrowthFreshModeCollision, carrierBathRotation,
    add_zero, smul_zero]
  rw [causalGrowthBathEnergy_append]
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, mul_pow, sq_abs]
  nlinarith [sq_nonneg ‖state.1‖]

/-! ## 5. Iteration along the causal birth clock -/

/-- System plus its complete growth-created bath after finitely many births. -/
def causalGrowthFreshModeTrajectory
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (cosine sine : ℝ) (initial : E) :
    ∀ depth : ℕ, E × CausalGrowthBath E depth
  | 0 => (initial, fun mode => Fin.elim0 mode)
  | depth + 1 =>
      causalGrowthFreshModeCollision cosine sine
        (causalGrowthFreshModeTrajectory cosine sine initial depth)

@[simp]
theorem causalGrowthFreshModeTrajectory_zero
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (cosine sine : ℝ) (initial : E) :
    causalGrowthFreshModeTrajectory cosine sine initial 0 =
      (initial, fun mode => Fin.elim0 mode) := rfl

@[simp]
theorem causalGrowthFreshModeTrajectory_succ
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (cosine sine : ℝ) (initial : E) (depth : ℕ) :
    causalGrowthFreshModeTrajectory cosine sine initial (depth + 1) =
      causalGrowthFreshModeCollision cosine sine
        (causalGrowthFreshModeTrajectory cosine sine initial depth) := rfl

/-- The reduced system follows the exact multiplicative defect semigroup. -/
theorem causalGrowthFreshModeTrajectory_system
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (cosine sine : ℝ) (initial : E) :
    ∀ depth : ℕ,
      (causalGrowthFreshModeTrajectory cosine sine initial depth).1 =
        (cosine ^ depth) • initial
  | 0 => by simp
  | depth + 1 => by
      rw [causalGrowthFreshModeTrajectory_succ,
        causalGrowthFreshModeCollision_system,
        causalGrowthFreshModeTrajectory_system]
      simp [smul_smul, pow_succ, mul_comm]

/-- The mode born at clock index `k` permanently stores the defect leaked at
that birth.  Its value is unchanged by every later collision. -/
theorem causalGrowthFreshModeTrajectory_record
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (cosine sine : ℝ) (initial : E) :
    ∀ (depth : ℕ) (mode : CausalBirthMode depth),
      (causalGrowthFreshModeTrajectory cosine sine initial depth).2 mode =
        ((-sine) * cosine ^ mode.val) • initial
  | 0, mode => Fin.elim0 mode
  | depth + 1, mode => by
      refine Fin.lastCases ?_ (fun old => ?_) mode
      · change
          (causalGrowthFreshModeCollision cosine sine
            (causalGrowthFreshModeTrajectory cosine sine initial depth)).2
              (newbornCausalBirthMode depth) =
            ((-sine) * cosine ^ depth) • initial
        rw [causalGrowthFreshModeCollision_new_record,
          causalGrowthFreshModeTrajectory_system]
        simp [smul_smul]
      · rw [causalGrowthFreshModeTrajectory_succ,
          causalGrowthFreshModeCollision_old_record,
          causalGrowthFreshModeTrajectory_record]
        rfl

/-- The growing bath, unlike the reduced system, retains exact total energy at
every depth. -/
theorem causalGrowthFreshModeTrajectory_total_energy
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (cosine sine : ℝ) (hCircle : cosine ^ 2 + sine ^ 2 = 1)
    (initial : E) : ∀ depth : ℕ,
    ‖(causalGrowthFreshModeTrajectory cosine sine initial depth).1‖ ^ 2 +
        causalGrowthBathEnergy depth
          (causalGrowthFreshModeTrajectory cosine sine initial depth).2 =
      ‖initial‖ ^ 2
  | 0 => by simp [causalGrowthBathEnergy]
  | depth + 1 => by
      rw [causalGrowthFreshModeTrajectory_succ,
        causalGrowthFreshModeCollision_total_energy cosine sine hCircle]
      exact causalGrowthFreshModeTrajectory_total_energy cosine sine hCircle
        initial depth

/-- For the causal half-defect law, the birth-indexed bath tower is exactly
the earlier abstract fresh-collision system trajectory. -/
theorem causalHalfGrowthFreshModeTrajectory_system_eq_iterated
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (initial : E) (depth : ℕ) :
    (causalGrowthFreshModeTrajectory (1 / 2) (bornBathLeakage (1 / 2))
        initial depth).1 =
      iteratedCarrierBathDefect (1 / 2) initial depth := by
  rw [causalGrowthFreshModeTrajectory_system,
    iteratedCarrierBathDefect_closed]

/-! ## 6. Exact causal Born trajectory and honest boundary -/

/-- Born trajectory whose environment modes are indexed by the actual causal
birth clock rather than supplied as an external list. -/
def growthDerivedRayBornTrajectory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : ℝ) (centered : E) (depth : ℕ) : E :=
  canonicalRadialShellPoint target centered +
    (causalGrowthFreshModeTrajectory (1 / 2)
      (bornBathLeakage (1 / 2))
      (rayConditionedBornDefect target centered) depth).1

/-- The growth-indexed collision construction reproduces the established
Born relaxation on every fixed nonzero ray. -/
theorem growthDerivedRayBornTrajectory_eq_bornRadialRelaxation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : ℝ) (centered : E) (depth : ℕ)
    (hCentered : centered ≠ 0) :
    growthDerivedRayBornTrajectory target centered depth =
      bornRadialRelaxation target centered depth := by
  rw [growthDerivedRayBornTrajectory,
    causalHalfGrowthFreshModeTrajectory_system_eq_iterated]
  exact rayConditionedCarrierBathTrajectory_eq_bornRadialRelaxation
    target centered depth hCentered

/-- On the actual physical-successor carrier this is the centered vector of
the full causal Born-relaxed amplitude. -/
theorem growthDerivedSupportBornTrajectory_eq_relaxedAmplitude
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) (depth : ℕ)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support) :
    growthDerivedRayBornTrajectory (supportBornTargetRadius support)
        (supportCenteredVector support amplitude) depth =
      supportCenteredVector support
        (finiteSupportBornRelaxedAmplitude support amplitude depth) := by
  rw [growthDerivedRayBornTrajectory_eq_bornRadialRelaxation _ _ depth
      (supportCenteredVector_ne_zero_of_nonuniform
        support amplitude hNonuniform),
    supportCenteredVector_relaxedAmplitude]
  rfl

/-- Fresh-mode kinematics is derived, but the state-dependent shell target
still forbids a universal linear Born collision law. -/
theorem growth_fresh_modes_do_not_remove_universal_linearity_noGo
    (target : ℝ) (hTarget : target ≠ 0) :
    ¬ ∃ evolution : ℝ →ₗ[ℝ] ℝ,
      ∀ centered : ℝ, centered ≠ 0 →
        evolution centered =
          growthDerivedRayBornTrajectory target centered 1 := by
  intro hEvolution
  apply no_linear_operator_realizes_universal_Born_relaxation target hTarget
  obtain ⟨evolution, hEvolution⟩ := hEvolution
  refine ⟨evolution, ?_⟩
  intro centered hCentered
  rw [hEvolution centered hCentered,
    growthDerivedRayBornTrajectory_eq_bornRadialRelaxation
      target centered 1 hCentered]

/-! ## Axiom audit -/

#print axioms physicalCausalGrowthStep_has_unique_fresh_mode
#print axioms causalBirthModeKet_orthonormal
#print axioms newbornCausalBirthModeKet_orthogonal_old
#print axioms undoCausalGrowthFreshModeCollision_apply
#print axioms causalGrowthFreshModeTrajectory_record
#print axioms causalGrowthFreshModeTrajectory_total_energy
#print axioms growthDerivedRayBornTrajectory_eq_bornRadialRelaxation
#print axioms growthDerivedSupportBornTrajectory_eq_relaxedAmplitude
#print axioms growth_fresh_modes_do_not_remove_universal_linearity_noGo

end

end UnifiedTheory.Audit.KFCausalBornGrowthFreshModes
