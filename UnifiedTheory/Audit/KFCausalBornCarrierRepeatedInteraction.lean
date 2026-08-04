/-
  Audit/KFCausalBornCarrierRepeatedInteraction.lean

  FRESH-BATH COLLISIONS ON THE FULL CAUSAL BORN CARRIER

  The scalar bath construction is lifted here to an arbitrary real carrier.
  A rotation acts simultaneously on a system carrier vector and one bath
  carrier vector.  It is invertible when its coefficients lie on the unit
  circle, and a vacuum bath reduces the system defect by the prescribed
  retention.  Iteration with fresh vacuum modes therefore gives the exact
  carrier-valued defect semigroup and conserves system plus accumulated bath
  defect energy.

  For a fixed nonzero causal amplitude, apply the collision law to its defect
  from the canonical radial Born-shell point.  The reduced system trajectory
  is exactly the already proved `bornRadialRelaxation`, and on a physical
  successor support it is exactly the centered vector of the full relaxed
  causal amplitude.

  The qualifier "fixed" is essential.  The equilibrium shell point depends
  on the input ray, so this is a ray-conditioned repeated-interaction model,
  not a universal state-independent CPTP instrument.  The existing linear
  no-go remains in force.  A protected auxiliary label is unchanged only
  because the product factorization is explicitly supplied here; causal
  growth still has to derive that factorization and the fresh bath modes.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalBornAutonomousDilationNoGo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornCarrierRepeatedInteraction

noncomputable section

open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornShellRelaxationDynamics
open UnifiedTheory.Audit.KFCausalBornRateAndDilation

universe u v

/-! ## 1. Reversible rotation on a full real carrier -/

/-- A plane rotation whose two coordinates are vectors in the same real
carrier. -/
def carrierBathRotation
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (cosine sine : ℝ) (state : E × E) : E × E :=
  (cosine • state.1 + sine • state.2,
    (-sine) • state.1 + cosine • state.2)

/-- Reversing the carrier-bath angle exactly inverts the coupling. -/
theorem carrierBathRotation_inverse
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (cosine sine : ℝ) (hCircle : cosine ^ 2 + sine ^ 2 = 1)
    (state : E × E) :
    carrierBathRotation cosine (-sine)
        (carrierBathRotation cosine sine state) = state := by
  apply Prod.ext
  · simp only [carrierBathRotation, neg_neg]
    conv_rhs => rw [← one_smul ℝ state.1]
    conv_rhs => rw [← hCircle]
    module
  · simp only [carrierBathRotation, neg_neg]
    have hCircle' : sine ^ 2 + cosine ^ 2 = 1 := by
      simpa [add_comm] using hCircle
    conv_rhs => rw [← one_smul ℝ state.2]
    conv_rhs => rw [← hCircle']
    module

/-- Reduced carrier defect after collision with one fresh vacuum mode. -/
def carrierBathReducedDefect
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (retention : ℝ) (defect : E) : E :=
  (carrierBathRotation retention (bornBathLeakage retention)
    (defect, 0)).1

@[simp]
theorem carrierBathReducedDefect_eq
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (retention : ℝ) (defect : E) :
    carrierBathReducedDefect retention defect = retention • defect := by
  simp [carrierBathReducedDefect, carrierBathRotation]

/-- Carrier defect after a sequence of independent vacuum-bath collisions. -/
def iteratedCarrierBathDefect
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (retention : ℝ) (initial : E) : ℕ → E
  | 0 => initial
  | step + 1 =>
      carrierBathReducedDefect retention
        (iteratedCarrierBathDefect retention initial step)

theorem iteratedCarrierBathDefect_closed
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (retention : ℝ) (initial : E) (step : ℕ) :
    iteratedCarrierBathDefect retention initial step =
      (retention ^ step) • initial := by
  induction step with
  | zero => simp [iteratedCarrierBathDefect]
  | succ step ih =>
      rw [iteratedCarrierBathDefect, carrierBathReducedDefect_eq, ih,
        smul_smul, pow_succ]
      ring

/-- Accumulated squared defect norm exported into independent bath modes. -/
def accumulatedCarrierBathEnergy
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (retention : ℝ) (initial : E) : ℕ → ℝ
  | 0 => 0
  | step + 1 =>
      accumulatedCarrierBathEnergy retention initial step +
        bornBathLeakage retention ^ 2 *
          ‖iteratedCarrierBathDefect retention initial step‖ ^ 2

/-- Every collision moves the missing system defect energy into its fresh
bath mode.  System plus all previous bath records is exactly conserved. -/
theorem freshCarrierBath_total_energy
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (retention : ℝ) (initial : E)
    (hRetentionZero : 0 ≤ retention) (hRetentionOne : retention ≤ 1) :
    ∀ step,
      ‖iteratedCarrierBathDefect retention initial step‖ ^ 2 +
          accumulatedCarrierBathEnergy retention initial step =
        ‖initial‖ ^ 2 := by
  intro step
  induction step with
  | zero => simp [iteratedCarrierBathDefect, accumulatedCarrierBathEnergy]
  | succ step ih =>
      rw [iteratedCarrierBathDefect, carrierBathReducedDefect_eq,
        accumulatedCarrierBathEnergy, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hRetentionZero,
        bornBathLeakage_sq retention hRetentionZero hRetentionOne]
      nlinarith [sq_nonneg ‖iteratedCarrierBathDefect retention initial step‖]

/-! ## 2. Fixed-ray realization of the Born carrier trajectory -/

/-- Defect of a carrier state from the canonical point on its own Born-shell
ray. -/
def rayConditionedBornDefect
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : ℝ) (centered : E) : E :=
  centered - canonicalRadialShellPoint target centered

/-- Reduced carrier state after repeated fresh-bath collisions around the
fixed shell point selected by the initial ray. -/
def rayConditionedCarrierBathTrajectory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : ℝ) (centered : E) (step : ℕ) : E :=
  canonicalRadialShellPoint target centered +
    iteratedCarrierBathDefect (1 / 2)
      (rayConditionedBornDefect target centered) step

/-- The full-carrier fresh-bath construction is exactly the discrete Born
radial relaxation on every fixed nonzero input ray. -/
theorem rayConditionedCarrierBathTrajectory_eq_bornRadialRelaxation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : ℝ) (centered : E) (step : ℕ)
    (hCentered : centered ≠ 0) :
    rayConditionedCarrierBathTrajectory target centered step =
      bornRadialRelaxation target centered step := by
  rw [rayConditionedCarrierBathTrajectory,
    iteratedCarrierBathDefect_closed]
  unfold rayConditionedBornDefect canonicalRadialShellPoint
    bornRadialRelaxation
  rw [bornRadialRadius_closed]
  have hNorm : ‖centered‖ ≠ 0 := norm_ne_zero_iff.mpr hCentered
  have hScale :
      target / ‖centered‖ +
          (1 / 2 : ℝ) ^ step * (1 - target / ‖centered‖) =
        (target + (1 / 2 : ℝ) ^ step * (‖centered‖ - target)) /
          ‖centered‖ := by
    field_simp [hNorm]
  rw [← hScale]
  module

/-- The collision trajectory is equivariant under every real linear
isometry, so it does not depend on carrier coordinates or sheet labels. -/
theorem rayConditionedCarrierBathTrajectory_equivariant
    {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (equiv : E ≃ₗᵢ[ℝ] F) (target : ℝ) (centered : E) (step : ℕ) :
    equiv (rayConditionedCarrierBathTrajectory target centered step) =
      rayConditionedCarrierBathTrajectory target (equiv centered) step := by
  by_cases hCentered : centered = 0
  · subst centered
    simp [rayConditionedCarrierBathTrajectory, rayConditionedBornDefect,
      canonicalRadialShellPoint, iteratedCarrierBathDefect_closed]
  · rw [rayConditionedCarrierBathTrajectory_eq_bornRadialRelaxation
        target centered step hCentered,
      bornRadialRelaxation_equivariant]
    exact (rayConditionedCarrierBathTrajectory_eq_bornRadialRelaxation
      target (equiv centered) step (equiv.map_ne_zero_iff.mpr hCentered)).symm

/-! ## 3. The actual causal successor carrier -/

/-- Fresh-bath trajectory on the physical zero-sum successor carrier. -/
def supportCarrierBathTrajectory
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) (step : ℕ) :
    EuclideanSpace ℂ {branch : Branch // branch ∈ support} :=
  rayConditionedCarrierBathTrajectory (supportBornTargetRadius support)
    (supportCenteredVector support amplitude) step

/-- On every nonuniform physical successor law, fresh carrier-bath collisions
recover exactly the established causal Born relaxation. -/
theorem supportCarrierBathTrajectory_eq_supportBornRelaxation
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) (step : ℕ)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support) :
    supportCarrierBathTrajectory support amplitude step =
      supportBornRelaxation support amplitude step := by
  exact rayConditionedCarrierBathTrajectory_eq_bornRadialRelaxation
    _ _ step (supportCenteredVector_ne_zero_of_nonuniform
      support amplitude hNonuniform)

/-- The system component of the collision construction is exactly the
centered vector of the full supported causal amplitude at that tick. -/
theorem supportCarrierBathTrajectory_eq_relaxedAmplitude
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) (step : ℕ)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support) :
    supportCarrierBathTrajectory support amplitude step =
      supportCenteredVector support
        (finiteSupportBornRelaxedAmplitude support amplitude step) := by
  rw [supportCarrierBathTrajectory_eq_supportBornRelaxation
      support amplitude step hNonuniform,
    supportCenteredVector_relaxedAmplitude]

/-! ## 4. Explicitly protected labels and the factorization boundary -/

/-- A supplied auxiliary label can be carried alongside the collision and is
left untouched.  This is the exact mathematical form of a protected sector;
the product factorization itself is data, not a consequence of this theorem. -/
def protectedCarrierBathRotation
    {Label : Type v} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (cosine sine : ℝ) (state : Label × (E × E)) : Label × (E × E) :=
  (state.1, carrierBathRotation cosine sine state.2)

@[simp]
theorem protectedCarrierBathRotation_label
    {Label : Type v} {E : Type u} [AddCommGroup E] [Module ℝ E]
    (cosine sine : ℝ) (state : Label × (E × E)) :
    (protectedCarrierBathRotation cosine sine state).1 = state.1 := rfl

/-- The earlier homogeneity obstruction still excludes interpreting this
fixed-ray construction as one universal linear evolution on all inputs. -/
theorem no_universal_linear_Born_carrier_collision
    (target : ℝ) (hTarget : target ≠ 0) :
    ¬ ∃ evolution : ℝ →ₗ[ℝ] ℝ,
      ∀ centered : ℝ, centered ≠ 0 →
        evolution centered =
          rayConditionedCarrierBathTrajectory target centered 1 := by
  intro hEvolution
  apply no_linear_operator_realizes_universal_Born_relaxation target hTarget
  obtain ⟨evolution, hEvolution⟩ := hEvolution
  refine ⟨evolution, ?_⟩
  intro centered hCentered
  rw [hEvolution centered hCentered,
    rayConditionedCarrierBathTrajectory_eq_bornRadialRelaxation
      target centered 1 hCentered]

/-! ## Axiom audit -/

#print axioms carrierBathRotation_inverse
#print axioms freshCarrierBath_total_energy
#print axioms rayConditionedCarrierBathTrajectory_eq_bornRadialRelaxation
#print axioms supportCarrierBathTrajectory_eq_relaxedAmplitude
#print axioms protectedCarrierBathRotation_label
#print axioms no_universal_linear_Born_carrier_collision

end

end UnifiedTheory.Audit.KFCausalBornCarrierRepeatedInteraction
