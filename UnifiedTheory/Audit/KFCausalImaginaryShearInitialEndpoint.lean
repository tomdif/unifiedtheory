/- The actual initial interpolation endpoint is a bounded clock operator
on the existing coherent state. Frequency-dependent operators are kept
separate before the finite superposition is formed. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearInitialMultiplier
import UnifiedTheory.Audit.KFCausalClockFloorCoherentParameters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalImaginaryShearInitialEndpoint
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalImaginaryShearInitialMultiplier
open UnifiedTheory.Audit.KFCausalBoundedClockCharge
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state action_state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant clockFrequency sourceCoefficients dampedState)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (gaussianState dampedState_eq)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoherentBridge (coherentSeed)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)

variable (ε a p h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3)

def modifierOperator : Hilbert →L[ℂ] Hilbert := multiplier (modifier ε a p h)
  (modifier_smooth ε a p h hε hb).continuous.measurable (bound a p h) (Real.exp_pos _).le
  (fun s => modifier_bound ε a p h s hε hb)
def initialOperator : Hilbert →L[ℂ] Hilbert := multiplier (symbol ε a p h)
  (symbol_smooth ε a p h hε hb).continuous.measurable (symbolBound ε a p h)
  (symbolBound_nonnegative ε a p h) (fun s => symbol_bound ε a p h s hε hb)

theorem modifierOperator_coe (f : Hilbert) : modifierOperator ε a p h hε hb f =ᵐ[volume]
    fun x => modifier ε a p h x.1*f x := multiplier_coe _ _ _ _ _ f
theorem initialOperator_coe (f : Hilbert) : initialOperator ε a p h hε hb f =ᵐ[volume]
    fun x => symbol ε a p h x.1*f x := multiplier_coe _ _ _ _ _ f

theorem initialOperator_coordinates (f : Hilbert) :
    KFCausalPhysicalCircleAction.chargeCoordinates (initialOperator ε a p h hε hb f) =ᵐ[volume]
      fun x => symbol ε a p h (x (.inr 0))*KFCausalPhysicalCircleAction.chargeCoordinates f x :=
  multiplier_coordinates _ _ _ _ _ f

theorem initialOperator_charge (hh : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    initialOperator ε a p h hε hb (action h hh θ f) = action h hh θ (initialOperator ε a p h hε hb f) :=
  multiplier_charge _ _ _ _ _ h hh θ f

theorem initialOperator_inverse (f : Hilbert) : initialOperator ε a p h hε hb f =
    modifierOperator ε a p h hε hb (KFCausalClockFloorClockHalf.inverseAction ε hε f) := by
  apply Lp.ext
  filter_upwards [initialOperator_coe ε a p h hε hb f,
    modifierOperator_coe ε a p h hε hb (KFCausalClockFloorClockHalf.inverseAction ε hε f),
    KFCausalClockFloorClockHalf.inverseAction_coe ε hε f] with x hi hm hf
  rw [hi,hm,hf]
  unfold symbol
  ring

theorem input_zero_eq (α β : ℝ) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (b : Fin 5 → ℂ) :
    KFCausalActualImaginaryShearCurve.input ε a p h α β hε ha hα hβ hw hb b 0 =
      modifierOperator ε a p h hε hb (gaussianState ε a α β p b 0 hε ha hα hβ hw (by simp; positivity)) := by
  rw [KFCausalActualImaginaryShearCurve.input_eq_state ε a p h α β hε ha hα hβ hw hb b
    ⟨0,by constructor <;> norm_num⟩]
  apply Lp.ext
  filter_upwards [KFCausalImaginaryShearPathDomain.actualState_coe α β hα hβ hw b ε a p h hε ha hb
      ⟨0,by constructor <;> norm_num⟩,
    modifierOperator_coe ε a p h hε hb (gaussianState ε a α β p b 0 hε ha hα hβ hw (by simp; positivity)),
    KFCausalShiftedGaussianPhysicalProfile.gaussianState_profile ε a α β p 0 b hε ha hα hβ hw (by simp; positivity)]
    with x hf hm hg
  rw [hf,hm,hg]
  change KFCausalImaginaryShearInterpolation.path _ _ _ _ _ 0 x = _
  rw [KFCausalImaginaryShearInterpolation.path_zero]
  simp only [KFCausalRelativeGaussianDifferential.profile,scale_zero ε x.1 hε]
  rw [clock_amplitude_identity ε a p h x.1 hε]
  ring

omit p in
theorem coherent_zero (ha : 0 < a) (hh : h ≠ 0) (k : Joint 2 4) :
    amplitudeConstant h k • KFCausalActualImaginaryShearCurve.input ε a (clockFrequency k) h
      (groundWidth h) (neutralWidth h) hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh)
      (neutralWidth_bound h) hb (sourceCoefficients h k) 0 =
    initialOperator ε a (clockFrequency k) h hε hb (state ε a h hε ha hh k) := by
  rw [input_zero_eq,← map_smul,← dampedState_eq]
  exact (initialOperator_inverse ε a (clockFrequency k) h hε hb (state ε a h hε ha hh k)).symm

omit p in
theorem input_zero_sum (ha : 0 < a) (hh : h ≠ 0) {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ) :
    KFCausalImaginaryShearCoherentBridge.input ε a h hε ha hh hb k z 0 =
      ∑ i, z i • initialOperator ε a (clockFrequency (k i)) h hε hb (state ε a h hε ha hh (k i)) := by
  unfold KFCausalImaginaryShearCoherentBridge.input KFCausalImaginaryShearSuperposition.sumInput
  simp only [coherentSeed,← smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [coherent_zero ε a h hε hb ha hh (k i)]

omit p in
theorem initial_charge (ha : 0 < a) (hh : h ≠ 0) (θ : ℝ) {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ) :
    KFCausalImaginaryShearCoherentBridge.input ε a h hε ha hh hb (fun i => parameter θ (k i)) z 0 =
      action h hh θ (KFCausalImaginaryShearCoherentBridge.input ε a h hε ha hh hb k z 0) := by
  rw [input_zero_sum,input_zero_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,KFCausalClockFloorCoherentParameters.clockFrequency_parameter,← action_state,
    initialOperator_charge]

#print axioms modifierOperator_coe
#print axioms initialOperator_coe
#print axioms initialOperator_coordinates
#print axioms initialOperator_charge
#print axioms initialOperator_inverse
#print axioms input_zero_eq
#print axioms coherent_zero
#print axioms input_zero_sum
#print axioms initial_charge
end
end UnifiedTheory.Audit.KFCausalImaginaryShearInitialEndpoint
