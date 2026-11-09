/- A bounded-operator formulation of a necessary translation identity for
states with a fixed neutral Gaussian factor. Its kernel is Hilbert closed;
no claim that this one identity characterizes that factor is needed. -/
import UnifiedTheory.Audit.KFCausalReciprocalStrongCommutator
import UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates
import UnifiedTheory.Audit.KFCausalUnboundedNeutralCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralGaussianConstraint
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalNeutralTranslationCoordinates (action action_coe vector)
open KFCausalUnboundedNeutralCharge
open KFCausalNeutralMultiplierCharge (multiplier)
open KFCausalReciprocalGaussianStates (configurationDensity quadratic)
open KFCausalClockFloorInvariantTrial (neutralWidth clockFunction)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def ratio (β : ℝ) (x : ℝ) : ℂ := Complex.exp (-((β*(2*x+1):ℝ):ℂ))

theorem ratio_continuous (β : ℝ) : Continuous (ratio β) := by
  unfold ratio
  fun_prop

def defect (β : ℝ) : Hilbert →L[ℂ] Hilbert :=
  (multiplier (reciprocal (ratio β)) (reciprocal_measurable _ (ratio_continuous β).measurable)
    (reciprocal_bound _)).comp (action 1 : Hilbert →L[ℂ] Hilbert) -
  multiplier (normalized (ratio β)) (normalized_measurable _ (ratio_continuous β).measurable)
    (normalized_bound _)

def constrained (β : ℝ) : Submodule ℂ Hilbert := (defect β).ker

theorem mem_constrained (β : ℝ) (f : Hilbert) :
    f ∈ constrained β ↔ relation (ratio β) f (action 1 f) := by
  rw [relation_iff_bounded _ (ratio_continuous β).measurable]
  change (defect β) f = 0 ↔ _
  simp only [defect,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,sub_eq_zero]
  rfl

theorem constrained_closed (β : ℝ) : IsClosed (constrained β : Set Hilbert) :=
  (defect β).isClosed_ker

theorem quadratic_shift (w : ℝ) (x : Configuration) :
    quadratic w (x+vector 1).2 = quadratic w x.2 := by
  simp [quadratic,KFCausalQuarticChargeProfiles.chargedRadius,
    KFCausalChargedPairCoordinates.pairPolynomial,vector]

theorem density_translation (α β w : ℝ) (g : ℝ → ℂ) (x : Configuration) :
    configurationDensity α β w g (x+vector 1) =
      ratio β (x.2 4)*configurationDensity α β w g x := by
  unfold configurationDensity
  rw [quadratic_shift]
  have h4 : (x+vector 1).2 4 = x.2 4+1 := by simp [vector]
  have h0 : (x+vector 1).1 = x.1 := by simp [vector]
  rw [h4,h0]
  unfold ratio
  rw [show -((α*quadratic w x.2+β*(x.2 4+1)^2:ℝ):ℂ) =
    -((β*(2*x.2 4+1):ℝ):ℂ) + -((α*quadratic w x.2+β*(x.2 4)^2:ℝ):ℂ) by push_cast; ring,
    Complex.exp_add]
  ring

theorem reciprocal_packet_constrained (ε a h w : ℝ) (hε : 0 < ε)
    (ha : 0 < a) (hh : h ≠ 0) (hw : 0 < w) :
    KFCausalReciprocalGaussianCharge.state ε a h w hε ha hh hw ∈ constrained (neutralWidth h) := by
  apply (mem_constrained _ _).mpr
  filter_upwards [action_coe 1 (KFCausalReciprocalGaussianCharge.state ε a h w hε ha hh hw),
    (KFCausalLpPhaseTranslation.shift_preserves volume (vector 1)).quasiMeasurePreserving.ae
      (KFCausalReciprocalGaussianCharge.state_configuration_coe ε a h w hε ha hh hw),
    KFCausalReciprocalGaussianCharge.state_configuration_coe ε a h w hε ha hh hw] with x ht hs hf
  change KFCausalReciprocalGaussianCharge.state ε a h w hε ha hh hw (x+vector 1) = _ at hs
  rw [ht,hs,hf]
  exact density_translation _ _ _ _ x

theorem reciprocal_sum_constrained (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) :
    KFCausalReciprocalSuperpositionFactors.state n ε h a w c hε ha hh hw ∈ constrained (neutralWidth h) :=
  (constrained _).sum_mem fun i _ => (constrained _).smul_mem (c i)
    (reciprocal_packet_constrained ε (a i) h (w i) hε (ha i) hh (by have := hw i; linarith))

def reciprocalStates (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) : Set Hilbert :=
  {f | ∃ (n : ℕ) (a w : Fin n → ℝ) (c : Fin n → ℂ) (ha : ∀ i, 0 < a i)
    (hw : ∀ i, 1 ≤ w i), f = KFCausalReciprocalSuperpositionFactors.state n ε h a w c hε ha hh hw}

theorem reciprocalClosure_constrained (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) :
    closure (reciprocalStates ε h hε hh) ⊆ constrained (neutralWidth h) := by
  apply closure_minimal _ (constrained_closed _)
  rintro f ⟨n,a,w,c,ha,hw,rfl⟩
  exact reciprocal_sum_constrained n ε h a w c hε ha hh hw

#print axioms ratio_continuous
#print axioms mem_constrained
#print axioms constrained_closed
#print axioms quadratic_shift
#print axioms density_translation
#print axioms reciprocal_packet_constrained
#print axioms reciprocal_sum_constrained
#print axioms reciprocalClosure_constrained
end
end UnifiedTheory.Audit.KFCausalNeutralGaussianConstraint
