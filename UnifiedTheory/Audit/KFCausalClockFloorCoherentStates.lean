/- An explicit total Gaussian modulation family in the actual charge
coordinates. The physical charge circle rotates its parameters with
constant norm. Energy-domain membership of this enlarged family is separate. -/
import UnifiedTheory.Audit.KFCausalModulatedLpTotality
import UnifiedTheory.Audit.KFCausalChargeModulationFlow
import UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentStates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (clockFunction clockFunction_continuous
  clockFunction_memLp clockFunction_ne_zero neutralWidth neutralWidth_positive trialState)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates action action_coordinates)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow
open UnifiedTheory.Audit.KFCausalEuclideanFourierUniqueness (modulate)

def weight (ε a hbar : ℝ) (x : Joint 2 4) : ℂ :=
  ((Real.pi/groundWidth hbar:ℝ):ℂ)*
    profile (groundWidth hbar) (neutralWidth hbar) (momentumScale hbar) (clockFunction ε a) x

theorem weight_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    chargeCoordinates (trialState ε a hbar hε ha hh) =ᵐ[volume] weight ε a hbar :=
  KFCausalPhysicalGaussianCharge.state_chargeCoordinates _ _ _
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (groundWidth_matching hbar hh)
    _ (clockFunction_continuous ε a) (clockFunction_memLp ε a hε ha)

theorem weight_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    MemLp (weight ε a hbar) 2 :=
  (Lp.memLp (chargeCoordinates (trialState ε a hbar hε ha hh))).ae_eq (weight_coe ε a hbar hε ha hh)

theorem weight_ne_zero (ε a hbar : ℝ) (hε : 0 < ε) (hh : hbar ≠ 0) (x : Joint 2 4) :
    weight ε a hbar x ≠ 0 := by
  unfold weight profile
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (div_ne_zero Real.pi_ne_zero
    (groundWidth_positive hbar hh).ne'))
    (mul_ne_zero (clockFunction_ne_zero ε a hε.le _) (Complex.exp_ne_zero _))

theorem weight_flow (ε a hbar : ℝ) (hh : hbar ≠ 0) (θ : ℝ) (x : Joint 2 4) :
    weight ε a hbar (flowEquiv (momentumScale hbar) (momentumScale_ne_zero hbar hh) θ x) =
      weight ε a hbar x := by
  simp only [weight,profile_flow]

def mixedState (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) : JointHilbert 2 4 :=
  KFCausalModulatedLpTotality.state (weight ε a hbar) (weight_memLp ε a hbar hε ha hh)
    (dilate (momentumScale hbar) k)

def state (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) : Hilbert := chargeCoordinates.symm (mixedState ε a hbar hε ha hh k)

theorem mixedState_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) : mixedState ε a hbar hε ha hh k =ᵐ[volume]
      modulate (dilate (momentumScale hbar) k) (weight ε a hbar) :=
  KFCausalModulatedLpTotality.state_coe _ _ _

theorem state_coordinates (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) : chargeCoordinates (state ε a hbar hε ha hh k) = mixedState ε a hbar hε ha hh k :=
  chargeCoordinates.apply_symm_apply _

theorem state_zero (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    state ε a hbar hε ha hh 0 = trialState ε a hbar hε ha hh := by
  apply chargeCoordinates.injective
  rw [state_coordinates]
  apply Lp.ext
  filter_upwards [mixedState_coe ε a hbar hε ha hh 0,weight_coe ε a hbar hε ha hh] with x hx hy
  have hzero : dilate (momentumScale hbar) (0 : Joint 2 4) = 0 :=
    (dilationEquiv _ (momentumScale_ne_zero hbar hh)).map_zero
  simp [hzero,modulate] at hx
  exact hx.trans hy.symm

theorem action_state (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (θ : ℝ) (k : Joint 2 4) :
    action hbar hh θ (state ε a hbar hε ha hh k) = state ε a hbar hε ha hh (parameter θ k) := by
  apply chargeCoordinates.injective
  rw [action_coordinates,state_coordinates,state_coordinates]
  apply Lp.ext
  filter_upwards [KFCausalMixedCircleAction.action_coe _ (momentumScale_ne_zero hbar hh) θ
      (mixedState ε a hbar hε ha hh k),
    (flow_preserves_volume _ (momentumScale_ne_zero hbar hh) θ).quasiMeasurePreserving.ae
      (mixedState_coe ε a hbar hε ha hh k),
    mixedState_coe ε a hbar hε ha hh (parameter θ k)] with x hx hy hz
  simp only [Function.comp_apply] at hx
  rw [hx,hy,hz]
  simp only [modulate,flow_phase]
  rw [weight_flow ε a hbar hh θ x]

theorem mixed_dense_span (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    (Submodule.span ℂ (Set.range (mixedState ε a hbar hε ha hh))).topologicalClosure = ⊤ := by
  have he : Set.range (mixedState ε a hbar hε ha hh) =
      Set.range (KFCausalModulatedLpTotality.state (weight ε a hbar) (weight_memLp ε a hbar hε ha hh)) :=
    (dilationEquiv _ (momentumScale_ne_zero hbar hh)).surjective.range_comp _
  rw [he]
  exact KFCausalModulatedLpTotality.dense_span _ _ (weight_ne_zero ε a hbar hε hh)

theorem dense_span (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    (Submodule.span ℂ (Set.range (state ε a hbar hε ha hh))).topologicalClosure = ⊤ := by
  let L : JointHilbert 2 4 →L[ℂ] Hilbert := chargeCoordinates.symm
  have hd : DenseRange L := chargeCoordinates.symm.surjective.denseRange
  have h := hd.topologicalClosure_map_submodule (mixed_dense_span ε a hbar hε ha hh)
  rw [Submodule.map_span,← Set.range_comp] at h
  exact h

#print axioms weight_coe
#print axioms weight_memLp
#print axioms weight_ne_zero
#print axioms weight_flow
#print axioms mixedState_coe
#print axioms state_coordinates
#print axioms state_zero
#print axioms action_state
#print axioms mixed_dense_span
#print axioms dense_span

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentStates
