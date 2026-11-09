/- An actual charge-compatible neutral-position test. The added Gaussian
in antisymmetric momentum completes the existing symmetric-position
Gaussian to a charge-invariant plane radius. This defines a bounded test
operator; full matter-domain preservation remains a separate obligation. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionCutoffCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar scalar_norm)
open UnifiedTheory.Audit.KFCausalContractiveMultiplier
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedKinetics (input input_eq chargedLinear)
open UnifiedTheory.Audit.KFCausalNeutralPositionCutoffCharge (charge_cutoff_coe)

def planeRadius (c : ℝ) (x : Joint 2 4) : ℝ := (c*x (.inl 1))^2+(x (.inr 2))^2

theorem planeRadius_nonneg (c : ℝ) (x : Joint 2 4) : 0 ≤ planeRadius c x :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem planeRadius_flow (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Joint 2 4) :
    planeRadius c (flowEquiv c hc θ x) = planeRadius c x := by
  have hp := congrArg Prod.fst (flow_second_plane c hc θ x)
  have hq := congrArg Prod.snd (flow_second_plane c hc θ x)
  dsimp only at hp hq
  have hp' : c*(flowEquiv c hc θ x) (.inl 1) =
      Real.cos θ*(c*x (.inl 1))-Real.sin θ*x (.inr 2) := by
    rw [hp]
    field_simp
  rw [planeRadius,hp',hq,planeRadius]
  nlinarith [congrArg (fun r : ℝ => r*(c*x (.inl 1))^2) (Real.sin_sq_add_cos_sq θ),
    congrArg (fun r : ℝ => r*(x (.inr 2))^2) (Real.sin_sq_add_cos_sq θ)]

def symbol (h δ v : ℝ) (x : Joint 2 4) : ℂ :=
  (Real.exp (-2*δ*planeRadius (momentumScale h) x):ℂ)*scalar (v*x (.inr 3))

theorem symbol_measurable (h δ v : ℝ) : Measurable (symbol h δ v) := by
  unfold symbol planeRadius scalar
  fun_prop

theorem symbol_norm (h δ v : ℝ) (hδ : 0 < δ) (x : Joint 2 4) : ‖symbol h δ v x‖ ≤ 1 := by
  rw [symbol,norm_mul,scalar_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (planeRadius_nonneg _ _)

theorem symbol_flow (h : ℝ) (hne : h ≠ 0) (δ v θ : ℝ) (x : Joint 2 4) :
    symbol h δ v (flowEquiv (momentumScale h) (momentumScale_ne_zero h hne) θ x) = symbol h δ v x := by
  simp only [symbol,planeRadius_flow,flow_neutral]

def action (h δ v : ℝ) (hδ : 0 < δ) : Hilbert →L[ℂ] Hilbert :=
  (chargeCoordinates.symm : JointHilbert 2 4 →L[ℂ] Hilbert).comp
    ((multiplyL (symbol h δ v) (symbol_measurable h δ v) (symbol_norm h δ v hδ)).comp
      (chargeCoordinates : Hilbert →L[ℂ] JointHilbert 2 4))

theorem action_coe (h δ v : ℝ) (hδ : 0 < δ) (f : Hilbert) :
    chargeCoordinates (action h δ v hδ f) =ᵐ[volume] fun x => symbol h δ v x*(chargeCoordinates f) x := by
  change chargeCoordinates (chargeCoordinates.symm (_)) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact multiplyL_coe (symbol h δ v) (symbol_measurable h δ v) (symbol_norm h δ v hδ) _

theorem action_norm (h δ v : ℝ) (hδ : 0 < δ) (f : Hilbert) : ‖action h δ v hδ f‖ ≤ ‖f‖ := by
  change ‖chargeCoordinates.symm (multiplyL (symbol h δ v) (symbol_measurable h δ v)
    (symbol_norm h δ v hδ) (chargeCoordinates f))‖ ≤ _
  rw [chargeCoordinates.symm.norm_map,← chargeCoordinates.norm_map f]
  exact multiply_norm_le (symbol h δ v) (symbol_measurable h δ v) (symbol_norm h δ v hδ) _

theorem action_charge (h : ℝ) (hne : h ≠ 0) (δ v : ℝ) (hδ : 0 < δ) (θ : ℝ) (f : Hilbert) :
    action h δ v hδ (KFCausalPhysicalCircleAction.action h hne θ f) =
      KFCausalPhysicalCircleAction.action h hne θ (action h δ v hδ f) := by
  apply chargeCoordinates.injective
  apply Lp.ext
  let c := momentumScale h
  have hc : c ≠ 0 := momentumScale_ne_zero h hne
  filter_upwards [action_coe h δ v hδ (KFCausalPhysicalCircleAction.action h hne θ f),
    KFCausalMixedCircleAction.action_coe c hc θ (chargeCoordinates f),
    KFCausalMixedCircleAction.action_coe c hc θ (chargeCoordinates (action h δ v hδ f)),
    (flow_preserves_volume c hc θ).quasiMeasurePreserving.ae (action_coe h δ v hδ f)] with x hm hu ha hf
  rw [hm,KFCausalPhysicalCircleAction.action_coordinates,hu,
    KFCausalPhysicalCircleAction.action_coordinates,ha]
  change chargeCoordinates (action h δ v hδ f) (flowEquiv c hc θ x) = _ at hf
  simp only [Function.comp_apply]
  rw [hf,symbol_flow h hne δ v θ x]

def heatSymbol (h δ : ℝ) (x : Joint 2 4) : ℂ :=
  (Real.exp (-2*δ*(momentumScale h*x (.inl 1))^2):ℂ)

theorem heatSymbol_measurable (h δ : ℝ) : Measurable (heatSymbol h δ) := by
  unfold heatSymbol
  fun_prop

theorem heatSymbol_norm (h δ : ℝ) (hδ : 0 < δ) (x : Joint 2 4) : ‖heatSymbol h δ x‖ ≤ 1 := by
  rw [heatSymbol,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)

def heat (h δ : ℝ) (hδ : 0 < δ) : Hilbert →L[ℂ] Hilbert :=
  (chargeCoordinates.symm : JointHilbert 2 4 →L[ℂ] Hilbert).comp
    ((multiplyL (heatSymbol h δ) (heatSymbol_measurable h δ) (heatSymbol_norm h δ hδ)).comp
      (chargeCoordinates : Hilbert →L[ℂ] JointHilbert 2 4))

theorem heat_coe (h δ : ℝ) (hδ : 0 < δ) (f : Hilbert) :
    chargeCoordinates (heat h δ hδ f) =ᵐ[volume] fun x => heatSymbol h δ x*(chargeCoordinates f) x := by
  change chargeCoordinates (chargeCoordinates.symm (_)) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact multiplyL_coe (heatSymbol h δ) (heatSymbol_measurable h δ) (heatSymbol_norm h δ hδ) _

theorem heat_norm (h δ : ℝ) (hδ : 0 < δ) (f : Hilbert) : ‖heat h δ hδ f‖ ≤ ‖f‖ := by
  change ‖chargeCoordinates.symm (multiplyL (heatSymbol h δ) (heatSymbol_measurable h δ)
    (heatSymbol_norm h δ hδ) (chargeCoordinates f))‖ ≤ _
  rw [chargeCoordinates.symm.norm_map,← chargeCoordinates.norm_map f]
  exact multiply_norm_le (heatSymbol h δ) (heatSymbol_measurable h δ) (heatSymbol_norm h δ hδ) _

theorem action_eq_input_heat (ε h δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (f : Hilbert) :
    action h δ v hδ f = input ε δ v hε hδ (heat h δ hδ f) := by
  rw [input_eq]
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [action_coe h δ v hδ f,
    KFCausalNeutralPositionCharge.charge_action_coe v
      (KFCausalPhysicalGaussianCutoff.cutoff δ hδ chargedLinear (heat h δ hδ f)),
    charge_cutoff_coe δ hδ (heat h δ hδ f),heat_coe h δ hδ f] with x hm hp hq hh
  rw [hm,hp,hq,hh]
  unfold symbol heatSymbol planeRadius
  rw [show -2*δ*((momentumScale h*x (.inl 1))^2+(x (.inr 2))^2) =
    -2*δ*(momentumScale h*x (.inl 1))^2+(-2*δ*(x (.inr 2))^2) by ring,Real.exp_add,Complex.ofReal_mul]
  ring

#print axioms planeRadius_nonneg
#print axioms planeRadius_flow
#print axioms symbol_measurable
#print axioms symbol_norm
#print axioms symbol_flow
#print axioms action_coe
#print axioms action_norm
#print axioms action_charge
#print axioms heatSymbol_measurable
#print axioms heatSymbol_norm
#print axioms heat_coe
#print axioms heat_norm
#print axioms action_eq_input_heat

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff
