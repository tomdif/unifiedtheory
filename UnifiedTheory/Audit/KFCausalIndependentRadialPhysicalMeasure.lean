/- Exact original mixed-coordinate measure attachment. The clock q is
unchanged, so the only Jacobian factor is the constant momentum scale
|c|^(-2); the real five-dimensional shear has determinant one. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialRealShearMeasure
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentumMeasure
import UnifiedTheory.Audit.KFCausalOrderedStaticPotentialPairing
import UnifiedTheory.Audit.KFCausalIndependentRadialTransverseRegularity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialPhysicalMeasure
noncomputable section
open MeasureTheory
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalIndependentRadialTransverseMeasure (RealSpace back)
open KFCausalRegularizedLongitudinalChart (chartIso)
open KFCausalIndependentRadialTransverseRegularity (realPoint)
open KFCausalIndependentRadialPulledLaplacian (coordinate)
open KFCausalEuclideanProductCoordinates (split)
open KFCausalPairedModeCoordinates (scale)

def inverse (ε : ℝ) (hε : 0<ε) (c q : ℝ) (y : RealSpace) : Product :=
  KFCausalIndependentRadialMomentumMeasure.scale c⁻¹
    (back q (KFCausalIndependentRadialRealShearMeasure.flow (2*scale)
      (-((chartIso ε hε).symm q)) y))

theorem inverse_clock (ε : ℝ) (hε : 0<ε) (c q : ℝ) (y : RealSpace) :
    (inverse ε hε c q y).2 0=q := rfl

private theorem coordinate_back (c q : ℝ) (hc : c≠0) (y : RealSpace) :
    coordinate c ((split 2 4).symm
      (KFCausalIndependentRadialMomentumMeasure.scale c⁻¹ (back q y)))=realPoint y := by
  ext i
  fin_cases i
  · change (c:ℂ)*((c⁻¹*y 0:ℝ):ℂ)=(y 0:ℂ)
    rw [←Complex.ofReal_mul,mul_inv_cancel_left₀ hc]
  · change (c:ℂ)*((c⁻¹*y 1:ℝ):ℂ)=(y 1:ℂ)
    rw [←Complex.ofReal_mul,mul_inv_cancel_left₀ hc]
  · rfl
  · rfl
  · rfl

theorem inverse_coordinate (ε : ℝ) (hε : 0<ε) (c q : ℝ) (hc : c≠0) (y : RealSpace) :
    coordinate c ((split 2 4).symm (inverse ε hε c q y))=
      KFCausalComplexShearPerturbation.flow (2*scale) (-((chartIso ε hε).symm q):ℝ)
        (realPoint y) := by
  rw [inverse,coordinate_back c q hc]
  exact (KFCausalIndependentRadialRealShearMeasure.complex_flow _ _ y).symm

theorem mixed_inverse (ε : ℝ) (hε : 0<ε) (c q : ℝ) (y : RealSpace) :
    KFCausalClockFloorMixedChart.mixedMap ε hε (inverse ε hε c q y)=
      (WithLp.toLp 2 ![c⁻¹*y 0,c⁻¹*y 1],
        WithLp.toLp 2 ![(chartIso ε hε).symm q,y 2,y 3,y 4]) := by
  apply Prod.ext
  · ext i
    fin_cases i <;>
      simp [KFCausalClockFloorMixedChart.mixedMap,inverse,
        KFCausalIndependentRadialMomentumMeasure.scale,back,
        KFCausalClockFloorPairedStraightening.dilation,
        KFCausalClockFloorPairedStraightening.clockInverse,
        KFCausalIndependentRadialRealShearMeasure.flow,Real.exp_neg,neg_div,mul_left_comm]
  · ext i
    fin_cases i <;>
      simp [KFCausalClockFloorMixedChart.mixedMap,inverse,
        KFCausalIndependentRadialMomentumMeasure.scale,back,
        KFCausalClockFloorSpectatorChart.backward,KFCausalClockFloorSpectatorChart.flow,
        KFCausalClockFloorSpectatorChart.changeClock,
        KFCausalIndependentRadialRealShearMeasure.flow,Real.exp_neg,neg_div]
    field_simp
    ring

theorem inverse_field (ε : ℝ) (hε : 0<ε) (c q : ℝ) (y : RealSpace) :
    KFCausalOrderedStaticPotentialPairing.field ε hε (inverse ε hε c q y)=
      2*scale*y 3+y 4 := by
  rw [KFCausalOrderedStaticPotentialPairing.field,mixed_inverse]
  rfl

private def fiber (τ : ℝ→ℝ) (hτ : Continuous τ) : (ℝ×RealSpace)≃ₜ(ℝ×RealSpace) where
  toFun z := (z.1,KFCausalIndependentRadialRealShearMeasure.flow (2*scale) (τ z.1) z.2)
  invFun z := (z.1,KFCausalIndependentRadialRealShearMeasure.flow (2*scale) (-τ z.1) z.2)
  left_inv z := by simp only [KFCausalIndependentRadialRealShearMeasure.flow_inverse]
  right_inv z := by
    have h := KFCausalIndependentRadialRealShearMeasure.flow_inverse (2*scale) (-τ z.1) z.2
    simpa only [neg_neg] using congrArg (fun y=>(z.1,y)) h
  continuous_toFun := by
    apply continuous_fst.prodMk
    apply continuous_pi
    intro i
    fin_cases i <;>
      simp [KFCausalIndependentRadialRealShearMeasure.flow]
    all_goals fun_prop
  continuous_invFun := by
    apply continuous_fst.prodMk
    apply continuous_pi
    intro i
    fin_cases i <;>
      simp [KFCausalIndependentRadialRealShearMeasure.flow]
    all_goals fun_prop

private theorem fiber_preserving (τ : ℝ→ℝ) (hτ : Continuous τ) :
    MeasurePreserving (fiber τ hτ) := by
  exact (MeasurePreserving.id volume).skew_product
    (g:=fun q y=>KFCausalIndependentRadialRealShearMeasure.flow (2*scale) (τ q) y)
    (measurable_snd.comp (fiber τ hτ).continuous.measurable)
    (Filter.Eventually.of_forall (fun q=>
      (KFCausalIndependentRadialRealShearMeasure.flow_preserving (2*scale) (τ q)).map_eq))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem integrable_inverse_iff (ε : ℝ) (hε : 0<ε) (c : ℝ) (hc : c≠0) (F : Product→E) :
    Integrable (fun z:ℝ×RealSpace=>F (inverse ε hε c z.1 z.2)) ↔ Integrable F := by
  let τ : ℝ→ℝ := fun q=>-((chartIso ε hε).symm q)
  have hτ : Continuous τ := (chartIso ε hε).symm.toHomeomorph.continuous.neg
  have he := (fiber_preserving τ hτ).integrable_comp_emb
    (fiber τ hτ).toMeasurableEquiv.measurableEmbedding
    (g:=fun z:ℝ×RealSpace=>F (KFCausalIndependentRadialMomentumMeasure.scale c⁻¹ (back z.1 z.2)))
  exact he.trans ((KFCausalIndependentRadialTransverseMeasure.integrable_iff _).trans
    (KFCausalIndependentRadialMomentumMeasure.scale_integrable_iff c⁻¹ (inv_ne_zero hc) F))

theorem integral_inverse (ε : ℝ) (hε : 0<ε) (c : ℝ) (hc : c≠0) (F : Product→E)
    (hF : Integrable F) :
    (∫x:Product,F x)=(|c|^2)⁻¹ • ∫q:ℝ,∫y:RealSpace,F (inverse ε hε c q y) := by
  rw [KFCausalIndependentRadialMomentumMeasure.integral_eq_inverse_scale c hc F]
  congr 1
  rw [KFCausalIndependentRadialTransverseMeasure.integral_order _
    ((KFCausalIndependentRadialMomentumMeasure.inverse_scale_integrable_iff c hc F).mpr hF)]
  apply integral_congr_ae
  filter_upwards with q
  exact (KFCausalIndependentRadialRealShearMeasure.integral_flow (2*scale)
    (-((chartIso ε hε).symm q))
    (fun y=>F (KFCausalIndependentRadialMomentumMeasure.scale c⁻¹ (back q y)))).symm

#print axioms inverse_clock
#print axioms inverse_coordinate
#print axioms mixed_inverse
#print axioms inverse_field
#print axioms integrable_inverse_iff
#print axioms integral_inverse
end
end UnifiedTheory.Audit.KFCausalIndependentRadialPhysicalMeasure
