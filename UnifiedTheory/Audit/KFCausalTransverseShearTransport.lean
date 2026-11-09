/- Actual strongly continuous transverse shear on physical L2. The clock
is fixed and the half-density exp(t) is derived from existing unitaries. -/
import UnifiedTheory.Audit.KFCausalTransverseShearCoordinates
import UnifiedTheory.Audit.KFCausalClockFourierDiagonalization
import UnifiedTheory.Audit.KFCausalStrongUnitaryContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalTransverseShearTransport
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph (flow_joint_continuous)
open UnifiedTheory.Audit.KFCausalCoupledCoordinateNullSets (flow_joint_differentiable homeomorph_quasiMeasurePreserving)
open UnifiedTheory.Audit.KFCausalTransverseShearCoordinates
open UnifiedTheory.Audit.KFCausalConfigurationTranslation
open UnifiedTheory.Audit.KFCausalClockFourierDiagonalization (clock_translation_coe)

def shearFlow (t : ℝ) : Configuration ≃ₜ Configuration where
  toFun x := (x.1,flow t x.2)
  invFun x := (x.1,flow (-t) x.2)
  left_inv x := by simp only [flow_reverse,Prod.mk.eta]
  right_inv x := by simp only [flow_compose,neg_add_cancel,flow_initial,Prod.mk.eta]
  continuous_toFun := continuous_fst.prodMk
    (flow_joint_continuous.comp (continuous_const.prodMk continuous_snd))
  continuous_invFun := continuous_fst.prodMk
    (flow_joint_continuous.comp (continuous_const.prodMk continuous_snd))

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem shearFlow_quasiMeasurePreserving (t : ℝ) :
    Measure.QuasiMeasurePreserving (shearFlow t) volume volume :=
  homeomorph_quasiMeasurePreserving volume (shearFlow t)
    (differentiable_fst.prodMk
      (flow_joint_differentiable.comp ((differentiable_const (-t)).prodMk differentiable_snd)))

theorem shearFlow_compose (t u : ℝ) (x : Configuration) :
    shearFlow u (shearFlow t x) = shearFlow (t+u) x := by
  change (x.1,flow u (flow t x.2)) = (x.1,flow (t+u) x.2)
  rw [flow_compose]

def transport (t : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  (translation (-t)).trans (coordinates.symm.trans ((translation t).trans coordinates))

theorem transport_apply (t : ℝ) (f : Hilbert) :
    transport t f = coordinates (translation t (coordinates.symm (translation (-t) f))) := rfl

theorem transport_coe (t : ℝ) (f : Hilbert) :
    transport t f =ᵐ[volume] fun x => (Real.exp t:ℂ)*f (shearFlow t x) := by
  filter_upwards [coordinates_coe (translation t (coordinates.symm (translation (-t) f))),
    shearChart_quasiMeasurePreserving.ae (clock_translation_coe t (coordinates.symm (translation (-t) f))),
    ((clockShift_measurePreserving t).quasiMeasurePreserving.comp shearChart_quasiMeasurePreserving).ae
      (coordinates_inverse_coe (translation (-t) f)),
    (shearChart_inverse_quasiMeasurePreserving.comp
      ((clockShift_measurePreserving t).quasiMeasurePreserving.comp shearChart_quasiMeasurePreserving)).ae
      (clock_translation_coe (-t) f)] with x hv ht hi hf
  dsimp only [Function.comp_apply] at ht hi hf
  change coordinates (translation t (coordinates.symm (translation (-t) f))) x = _
  rw [hv,ht,hi,hf]
  have hp : clockShift (-t) (shearChart.symm (clockShift t (shearChart x))) = shearFlow t x := by
    simp only [clockShift_apply]
    change ((x.1+t)+(-t),flow (x.1+t) (flow (-x.1) x.2)) = (x.1,flow t x.2)
    rw [flow_compose]
    simp only [add_neg_cancel_right,neg_add_cancel_left]
  have hw : (Real.exp (-x.1):ℂ)*(Real.exp (clockShift t (shearChart x)).1:ℂ) = (Real.exp t:ℂ) := by
    rw [clockShift_apply]
    change (Real.exp (-x.1):ℂ)*(Real.exp (x.1+t):ℂ) = _
    rw [← Complex.ofReal_mul,← Real.exp_add,neg_add_cancel_left]
  rw [hp,← mul_assoc,hw]

theorem transport_initial (f : Hilbert) : transport 0 f = f := by
  rw [transport_apply,neg_zero,translation_initial,translation_initial,LinearIsometryEquiv.apply_symm_apply]

theorem transport_compose (t u : ℝ) (f : Hilbert) :
    transport u (transport t f) = transport (t+u) f := by
  apply Lp.ext
  filter_upwards [transport_coe u (transport t f),transport_coe (t+u) f,
    (shearFlow_quasiMeasurePreserving u).ae (transport_coe t f)] with x hu hsum ht
  rw [hu,hsum,ht,shearFlow_compose]
  rw [add_comm u t,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add,add_comm u t]

theorem transport_reverse (t : ℝ) (f : Hilbert) : transport (-t) (transport t f) = f := by
  rw [transport_compose,add_neg_cancel,transport_initial]

theorem transport_strong_continuous (f : Hilbert) : Continuous (fun t : ℝ => transport t f) := by
  change Continuous (fun t : ℝ => coordinates (translation t (coordinates.symm (translation (-t) f))))
  have hv : Continuous (fun t : ℝ => coordinates.symm (translation (-t) f)) :=
    coordinates.symm.continuous.comp ((translation_strong_continuous f).comp continuous_neg)
  have hc : Continuous (fun p : ℝ × Hilbert => translation p.1 p.2) :=
    KFCausalStrongUnitaryContinuity.joint_evaluation_continuous translation translation_strong_continuous
  have hp : Continuous (fun t : ℝ => (t,coordinates.symm (translation (-t) f))) :=
    (continuous_id : Continuous (fun t : ℝ => t)).prodMk hv
  have ht : Continuous (fun t : ℝ => translation t (coordinates.symm (translation (-t) f))) := by
    simpa only [Function.comp_apply] using hc.comp hp
  simpa only [Function.comp_apply] using coordinates.continuous.comp ht

theorem transport_unitary (t : ℝ) :
    (transport t : Hilbert →L[ℂ] Hilbert) ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  (Unitary.linearIsometryEquiv.symm (transport t)).property

theorem transport_toLp_coe (t : ℝ) (f : Configuration → ℂ) (hf : MemLp f 2) :
    transport t (hf.toLp f) =ᵐ[volume] fun x => (Real.exp t:ℂ)*f (shearFlow t x) := by
  filter_upwards [transport_coe t (hf.toLp f),(shearFlow_quasiMeasurePreserving t).ae hf.coeFn_toLp]
    with x hx hf'
  rw [hx,hf']

theorem transport_translation (t u : ℝ) (f : Hilbert) :
    transport t (translation u f) = translation u (transport t f) := by
  apply Lp.ext
  filter_upwards [transport_coe t (translation u f),clock_translation_coe u (transport t f),
    (shearFlow_quasiMeasurePreserving t).ae (clock_translation_coe u f),
    (clockShift_measurePreserving u).quasiMeasurePreserving.ae (transport_coe t f)] with x hs ht hf hg
  rw [hs,ht,hf,hg]
  simp only [clockShift_apply]
  rfl

#print axioms shearFlow_quasiMeasurePreserving
#print axioms shearFlow_compose
#print axioms transport_coe
#print axioms transport_initial
#print axioms transport_compose
#print axioms transport_reverse
#print axioms transport_strong_continuous
#print axioms transport_unitary
#print axioms transport_toLp_coe
#print axioms transport_translation
end
end UnifiedTheory.Audit.KFCausalTransverseShearTransport
