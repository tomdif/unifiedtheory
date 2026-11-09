/- The actual commuting chart-phase/squeeze group and its strong
 derivative on common first-generator graphs. No mixed operator products
 or evolved-state moments are assumed. -/
import UnifiedTheory.Audit.KFCausalSqueezeChartCommutation
import UnifiedTheory.Audit.KFCausalPairedSqueezeTimeDerivative
import UnifiedTheory.Audit.KFCausalStrongUnitaryProductDerivative
import UnifiedTheory.Audit.KFCausalClockFloorChartPhaseContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorCombinedUnitary
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport (transport transport_initial transport_compose)
open UnifiedTheory.Audit.KFCausalPairedSqueezeContinuity (transport_strong_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorGaugeDerivative
open UnifiedTheory.Audit.KFCausalClockFloorChartPhaseContinuity (modulation_continuous modulation_zero)
open UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy (rate)
open UnifiedTheory.Audit.KFCausalSqueezeChartCommutation
open UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator (squeezeMomentum)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage (StrongUnitaryGroup)

def combined (ε h a t : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert := (transport (a*t)).trans (gauge ε h t)

theorem combined_apply (ε h a t : ℝ) (f : Hilbert) :
    combined ε h a t f = gauge ε h t (transport (a*t) f) := rfl

theorem gauge_initial (ε h : ℝ) (f : Hilbert) : gauge ε h 0 f = f := by
  change KFCausalClockFloorChartModulation.modulation ε (rate h 0) f = f
  simp only [rate,neg_zero,zero_div,modulation_zero]

theorem gauge_continuous (ε h : ℝ) (f : Hilbert) : Continuous (fun t => gauge ε h t f) :=
  (modulation_continuous ε f).comp (by unfold rate; fun_prop)

theorem combined_initial (ε h a : ℝ) (f : Hilbert) : combined ε h a 0 f = f := by
  rw [combined_apply,mul_zero,transport_initial,gauge_initial]

private theorem continuous_diagonal {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : ℝ × X → Y} (hf : Continuous f) {g : ℝ → X} (hg : Continuous g) :
    Continuous (fun t => f (t,g t)) := hf.comp (continuous_id.prodMk hg)

theorem combined_continuous (ε h a : ℝ) (f : Hilbert) : Continuous (fun t => combined ε h a t f) := by
  have hg := KFCausalStrongUnitaryContinuity.joint_evaluation_continuous (gauge ε h) (gauge_continuous ε h)
  have hs : Continuous (fun t : ℝ => transport (a*t) f) :=
    (transport_strong_continuous f).comp (continuous_const.mul continuous_id)
  change Continuous (fun t : ℝ => gauge ε h t (transport (a*t) f))
  exact continuous_diagonal hg hs

theorem combined_compose (ε h : ℝ) (hne : h ≠ 0) (a s t : ℝ) (f : Hilbert) :
    combined ε h a t (combined ε h a s f) = combined ε h a (s+t) f := by
  simp only [combined_apply,gauge_commutes,transport_compose,← gauge_add ε h hne,mul_add,add_comm]

def combinedGroup (ε h : ℝ) (hne : h ≠ 0) (a : ℝ) : StrongUnitaryGroup Hilbert where
  action := combined ε h a
  initial := combined_initial ε h a
  compose := combined_compose ε h hne a
  continuous_orbit := combined_continuous ε h a

theorem combined_inverse (ε h : ℝ) (hne : h ≠ 0) (a t : ℝ) (f : Hilbert) :
    combined ε h a (-t) (combined ε h a t f) = f := by
  rw [combined_compose ε h hne,add_neg_cancel,combined_initial]

theorem combined_dual (ε h : ℝ) (hne : h ≠ 0) (a t : ℝ) (f z : Hilbert) :
    inner ℂ (combined ε h a (-t) f) z = inner ℂ f (combined ε h a t z) := by
  have he := (combined ε h a (-t)).inner_map_map f (combined ε h a t z)
  rwa [combined_inverse ε h hne] at he

theorem combined_derivative_zero (ε h : ℝ) (hne : h ≠ 0) (a : ℝ) (f zQ zA : Hilbert)
    (hQ : (f,zQ) ∈ (chartOperator ε).graph) (hA : (f,zA) ∈ (squeezeMomentum h).graph) :
    HasDerivAt (fun t => combined ε h a t f) (coefficient h • ((a:ℂ) • zA-(2:ℂ) • zQ)) 0 := by
  have hs := KFCausalPairedSqueezeTimeDerivative.affine_time_derivative h hne a 0 f zA hA
  simp only [mul_zero,transport_initial] at hs
  have hg : HasDerivAt (fun t => gauge ε h t (transport (a*0) f))
      ((Complex.I*((-2/h:ℝ):ℂ)) • zQ) 0 := by
    simpa only [mul_zero,transport_initial] using gauge_derivative_zero ε h hne f zQ hQ
  have hd := KFCausalStrongUnitaryProductDerivative.product_derivative (gauge ε h)
    (gauge_continuous ε h) (gauge_initial ε h) (fun t => transport (a*t) f) _ _ hg hs
  have he : Complex.I*((-2/h:ℝ):ℂ) = coefficient h*(-2) := by
    unfold coefficient
    push_cast
    ring
  exact hd.congr_deriv (by
    simp only [he,smul_sub,smul_smul,mul_neg,neg_smul]
    rw [sub_eq_add_neg])

theorem combined_derivative (ε h : ℝ) (hne : h ≠ 0) (a t : ℝ) (f zQ zA : Hilbert)
    (hQ : (f,zQ) ∈ (chartOperator ε).graph) (hA : (f,zA) ∈ (squeezeMomentum h).graph) :
    HasDerivAt (fun b => combined ε h a b f)
      (coefficient h • combined ε h a t ((a:ℂ) • zA-(2:ℂ) • zQ)) t := by
  simpa only [combinedGroup,map_smul] using KFCausalStrongUnitaryGenerator.derivative_at_time
    (combinedGroup ε h hne a) f (coefficient h • ((a:ℂ) • zA-(2:ℂ) • zQ))
    (combined_derivative_zero ε h hne a f zQ zA hQ hA) t

theorem combined_defect_norm (ε : ℝ) (hε : 0 < ε) (h a t : ℝ) (f : Hilbert) :
    ‖KFCausalClockFloorDefectOperator.defectOperator ε hε (combined ε h a t f)‖ =
      ‖KFCausalClockFloorDefectOperator.defectOperator ε hε f‖ := by
  rw [combined_apply,← gauge_defect_commutes,LinearIsometryEquiv.norm_map,
    ← KFCausalPairedSqueezeClockCommutation.defect_commutes,LinearIsometryEquiv.norm_map]

#print axioms combined_apply
#print axioms gauge_initial
#print axioms gauge_continuous
#print axioms combined_initial
#print axioms combined_continuous
#print axioms combined_compose
#print axioms combined_inverse
#print axioms combined_dual
#print axioms combined_derivative_zero
#print axioms combined_derivative
#print axioms combined_defect_norm
end
end UnifiedTheory.Audit.KFCausalClockFloorCombinedUnitary
