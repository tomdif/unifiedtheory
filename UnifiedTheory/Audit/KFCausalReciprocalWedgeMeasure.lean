/- The real-linear Laplace chart transports Lebesgue measure with the
proved wedge Jacobian. Both the restricted integral and integrability
are transported; no change-of-variables premise is assumed. -/
import UnifiedTheory.Audit.KFCausalReciprocalWedgePrefactor
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalReciprocalWedgeMeasure
noncomputable section
open MeasureTheory Set
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalReciprocalWedgeGeometry (chart first second wedge)
open KFCausalReciprocalWedgePrefactor (jacobian signedJacobian)

def quadrant : Set ℂ := {z | 0 ≤ z.re ∧ 0 ≤ z.im}

def linear (α : ℝ) (r : ℂ) : ℂ →ₗ[ℝ] ℂ where
  toFun z := chart α r z.re z.im
  map_add' z w := by simp only [chart,Complex.add_re,Complex.add_im,Complex.ofReal_add]; ring
  map_smul' a z := by
    change chart α r (a • z).re (a • z).im = a • chart α r z.re z.im
    rw [Complex.smul_re,Complex.smul_im]
    simp only [smul_eq_mul,chart,Complex.ofReal_mul,Complex.real_smul]
    ring

theorem linear_apply (α : ℝ) (r z : ℂ) : linear α r z = chart α r z.re z.im := rfl

theorem linear_matrix (α : ℝ) (r : ℂ) :
    LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (linear α r) =
      !![α*area r/2,α*area r/2;α*r.re*r.im,-α*r.re*r.im] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply,Complex.coe_basisOneI,Complex.coe_basisOneI_repr,
      linear_apply,KFCausalReciprocalWedgeGeometry.chart_re,KFCausalReciprocalWedgeGeometry.chart_im]

theorem linear_det (α : ℝ) (r : ℂ) :
    LinearMap.det (linear α r) = -α^2*area r*r.re*r.im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI,linear_matrix,Matrix.det_fin_two]
  dsimp
  ring

def equivalence (α : ℝ) (r : ℂ) (hα : α ≠ 0) (hA : area r ≠ 0)
    (ha : r.re ≠ 0) (hb : r.im ≠ 0) : ℂ ≃ₗ[ℝ] ℂ :=
  { linear α r with
    invFun := fun z => ⟨first α r z,second α r z⟩
    left_inv := fun z => by
      apply Complex.ext
      · exact KFCausalReciprocalWedgeGeometry.first_chart α z.re z.im r hα hA ha hb
      · exact KFCausalReciprocalWedgeGeometry.second_chart α z.re z.im r hα hA ha hb
    right_inv := fun z => KFCausalReciprocalWedgeGeometry.chart_coordinates α r z hα hA ha hb }

theorem map_volume (α : ℝ) (r : ℂ) (hα : α ≠ 0) (hA : area r ≠ 0)
    (ha : r.re ≠ 0) (hb : r.im ≠ 0) :
    Measure.map (linear α r) volume = ENNReal.ofReal (jacobian α r) • (volume : Measure ℂ) := by
  have hd : LinearMap.det (linear α r) ≠ 0 := by
    rw [linear_det]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hα)) hA) ha) hb
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) hd
  rw [linear_det] at hm
  simpa only [jacobian,signedJacobian,one_div,neg_mul,inv_neg,abs_neg] using hm

theorem quadrant_measurable : MeasurableSet quadrant :=
  (isClosed_le continuous_const Complex.continuous_re).measurableSet.inter
    (isClosed_le continuous_const Complex.continuous_im).measurableSet

theorem wedge_measurable (α : ℝ) (r : ℂ) : MeasurableSet (wedge α r) := by
  have hf : Continuous (first α r) := by unfold first; fun_prop
  have hs : Continuous (second α r) := by unfold second; fun_prop
  exact (isClosed_le continuous_const hf).measurableSet.inter
    (isClosed_le continuous_const hs).measurableSet

theorem preimage_wedge (α : ℝ) (r : ℂ) (hα : α ≠ 0) (hA : area r ≠ 0)
    (ha : r.re ≠ 0) (hb : r.im ≠ 0) : (linear α r) ⁻¹' wedge α r = quadrant := by
  ext z
  simp only [mem_preimage,wedge,quadrant,mem_setOf_eq,linear_apply,
    KFCausalReciprocalWedgeGeometry.first_chart α z.re z.im r hα hA ha hb,
    KFCausalReciprocalWedgeGeometry.second_chart α z.re z.im r hα hA ha hb]

theorem integral_quadrant (α : ℝ) (r : ℂ) (hα : α ≠ 0) (hA : area r ≠ 0)
    (ha : r.re ≠ 0) (hb : r.im ≠ 0) (f : ℂ → ℝ) :
    (∫ z in quadrant, f (linear α r z)) = jacobian α r*∫ z in wedge α r, f z := by
  have hm := (equivalence α r hα hA ha hb).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding.integral_map
    (μ := volume) ((wedge α r).indicator f)
  change (∫ z, (wedge α r).indicator f z ∂Measure.map (linear α r) volume) =
    ∫ z, (wedge α r).indicator f (linear α r z) at hm
  rw [map_volume α r hα hA ha hb,integral_smul_measure] at hm
  simp only [ENNReal.toReal_ofReal (show 0 ≤ jacobian α r by unfold jacobian; positivity),smul_eq_mul,
    integral_indicator (wedge_measurable α r),← indicator_comp_right,preimage_wedge α r hα hA ha hb,
    integral_indicator quadrant_measurable] at hm
  exact hm.symm

theorem integrable_quadrant (α : ℝ) (r : ℂ) (hα : α ≠ 0) (hA : area r ≠ 0)
    (ha : r.re ≠ 0) (hb : r.im ≠ 0) (f : ℂ → ℝ) :
    IntegrableOn (fun z => f (linear α r z)) quadrant ↔ IntegrableOn f (wedge α r) := by
  have hj : 0 < jacobian α r := by unfold jacobian signedJacobian; positivity
  have hm := (equivalence α r hα hA ha hb).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding.integrable_map_iff
    (μ := volume) (g := (wedge α r).indicator f)
  change Integrable ((wedge α r).indicator f) (Measure.map (linear α r) volume) ↔
    Integrable ((wedge α r).indicator f ∘ linear α r) at hm
  rw [map_volume α r hα hA ha hb,integrable_smul_measure (by positivity) (by finiteness)] at hm
  change Integrable ((wedge α r).indicator f) ↔
    Integrable (fun z => (wedge α r).indicator f (linear α r z)) at hm
  simp only [← indicator_comp_right,preimage_wedge α r hα hA ha hb,
    integrable_indicator_iff (wedge_measurable α r),integrable_indicator_iff quadrant_measurable] at hm
  exact hm.symm

#print axioms linear_apply
#print axioms linear_matrix
#print axioms linear_det
#print axioms map_volume
#print axioms quadrant_measurable
#print axioms wedge_measurable
#print axioms preimage_wedge
#print axioms integral_quadrant
#print axioms integrable_quadrant
end
end UnifiedTheory.Audit.KFCausalReciprocalWedgeMeasure
