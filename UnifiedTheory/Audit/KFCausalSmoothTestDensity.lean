/- Every smooth compactly supported spacetime test has finite tensor
approximants converging uniformly together with both partial derivatives. -/
import UnifiedTheory.Audit.KFCausalSmoothUnitWindow
import UnifiedTheory.Audit.KFCausalTensorAffineTime
import Mathlib.Topology.Algebra.GroupWithZero

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSmoothTestDensity
noncomputable section
open Set Filter BoundedContinuousFunction
open scoped Topology ContDiff
open UnifiedTheory.Audit.KFCausalSmoothSpacetimeTests (Test)
open UnifiedTheory.Audit.KFCausalTensorTestClosure (Approximable)
open UnifiedTheory.Audit.KFCausalSmoothTestApproximation (identify_derivatives)
open UnifiedTheory.Audit.KFCausalSmoothUnitWindow (approximable_unit_window)
open UnifiedTheory.Audit.KFCausalTensorAffineTime

def affineHomeomorph (c d : ℝ) (hc : c ≠ 0) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  ((Homeomorph.mulLeft₀ c hc).trans (Homeomorph.addRight d)).prodCongr (Homeomorph.refl ℝ)

theorem affineHomeomorph_apply (c d : ℝ) (hc : c ≠ 0) (z : ℝ × ℝ) :
    affineHomeomorph c d hc z = (c*z.1+d,z.2) := rfl

def affineTest (φ : Test) (c d : ℝ) (hc : c ≠ 0) : Test where
  value z := φ.value (c*z.1+d,z.2)
  smooth := φ.smooth.comp (((contDiff_const.mul contDiff_fst).add contDiff_const).prodMk contDiff_snd)
  compact := φ.compact.comp_isClosedEmbedding (affineHomeomorph c d hc).isClosedEmbedding

theorem test_time_bound (φ : Test) :
    ∃ R : ℝ, 0 < R ∧ ∀ z, φ.value z ≠ 0 → |z.1| ≤ R := by
  obtain ⟨R,hR,hbound⟩ := (φ.compact.image continuous_fst).isBounded.exists_pos_norm_le
  refine ⟨R,hR,fun z hz => ?_⟩
  exact hbound z.1 ⟨z,subset_tsupport φ.value hz,rfl⟩

theorem rescaled_test_support (φ : Test) (R : ℝ) (hR : 0 < R)
    (hb : ∀ z, φ.value z ≠ 0 → |z.1| ≤ R) :
    ∀ z, (affineTest φ (4*R) (-2*R) (by positivity)).value z ≠ 0 →
      z.1 ∈ Icc (1/4 : ℝ) (3/4) := by
  intro z hz
  have hh := hb (4*R*z.1+ -2*R,z.2) hz
  simp only [neg_mul,← sub_eq_add_neg] at hh
  rw [abs_le] at hh
  constructor <;> nlinarith [hh.1,hh.2]

theorem smooth_test_approximable (φ : Test) :
    Approximable φ.toBCF φ.dt.toBCF φ.dp.toBCF := by
  obtain ⟨R,hR,hbound⟩ := test_time_bound φ
  let ψ := affineTest φ (4*R) (-2*R) (by positivity)
  have hψ := approximable_unit_window ψ (rescaled_test_support φ R hR hbound)
  have ha := approximable_pullback (1/(4*R)) (1/2) ψ.toBCF ψ.dt.toBCF ψ.dp.toBCF hψ
  apply identify_derivatives φ _ _ _ ha
  ext ⟨t,p⟩
  change φ.value (4*R*((1/(4*R))*t+1/2)+ -2*R,p) = φ.value (t,p)
  congr 2
  field_simp
  ring

#print axioms affineHomeomorph_apply
#print axioms affineTest
#print axioms test_time_bound
#print axioms rescaled_test_support
#print axioms smooth_test_approximable
end
end UnifiedTheory.Audit.KFCausalSmoothTestDensity
