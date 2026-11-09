/- The actual six-coordinate straightening pullback is a linear
equivalence of compactly supported continuous tests and preserves the
physical L2 norm. Both Jacobian factors are derived from the model. -/
import UnifiedTheory.Audit.KFCausalWeightedConfigurationTests
import UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
import UnifiedTheory.Audit.KFCausalTransverseDilationPullback
import Mathlib.MeasureTheory.Function.JacobianOneDim

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoupledTestPullback
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseDilationPullback
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalWeightedConfigurationTests
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph

def weight (ε : ℝ) (x : Configuration) : ℂ := amplitude ε x.1

theorem weight_continuous (ε : ℝ) : Continuous (weight ε) :=
  Complex.continuous_ofReal.comp ((amplitude_continuous ε).comp continuous_fst)

theorem weight_ne_zero (ε : ℝ) (hε : 0 < ε) (x : Configuration) : weight ε x ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (amplitude_positive ε x.1 hε).ne'

def testPullback (ε : ℝ) (hε : 0 < ε) : Test ≃ₗ[ℂ] Test :=
  weightedEquiv (coordinateHomeomorph ε hε) (weight ε) (weight_continuous ε) (weight_ne_zero ε hε)

theorem testPullback_apply (ε : ℝ) (hε : 0 < ε) (f : Test) (x : Configuration) :
    testPullback ε hε f x = (Real.sqrt (Real.exp x.1+ε):ℂ)*
      pullback (phase ε x.1) (fun y => f (chart ε x.1,y)) x.2 := by
  simp only [testPullback,weightedEquiv_apply,weight,amplitude,coordinateHomeomorph_apply,
    pullback,Complex.ofReal_mul,mul_assoc]

theorem testPullback_slice_square (ε : ℝ) (hε : 0 < ε) (f : Test) (s : ℝ) :
    (∫ x : Transverse, ‖testPullback ε hε f (s,x)‖^2) =
      (Real.exp s+ε)*(∫ x : Transverse, ‖f (chart ε s,x)‖^2) := by
  have hd (x : Transverse) : ‖testPullback ε hε f (s,x)‖^2 =
      (Real.exp s+ε)*‖pullback (phase ε s) (fun y => f (chart ε s,y)) x‖^2 := by
    rw [testPullback_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (by positivity)]
  simp_rw [hd]
  rw [integral_const_mul,pullback_square_integral]

theorem clock_change_integral (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℝ) :
    (∫ s, (Real.exp s+ε)*g (chart ε s)) = ∫ q, g q := by
  have hh := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun s (_ : s ∈ (univ : Set ℝ)) => (chart_derivative ε s).hasDerivWithinAt)
    (chart_strictMono ε hε).injective.injOn g
  have hw (s : ℝ) : |Real.exp s+ε|=Real.exp s+ε := abs_of_pos (by positivity)
  simpa only [image_univ,(chart_surjective ε hε).range_eq,setIntegral_univ,hw,smul_eq_mul] using hh.symm

theorem testPullback_square_integral (ε : ℝ) (hε : 0 < ε) (f : Test) :
    (∫ x : Configuration, ‖testPullback ε hε f x‖^2) = ∫ x : Configuration, ‖f x‖^2 := by
  rw [Measure.volume_eq_prod ℝ Transverse]
  rw [integral_prod _ (test_square_integrable (testPullback ε hε f)),
    integral_prod _ (test_square_integrable f)]
  simp_rw [testPullback_slice_square]
  exact clock_change_integral ε hε (fun q => ∫ x : Transverse, ‖f (q,x)‖^2)

theorem testPullback_physical_norm (ε : ℝ) (hε : 0 < ε) (f : Test) :
    ‖embedding (testPullback ε hε f)‖ = ‖embedding f‖ := by
  have he : ‖embedding (testPullback ε hε f)‖^2 = ‖embedding f‖^2 := by
    rw [embedding_norm_square,embedding_norm_square,testPullback_square_integral]
  nlinarith [norm_nonneg (embedding (testPullback ε hε f)),norm_nonneg (embedding f)]

#print axioms testPullback
#print axioms testPullback_apply
#print axioms testPullback_slice_square
#print axioms clock_change_integral
#print axioms testPullback_square_integral
#print axioms testPullback_physical_norm

end
end UnifiedTheory.Audit.KFCausalCoupledTestPullback
