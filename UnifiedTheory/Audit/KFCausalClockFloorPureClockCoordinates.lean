/- Unitary straightening of the physical clock alone. The transverse
coordinates stay fixed; this is a new observable, not a new Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalClockFloorTestPullback
import UnifiedTheory.Audit.KFCausalDenseUnitaryExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalWeightedConfigurationTests
open UnifiedTheory.Audit.KFCausalDenseUnitaryExtension

variable (ε : ℝ) (hε : 0 < ε)

def chartHomeomorph : Configuration ≃ₜ Configuration :=
  (chartIso ε hε).toHomeomorph.prodCongr (Homeomorph.refl Transverse)

def weight (x : Configuration) : ℂ := Real.sqrt (Real.exp x.1+ε)

theorem weight_continuous : Continuous (weight ε) := by unfold weight; fun_prop

include hε in
theorem weight_ne_zero (x : Configuration) : weight ε x ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'

def testCoordinates : Test ≃ₗ[ℂ] Test :=
  weightedEquiv (chartHomeomorph ε hε) (weight ε) (weight_continuous ε) (weight_ne_zero ε hε)

theorem testCoordinates_apply (f : Test) (x : Configuration) :
    testCoordinates ε hε f x = weight ε x*f (chart ε x.1,x.2) := rfl

theorem testCoordinates_square_integral (f : Test) :
    (∫ x : Configuration, ‖testCoordinates ε hε f x‖^2) = ∫ x : Configuration, ‖f x‖^2 := by
  have hd (s : ℝ) (x : Transverse) : ‖testCoordinates ε hε f (s,x)‖^2 =
      (Real.exp s+ε)*‖f (chart ε s,x)‖^2 := by
    rw [testCoordinates_apply,norm_mul,weight,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (by positivity)]
  rw [Measure.volume_eq_prod ℝ Transverse]
  rw [integral_prod _ (test_square_integrable (testCoordinates ε hε f)),
    integral_prod _ (test_square_integrable f)]
  simp_rw [hd,integral_const_mul]
  exact KFCausalCoupledTestPullback.clock_change_integral ε hε (fun q => ∫ x : Transverse, ‖f (q,x)‖^2)

theorem testCoordinates_norm (f : Test) :
    ‖embedding (testCoordinates ε hε f)‖ = ‖embedding f‖ := by
  have he : ‖embedding (testCoordinates ε hε f)‖^2 = ‖embedding f‖^2 := by
    rw [embedding_norm_square,embedding_norm_square,testCoordinates_square_integral]
  nlinarith [norm_nonneg (embedding (testCoordinates ε hε f)),norm_nonneg (embedding f)]

def coordinates : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  extension embedding embedding_dense (testCoordinates ε hε) (testCoordinates_norm ε hε)

theorem coordinates_embedding (f : Test) :
    coordinates ε hε (embedding f) = embedding (testCoordinates ε hε f) :=
  extension_embedding _ _ _ _ f

theorem coordinates_symm_embedding (f : Test) :
    (coordinates ε hε).symm (embedding f) = embedding ((testCoordinates ε hε).symm f) := by
  apply (coordinates ε hε).injective
  rw [LinearIsometryEquiv.apply_symm_apply,coordinates_embedding,LinearEquiv.apply_symm_apply]

#print axioms weight_continuous
#print axioms weight_ne_zero
#print axioms testCoordinates_apply
#print axioms testCoordinates_square_integral
#print axioms testCoordinates_norm
#print axioms coordinates
#print axioms coordinates_embedding
#print axioms coordinates_symm_embedding
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockCoordinates
