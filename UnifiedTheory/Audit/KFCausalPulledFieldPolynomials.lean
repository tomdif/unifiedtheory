/- Exact polynomial representatives of a physical field and its square
on the repaired product trials. The full transverse shear is retained. -/
import UnifiedTheory.Audit.KFCausalFieldPolynomialPackets
import UnifiedTheory.Audit.KFCausalShiftedFieldCoefficient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPulledFieldPolynomials
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
open UnifiedTheory.Audit.KFCausalCoupledTestPullback
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalTransversePositionMoments
open UnifiedTheory.Audit.KFCausalFieldPolynomialPackets
open UnifiedTheory.Audit.KFCausalFieldCoefficientTrials
open UnifiedTheory.Audit.KFCausalShiftedFieldCoefficient

theorem shiftedWeighted_real_power (ε a p q : ℝ) (hε : 0 < ε) (j : ℕ) :
    shiftedWeighted ε a j p 0 q =
      (scale (phase ε ((chartIso ε hε).symm q)):ℂ)^j*modulate p (realTrial ε a) q := by
  rw [shiftedWeighted_zero]
  unfold modulate
  rw [weightedLine_real ε a j hε]
  have he : Real.exp (((j:ℝ)/2)*phase ε ((chartIso ε hε).symm q)) =
      (scale (phase ε ((chartIso ε hε).symm q)))^j := by
    rw [scale,← Real.exp_nat_mul]
    congr 1
    ring
  rw [he,Complex.ofReal_pow]
  change _ = _*( _*(KFCausalCoupledDampedGaussian.dampedGaussian ε a q:ℂ))
  ring

theorem pulledField_decomposition (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ)
    (z : Configuration) :
    pulledField ε hε l z = constantField l (transverseCoordinates z.2)+
      scale (phase ε ((chartIso ε hε).symm z.1))*scaleField l (transverseCoordinates z.2) :=
  field_flow_decomposition l _ _

theorem pulledField_at_coordinate (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ)
    (z : Configuration) : pulledField ε hε l (coordinateHomeomorph ε hε z)=l z.2 := by
  simp only [pulledField,Homeomorph.symm_apply_apply]

def monomialFunction (ε a p : ℝ) (l : Transverse →L[ℝ] ℝ) (i j : ℕ)
    (ψ : SchwartzMap TailSpace ℂ) : Configuration → ℂ :=
  configurationProduct (shiftedWeighted ε a j p 0) (polynomialPacket l i j ψ)

theorem linear_polynomial (ε a p : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ)
    (ψ : SchwartzMap TailSpace ℂ) :
    monomialFunction ε a p l 1 0 ψ+monomialFunction ε a p l 0 1 ψ =
      fun z => (pulledField ε hε l z:ℂ)*configurationProduct (modulate p (realTrial ε a)) ψ z := by
  funext z
  simp only [Pi.add_apply,monomialFunction,configurationProduct,shiftedWeighted_real_power ε a p _ hε,
    polynomialPacket_apply,pow_zero,pow_one,pulledField_decomposition,
    Complex.ofReal_add,Complex.ofReal_mul]
  ring

theorem quadratic_polynomial (ε a p : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ)
    (ψ : SchwartzMap TailSpace ℂ) :
    monomialFunction ε a p l 2 0 ψ+(2:ℂ) • monomialFunction ε a p l 1 1 ψ+
      monomialFunction ε a p l 0 2 ψ =
      fun z => (pulledField ε hε l z:ℂ)^2*configurationProduct (modulate p (realTrial ε a)) ψ z := by
  funext z
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,monomialFunction,configurationProduct,
    shiftedWeighted_real_power ε a p _ hε,polynomialPacket_apply,pow_zero,pow_one,
    pulledField_decomposition,Complex.ofReal_add,Complex.ofReal_mul]
  ring

theorem weighted_linear_polynomial (ε a p : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ)
    (ψ : SchwartzMap TailSpace ℂ) (z : Configuration) :
    weightedFunction ε hε (monomialFunction ε a p l 1 0 ψ) z+
      weightedFunction ε hε (monomialFunction ε a p l 0 1 ψ) z =
      (l z.2:ℂ)*weightedFunction ε hε (configurationProduct (modulate p (realTrial ε a)) ψ) z := by
  have h := congrFun (linear_polynomial ε a p hε l ψ) (coordinateHomeomorph ε hε z)
  simp only [Pi.add_apply,pulledField_at_coordinate] at h
  simp only [weightedFunction]
  linear_combination weight ε z*h

theorem weighted_quadratic_polynomial (ε a p : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ)
    (ψ : SchwartzMap TailSpace ℂ) (z : Configuration) :
    weightedFunction ε hε (monomialFunction ε a p l 2 0 ψ) z+
      (2:ℂ)*weightedFunction ε hε (monomialFunction ε a p l 1 1 ψ) z+
      weightedFunction ε hε (monomialFunction ε a p l 0 2 ψ) z =
      (l z.2:ℂ)^2*weightedFunction ε hε (configurationProduct (modulate p (realTrial ε a)) ψ) z := by
  have h := congrFun (quadratic_polynomial ε a p hε l ψ) (coordinateHomeomorph ε hε z)
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,pulledField_at_coordinate] at h
  simp only [weightedFunction]
  linear_combination weight ε z*h

#print axioms shiftedWeighted_real_power
#print axioms pulledField_decomposition
#print axioms pulledField_at_coordinate
#print axioms linear_polynomial
#print axioms quadratic_polynomial
#print axioms weighted_linear_polynomial
#print axioms weighted_quadratic_polynomial

end
end UnifiedTheory.Audit.KFCausalPulledFieldPolynomials
