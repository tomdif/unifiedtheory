/- Match the arbitrary-L field kernel to the exact original orientation
and width normalization. The field bound is on the original joint integral. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianFieldFamily
import UnifiedTheory.Audit.KFCausalOriginalCommonRealGaussianEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianOriginalField
noncomputable section
open MeasureTheory
open scoped ComplexConjugate BigOperators
open KFCausalChargedEvenMomentImaginaryBound (gamma)
open KFCausalChargedCoolingWidthPositive (widthSum)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalGaussianSourceKernelDerivative (slope)
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)

def originalFieldSlope (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (B : ℝ) (c : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*
    slope (KFCausalReciprocalCrossGeometry.B α (w i) (w j) r)
      (conj (KFCausalReciprocalCrossGeometry.B α (w i) (w j) r))
      (KFCausalReciprocalCrossGeometry.C α β (w i) (w j) r)
      0 (2*(B:ℂ)) 0 0 0 0 β (fieldSlope r) 1

theorem charged_width (α w v : ℝ) (r : ℂ) :
    KFCausalReciprocalCrossGeometry.B α w v r=widthSum (gamma α r) v w := by
  unfold KFCausalReciprocalCrossGeometry.B widthSum gamma
  simp only [map_mul,map_div₀,map_pow,Complex.conj_ofReal,map_ofNat]
  push_cast
  ring

theorem original_field_eq (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (B : ℝ) (c : Fin n → ℂ) :
    originalFieldSlope n α β w r B c =
      KFCausalCommonRealGaussianFieldFamily.familyFieldSlope β B (fieldSlope r)
        (gamma α r) (8*β*r.im^2) w (fun i => c i*(w i:ℂ)) := by
  unfold originalFieldSlope KFCausalCommonRealGaussianFieldFamily.familyFieldSlope
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [KFCausalReciprocalCrossGeometry.C,charged_width]
  simp only [map_mul,Complex.conj_ofReal]
  ring

theorem original_field_derivative (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (B : ℝ) (c : Fin n → ℂ) (hβ : 0 < β)
    (hp : 0 < (gamma α r).re) (hw : ∀ i, 0 < w i)
    (hd : ∀ i, 8*β*r.im^2 < 2*(gamma α r).re*w i) :
    HasDerivAt (fun L => KFCausalCommonRealGaussianEnergy.energy β B L (gamma α r)
      (8*β*r.im^2) w (fun i => c i*(w i:ℂ)))
      (originalFieldSlope n α β w r B c).re (fieldSlope r) := by
  rw [original_field_eq]
  exact KFCausalCommonRealGaussianFieldFamily.actual_field_derivative β B (fieldSlope r)
    (gamma α r) (8*β*r.im^2) w (fun i => c i*(w i:ℂ)) hβ hp hw hd

theorem original_field_bounds (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (B : ℝ) (c : Fin n → ℂ) (hβ : 0 < β)
    (hp : 0 < (gamma α r).re) (hw : ∀ i, 0 < w i)
    (hd : ∀ i, 8*β*r.im^2 < 2*(gamma α r).re*w i) :
    0 ≤ fieldSlope r*(originalFieldSlope n α β w r B c).re ∧
    fieldSlope r*(originalFieldSlope n α β w r B c).re ≤
      4*(∫ z, positiveDensity n α β w r c (fun _ => exponentialProfile (B:ℂ) 1 1) z ∂jointMeasure) := by
  rw [KFCausalOriginalCommonRealGaussianEnergy.original_energy n α β B w r c hβ hp hw hd,
    original_field_eq]
  exact KFCausalCommonRealGaussianFieldFamily.field_slope_bounds β B (fieldSlope r)
    (gamma α r) (8*β*r.im^2) w (fun i => c i*(w i:ℂ)) hβ hp hw hd

#print axioms charged_width
#print axioms original_field_eq
#print axioms original_field_derivative
#print axioms original_field_bounds
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianOriginalField
