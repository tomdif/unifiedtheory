/- The exact mixed square applies to the actual correlated joint
Laplace/neutral profile. Its charged derivative and all neutral domain
and integration-by-parts hypotheses are derived from the finite packets. -/
import UnifiedTheory.Audit.KFCausalJointFourierDissipationMixedSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalJointFourierDissipationMixedPackets
noncomputable section
open MeasureTheory
open KFCausalNeutralLineDomain (family Regular)
open KFCausalNeutralLinePackets (entire step)
open KFCausalNeutralJointCurvatureForm (coefficients translated_family_derivative)
open KFCausalNeutralQuarticFormBound (energy)
open KFCausalQuarticNeutralDefect (direction)
open KFCausalJointFourierDissipationMixedSquare

variable (n : ℕ) (β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

def profile (z ζ : ℂ) : ℂ := family n β b (coefficients n w c z) P ζ

def chargedProfile (z ζ : ℂ) : ℂ :=
  family n β b (fun i => -(w i:ℂ)*coefficients n w c z i) P ζ

theorem charged_derivative (z ζ : ℂ) :
    HasDerivAt (fun q => profile n β w b c P q ζ) (chargedProfile n β w b c P z ζ) z := by
  have hd (i : Fin n) : HasDerivAt (fun q => coefficients n w c q i*entire β (b i) (P i) ζ)
      (-(w i:ℂ)*coefficients n w c z i*entire β (b i) (P i) ζ) z := by
    have he := (((hasDerivAt_id z).const_mul (-(w i:ℂ))).cexp.const_mul
      (c i*(w i:ℂ))).mul_const (entire β (b i) (P i) ζ)
    convert he using 1
    simp only [coefficients,id_eq]
    ring
  unfold profile chargedProfile family
  exact HasDerivAt.fun_sum (fun i _ => hd i)

theorem neutral_derivative (z ζ : ℂ) :
    HasDerivAt (profile n β w b c P z)
      (profile n β w b c (fun i => step β (b i) (P i)) z ζ) ζ :=
  KFCausalNeutralLineDomain.family_derivative n β b (coefficients n w c z) P ζ

theorem charged_neutral_derivative (z ζ : ℂ) :
    HasDerivAt (chargedProfile n β w b c P z)
      (chargedProfile n β w b c (fun i => step β (b i) (P i)) z ζ) ζ :=
  KFCausalNeutralLineDomain.family_derivative n β b _ P ζ

theorem actual_mixed_square (hβ : 0 < β) (u v Y η L : ℝ) (z ζ d : ℂ) :
    let f := fun x : ℝ => profile n β w b c P z ((x:ℂ)+ζ)
    let g := fun x : ℝ => profile n β w b c (fun i => step β (b i) (P i)) z ((x:ℂ)+ζ)
    let k := fun x : ℝ => profile n β w b c (fun i => step β (b i) (step β (b i) (P i))) z ((x:ℂ)+ζ)
    let C := fun x : ℝ => d*chargedProfile n β w b c P z ((x:ℂ)+ζ)
    let Cg := fun x : ℝ => d*chargedProfile n β w b c (fun i => step β (b i) (P i)) z ((x:ℂ)+ζ)
    (∫ x, reducedDensity u v Y η L x (f x) (g x) (k x) (C x) (Cg x)) =
      Y*(energy (fun x => direction η L x (f x) (g x)+(2*(v:ℂ))*C x)+
        4*u^2*energy C+(L^2+η^2)/4*curvature f) := by
  apply complete_mixed_square u v Y η L
  · exact KFCausalNeutralLineDomain.family_regular n β hβ b _ P ζ
  · exact KFCausalNeutralLineDomain.family_regular n β hβ b _ _ ζ
  · exact KFCausalNeutralLineDomain.family_regular n β hβ b _ _ ζ
  · exact KFCausalNeutralLineDomain.regular_const_mul _
      (KFCausalNeutralLineDomain.family_regular n β hβ b _ P ζ) d
  · exact KFCausalNeutralLineDomain.regular_const_mul _
      (KFCausalNeutralLineDomain.family_regular n β hβ b _ _ ζ) d
  · exact translated_family_derivative n β b _ P ζ
  · exact translated_family_derivative n β b _ _ ζ
  · intro x
    exact (translated_family_derivative n β b _ P ζ x).const_mul d

#print axioms charged_derivative
#print axioms neutral_derivative
#print axioms charged_neutral_derivative
#print axioms actual_mixed_square
end
end UnifiedTheory.Audit.KFCausalJointFourierDissipationMixedPackets
