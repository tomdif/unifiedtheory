/- The quantitative quartic form bound applies to every actual finite
neutral profile at every complex translation, including the entire joint
Laplace sum. All domain and boundary hypotheses are discharged here.
The full clock-response derivative is a separate remaining obligation. -/
import UnifiedTheory.Audit.KFCausalNeutralQuarticFormBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralJointCurvatureForm
noncomputable section
open KFCausalNeutralLinePackets (entire step)
open KFCausalNeutralLineDomain (family Regular)
open KFCausalNeutralQuarticFormBound (energy first second)
open KFCausalReciprocalNeutralHolomorphic (weightedProfile)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalReciprocalNeutralPositiveForm (profileSum)
open KFCausalReciprocalWedgeLaplace (laplaceSum)

theorem translated_family_derivative (n : ℕ) (β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => family n β b c P ((t:ℂ)+z))
      (family n β b c (fun i => step β (b i) (P i)) ((x:ℂ)+z)) x := by
  have he := (KFCausalNeutralLineDomain.family_derivative n β b c P ((x:ℂ)+z)).comp
    (x:ℂ) ((hasDerivAt_id (x:ℂ)).add_const z)
  simpa only [mul_one] using he.comp_ofReal

theorem family_form_bound (n : ℕ) (β : ℝ) (hβ : 0 < β) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (z : ℂ) (η L : ℝ) :
    let f := fun x : ℝ => family n β b c P ((x:ℂ)+z)
    let g := fun x : ℝ => family n β b c (fun i => step β (b i) (P i)) ((x:ℂ)+z)
    (first η L f g)^2-4*(L^2+η^2)*(energy f)^2 ≤ energy f*second η L f g := by
  exact KFCausalNeutralQuarticFormBound.curvature_form_bound η L _ _
    (KFCausalNeutralLineDomain.family_regular n β hβ b c P z)
    (KFCausalNeutralLineDomain.family_regular n β hβ b c _ z)
    (translated_family_derivative n β b c P z)

theorem family_second_lower (n : ℕ) (β : ℝ) (hβ : 0 < β) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (z : ℂ) (η L : ℝ) :
    let f := fun x : ℝ => family n β b c P ((x:ℂ)+z)
    let g := fun x : ℝ => family n β b c (fun i => step β (b i) (P i)) ((x:ℂ)+z)
    (-4*(L^2+η^2)*energy f) ≤ second η L f g := by
  dsimp only
  have he := KFCausalNeutralQuarticFormBound.second_lower η L _ _
    (KFCausalNeutralLineDomain.family_regular n β hβ b c P z)
    (KFCausalNeutralLineDomain.family_regular n β hβ b c _ z)
    (translated_family_derivative n β b c P z)
  have hp := KFCausalNeutralQuarticFormBound.energy_nonnegative
    (fun x => KFCausalQuarticNeutralDefect.direction η L x
      (family n β b c P ((x:ℂ)+z)) (family n β b c (fun i => step β (b i) (P i)) ((x:ℂ)+z)))
  linarith

theorem weightedProfile_entire (β : ℝ) (b c : ℂ) (P : Polynomial ℂ) (z : ℂ) :
    weightedProfile β (exponentialProfile b c P) z = c*entire β b P z := by
  unfold weightedProfile exponentialProfile entire
  rw [Complex.exp_add]
  ring

def coefficients (n : ℕ) (w : Fin n → ℝ) (c : Fin n → ℂ) (z : ℂ) (i : Fin n) : ℂ :=
  c i*(w i:ℂ)*Complex.exp (-(w i:ℂ)*z)

theorem joint_profile_family (n : ℕ) (β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (z ζ : ℂ) :
    profileSum n w c (fun i => weightedProfile β (exponentialProfile (b i) 1 (P i))) z ζ =
      family n β b (coefficients n w c z) P ζ := by
  unfold profileSum laplaceSum family
  simp only [weightedProfile_entire,one_mul]
  apply Finset.sum_congr rfl
  intro i _
  unfold coefficients
  ring

theorem joint_form_bound (n : ℕ) (β : ℝ) (hβ : 0 < β) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (z ζ : ℂ) (η L : ℝ) :
    let f := fun x : ℝ => profileSum n w c
      (fun i => weightedProfile β (exponentialProfile (b i) 1 (P i))) z ((x:ℂ)+ζ)
    let g := fun x : ℝ => profileSum n w c
      (fun i => weightedProfile β (exponentialProfile (b i) 1 (step β (b i) (P i)))) z ((x:ℂ)+ζ)
    (first η L f g)^2-4*(L^2+η^2)*(energy f)^2 ≤ energy f*second η L f g := by
  dsimp only
  simp_rw [joint_profile_family]
  exact family_form_bound n β hβ b (coefficients n w c z) P ζ η L

#print axioms translated_family_derivative
#print axioms family_form_bound
#print axioms family_second_lower
#print axioms weightedProfile_entire
#print axioms joint_profile_family
#print axioms joint_form_bound
end
end UnifiedTheory.Audit.KFCausalNeutralJointCurvatureForm
