/- Absorb the neutral Gaussian into the entire neutral profiles.
This identity isolates the positive quartic weight in the joint integral;
it does not assert a comparison between different clock slices. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralActualPositive
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralHolomorphic
noncomputable section
open KFCausalReciprocalNeutralKernel (neutral)
open KFCausalReciprocalNeutralLaplace (Joint weight)
open KFCausalReciprocalNeutralPositiveForm (profileSum positiveDensity)
open KFCausalReciprocalWedgeLaplace (laplaceSum)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalQuarticPlaneDomination (potential)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalNeutralExponentialProfiles (exponentialProfile)

def weightedProfile (β : ℝ) (F : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  Complex.exp (-(β:ℂ)*ζ^2)*F ζ

theorem gaussian_norm (β : ℝ) (r : ℂ) (y x : ℝ) :
    ‖Complex.exp (-(β:ℂ)*(neutral r y x)^2)‖^2 =
      Real.exp (-2*β*x^2+8*β*r.im^2*y^2) := by
  rw [Complex.norm_exp,← Real.exp_nat_mul]
  congr 1
  simp [neutral,Complex.mul_re,Complex.mul_im,pow_two]
  ring

theorem profileSum_weighted (n : ℕ) (β : ℝ) (w : Fin n → ℝ)
    (c : Fin n → ℂ) (F : Fin n → ℂ → ℂ) (z ζ : ℂ) :
    profileSum n w c (fun i => weightedProfile β (F i)) z ζ =
      Complex.exp (-(β:ℂ)*ζ^2)*profileSum n w c F z ζ := by
  unfold profileSum laplaceSum weightedProfile
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem density_absorbed (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c : Fin n → ℂ) (F : Fin n → ℂ → ℂ) (p : Joint) :
    positiveDensity n α β w r c F p =
      potential (p.1.2 1+fieldSlope r*p.1.2 0)*
        ‖profileSum n w c (fun i => weightedProfile β (F i))
          (chart α r (p.1.1^2+(p.1.2 0)^2) p.2)
          (neutral r (p.1.2 0) (p.1.2 1))‖^2 := by
  rw [profileSum_weighted,norm_mul,mul_pow,gaussian_norm]
  unfold positiveDensity weight
  ring

theorem weightedProfile_differentiable (β : ℝ) (b C : ℂ) (P : Polynomial ℂ) :
    Differentiable ℂ (weightedProfile β (exponentialProfile b C P)) := by
  unfold weightedProfile exponentialProfile
  fun_prop

#print axioms gaussian_norm
#print axioms profileSum_weighted
#print axioms density_absorbed
#print axioms weightedProfile_differentiable
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralHolomorphic
