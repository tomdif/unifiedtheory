/- Actual charge coordinates of the paired quadratic tensor state.
The two constant Fourier moments cancel. The physical width matching
turns the remaining multiplier into half the radial imbalance. -/
import UnifiedTheory.Audit.KFCausalPairedQuadraticStates
import UnifiedTheory.Audit.KFCausalChargeZeroSwapWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalPairedQuadraticChargeCoordinates
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalEuclideanProductCoordinates (Block Joint split coordinates_coe split_preserves_volume)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalPhysicalMixedCoordinates (mixedCoordinates mixedCoordinates_functions_coe)
open KFCausalChargeGaussianProducts (gaussian gaussian_integrable gaussian_memLp spectator spectator_memLp)
open KFCausalChargeGaussianGeometry (profile)
open KFCausalChargeGaussianIdentities (mixed_profile_identity)
open KFCausalPairedQuadraticFourier
  (difference difference_integrable difference_memLp difference_fourier)
open KFCausalPairedQuadraticStates
open KFCausalChargeZeroSwapWitness (imbalance imbalanceRaw)

variable (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
  (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)

theorem left_coordinates_coe :
    chargeCoordinates (leftState α β hα hβ g hc hg) =ᵐ[volume]
      fun x => (𝓕 (gaussian 2 α)) (split 2 4 x).1 *
        spectatorDifference α β g (split 2 4 x).2 := by
  have hm := mixedCoordinates_functions_coe (gaussian 2 α) (spectatorDifference α β g)
    (gaussian_integrable 2 α hα) (gaussian_memLp 2 α hα)
    (spectatorDifference_memLp α β hα hβ g hc hg)
  filter_upwards [coordinates_coe 2 4 (mixedCoordinates (leftState α β hα hβ g hc hg)),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae hm] with x hx hp
  exact hx.trans hp

theorem right_coordinates_coe :
    chargeCoordinates (rightState α β hα hβ g hc hg) =ᵐ[volume]
      fun x => (𝓕 (difference α)) (split 2 4 x).1 * spectator α β g (split 2 4 x).2 := by
  have hm := mixedCoordinates_functions_coe (difference α) (spectator α β g)
    (difference_integrable α hα) (difference_memLp α hα)
    (spectator_memLp α β hα hβ g hc hg)
  filter_upwards [coordinates_coe 2 4 (mixedCoordinates (rightState α β hα hβ g hc hg)),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae hm] with x hx hp
  exact hx.trans hp

def mixedProfile (c : ℝ) (x : Joint 2 4) : ℂ :=
  (imbalance c x:ℂ)/2 * (((Real.pi/α:ℝ):ℂ)*profile α β c g x)

include hα in
theorem mixed_identity (c : ℝ) (hmatch : Real.pi^2/α = α*c^2) (x : Joint 2 4) :
    (1/2:ℂ)*((𝓕 (gaussian 2 α)) (split 2 4 x).1 *
        spectatorDifference α β g (split 2 4 x).2 -
      (𝓕 (difference α)) (split 2 4 x).1 * spectator α β g (split 2 4 x).2) =
      mixedProfile α β g c x := by
  have hr : Real.pi^2/α^2 = c^2 := by
    have he := (div_eq_iff hα.ne').mp hmatch
    apply (div_eq_iff (pow_ne_zero 2 hα.ne')).mpr
    nlinarith only [he]
  have hrc : (Real.pi:ℂ)^2/(α:ℂ)^2 = (c:ℂ)^2 := by exact_mod_cast hr
  rw [spectatorDifference_polynomial,difference_fourier α hα]
  calc
    _ = (1/2:ℂ)*(((split 2 4 x).2 1:ℂ)^2-((split 2 4 x).2 2:ℂ)^2+
        (Real.pi:ℂ)^2/(α:ℂ)^2*
          (((split 2 4 x).1 0:ℂ)^2-((split 2 4 x).1 1:ℂ)^2)) *
        ((𝓕 (gaussian 2 α)) (split 2 4 x).1 * spectator α β g (split 2 4 x).2) := by ring
    _ = _ := by
      rw [hrc,mixed_profile_identity α β c hα hmatch g x]
      unfold mixedProfile imbalance imbalanceRaw KFCausalNormalizedChargeFlow.dilate
      simp only [KFCausalEuclideanProductCoordinates.split_fst,
        KFCausalEuclideanProductCoordinates.split_snd]
      push_cast
      ring

theorem state_coordinates_coe (c : ℝ) (hmatch : Real.pi^2/α = α*c^2) :
    chargeCoordinates (state α β hα hβ g hc hg) =ᵐ[volume] mixedProfile α β g c := by
  rw [state,map_smul,map_sub]
  filter_upwards [Lp.coeFn_smul (1/2:ℂ)
    (chargeCoordinates (leftState α β hα hβ g hc hg)-
      chargeCoordinates (rightState α β hα hβ g hc hg)),
    Lp.coeFn_sub (chargeCoordinates (leftState α β hα hβ g hc hg))
      (chargeCoordinates (rightState α β hα hβ g hc hg)),
    left_coordinates_coe α β hα hβ g hc hg,
    right_coordinates_coe α β hα hβ g hc hg] with x h0 h1 h2 h3
  rw [h0,Pi.smul_apply,smul_eq_mul,h1,Pi.sub_apply,h2,h3]
  exact mixed_identity α β hα g c hmatch x

#print axioms left_coordinates_coe
#print axioms right_coordinates_coe
#print axioms mixed_identity
#print axioms state_coordinates_coe
end
end UnifiedTheory.Audit.KFCausalPairedQuadraticChargeCoordinates
