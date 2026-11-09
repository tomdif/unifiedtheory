/- Actual finite tensor states for the quartic charge calculation.
Both configuration and partial-Fourier representatives come from the
established unitary coordinate maps and integrable Gaussian moments. -/
import UnifiedTheory.Audit.KFCausalQuarticChargeAlgebra
import UnifiedTheory.Audit.KFCausalPairedQuadraticStates
import UnifiedTheory.Audit.KFCausalFiniteLpRepresentatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalQuarticTensorStates
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalEuclideanConfiguration (Space euclideanPullback euclideanPullback_coe)
open KFCausalEuclideanProductCoordinates (Block Joint split coordinates_coe split_preserves_volume)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalPhysicalMixedCoordinates
  (pairedState pairedState_position_coe mixedCoordinates mixedCoordinates_functions_coe)
open KFCausalGaussianQuadraticFourier (moment)
open KFCausalPairedQuadraticFourier (product product_gaussian product_integrable product_memLp)
open KFCausalPairedQuadraticStates (spectatorProduct spectatorProduct_memLp spectatorProduct_zero)
open KFCausalChargeGaussianProducts (gaussian spectator)
open KFCausalChargeGaussianIdentities (configurationProfile positionProfile paired_profile_identity)
open KFCausalPairedModeCoordinates (scale)
open KFCausalQuarticChargeAlgebra (powers monomial transformedMonomial product_fourier)
open KFCausalFiniteLpRepresentatives (weighted_sum_coe)

theorem product_polynomial (α : ℝ) (n m : ℕ) (u : Block 2) :
    product α n m u = (u 0:ℂ)^n*(u 1:ℂ)^m*gaussian 2 α u := by
  rw [← product_gaussian]
  simp only [product,moment,pow_zero,one_mul]
  ring

theorem spectator_polynomial (α β : ℝ) (g : ℝ → ℂ) (n m : ℕ) (v : Block 4) :
    spectatorProduct α β g n m v = (v 1:ℂ)^n*(v 2:ℂ)^m*spectator α β g v := by
  rw [← spectatorProduct_zero]
  simp only [spectatorProduct,moment,pow_zero,one_mul]
  ring

def configurationMonomial (i : Fin 15) (x : Configuration) : ℂ :=
  monomial i (scale*(x.2 0-x.2 1):ℝ) (scale*(x.2 2-x.2 3):ℝ)
    (scale*(x.2 0+x.2 1):ℝ) (scale*(x.2 2+x.2 3):ℝ)
def positionMonomial (i : Fin 15) (x : Space) : ℂ :=
  monomial i (scale*(x 1-x 2):ℝ) (scale*(x 3-x 4):ℝ)
    (scale*(x 1+x 2):ℝ) (scale*(x 3+x 4):ℝ)
def configurationDensity (α β : ℝ) (g : ℝ → ℂ) (d : Fin 15 → ℂ) (x : Configuration) : ℂ :=
  (∑ i, d i*configurationMonomial i x)*configurationProfile α β g x
def mixedDensity (α β : ℝ) (g : ℝ → ℂ) (d : Fin 15 → ℂ) (x : Joint 2 4) : ℂ :=
  (∑ i, d i*transformedMonomial α i ((split 2 4 x).1 0) ((split 2 4 x).1 1)
    ((split 2 4 x).2 1) ((split 2 4 x).2 2))*
      ((𝓕 (gaussian 2 α)) (split 2 4 x).1*spectator α β g (split 2 4 x).2)

variable (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
  (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)

def tensorState (i : Fin 15) : Hilbert :=
  pairedState ((product_memLp α hα (powers i 0) (powers i 1)).toLp
    (product α (powers i 0) (powers i 1)))
    ((spectatorProduct_memLp α β hα hβ g hc hg (powers i 2) (powers i 3)).toLp
      (spectatorProduct α β g (powers i 2) (powers i 3)))
def state (d : Fin 15 → ℂ) : Hilbert := ∑ i, d i • tensorState α β hα hβ g hc hg i

theorem tensor_position_coe (i : Fin 15) :
    euclideanPullback (tensorState α β hα hβ g hc hg i) =ᵐ[volume]
      fun x => positionMonomial i x*positionProfile α β g x := by
  have he := pairedState_position_coe
    (product α (powers i 0) (powers i 1)) (spectatorProduct α β g (powers i 2) (powers i 3))
    (product_memLp α hα _ _) (spectatorProduct_memLp α β hα hβ g hc hg _ _)
  filter_upwards [he] with x hx
  change euclideanPullback (tensorState α β hα hβ g hc hg i) x = _ at hx
  rw [hx,product_polynomial,spectator_polynomial]
  rw [← paired_profile_identity α β g x]
  change
    (((scale*(x 1-x 2):ℝ):ℂ)^(powers i 0)*((scale*(x 3-x 4):ℝ):ℂ)^(powers i 1)*_)*
      (((scale*(x 1+x 2):ℝ):ℂ)^(powers i 2)*((scale*(x 3+x 4):ℝ):ℂ)^(powers i 3)*_) = _
  unfold positionMonomial monomial
  ring

theorem tensor_configuration_coe (i : Fin 15) :
    tensorState α β hα hβ g hc hg i =ᵐ[volume]
      fun x => configurationMonomial i x*configurationProfile α β g x := by
  have he : (fun x : Space =>
      (tensorState α β hα hβ g hc hg i) (KFCausalEuclideanConfiguration.split x)) =ᵐ[volume]
      fun x => configurationMonomial i (KFCausalEuclideanConfiguration.split x)*
        configurationProfile α β g (KFCausalEuclideanConfiguration.split x) := by
    filter_upwards [euclideanPullback_coe (tensorState α β hα hβ g hc hg i),
      tensor_position_coe α β hα hβ g hc hg i] with x hx hp
    have hx' : (tensorState α β hα hβ g hc hg i) (KFCausalEuclideanConfiguration.split x) =
        positionMonomial i x*positionProfile α β g x := hx.symm.trans hp
    rw [hx',KFCausalChargeGaussianIdentities.configurationProfile_split]
    rfl
  have ht := KFCausalEuclideanConfiguration.split_preserves_volume.symm.quasiMeasurePreserving.ae he
  filter_upwards [ht] with x hx
  simpa only [MeasurableEquiv.apply_symm_apply] using hx

theorem tensor_coordinates_coe (i : Fin 15) :
    chargeCoordinates (tensorState α β hα hβ g hc hg i) =ᵐ[volume]
      fun x => transformedMonomial α i ((split 2 4 x).1 0) ((split 2 4 x).1 1)
        ((split 2 4 x).2 1) ((split 2 4 x).2 2)*
          ((𝓕 (gaussian 2 α)) (split 2 4 x).1*spectator α β g (split 2 4 x).2) := by
  have hm := mixedCoordinates_functions_coe
    (product α (powers i 0) (powers i 1)) (spectatorProduct α β g (powers i 2) (powers i 3))
    (product_integrable α hα _ _) (product_memLp α hα _ _)
    (spectatorProduct_memLp α β hα hβ g hc hg _ _)
  filter_upwards [coordinates_coe 2 4 (mixedCoordinates (tensorState α β hα hβ g hc hg i)),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae hm] with x hx hp
  refine (hx.trans hp).trans ?_
  rw [product_fourier α hα,spectator_polynomial]
  unfold transformedMonomial
  ring

theorem state_configuration_coe (d : Fin 15 → ℂ) :
    state α β hα hβ g hc hg d =ᵐ[volume] configurationDensity α β g d := by
  have he := weighted_sum_coe volume d (tensorState α β hα hβ g hc hg)
    (fun i x => configurationMonomial i x*configurationProfile α β g x)
    (tensor_configuration_coe α β hα hβ g hc hg)
  filter_upwards [he] with x hx
  change (∑ i, d i • tensorState α β hα hβ g hc hg i : Hilbert) x = _
  rw [hx]
  simp only [configurationDensity,Finset.sum_mul,mul_assoc]

theorem state_coordinates_coe (d : Fin 15 → ℂ) :
    chargeCoordinates (state α β hα hβ g hc hg d) =ᵐ[volume] mixedDensity α β g d := by
  rw [state,map_sum]
  simp only [map_smul]
  have he := weighted_sum_coe volume d (fun i => chargeCoordinates (tensorState α β hα hβ g hc hg i))
    _ (tensor_coordinates_coe α β hα hβ g hc hg)
  filter_upwards [he] with x hx
  rw [hx]
  simp only [mixedDensity,Finset.sum_mul,mul_assoc]

#print axioms product_polynomial
#print axioms spectator_polynomial
#print axioms tensor_position_coe
#print axioms tensor_configuration_coe
#print axioms tensor_coordinates_coe
#print axioms state_configuration_coe
#print axioms state_coordinates_coe
end
end UnifiedTheory.Audit.KFCausalQuarticTensorStates
