/- Actual paired Gaussian states with one common width for both symmetric
position modes and reciprocal width for both antisymmetric position modes.
Their physical mixed-coordinate density has the same width in all four
charged coordinates. Domain construction is supplied separately. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianStates
import UnifiedTheory.Audit.KFCausalPairedQuarticCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedGaussianStates
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalEuclideanProductCoordinates (Block Joint split split_fst split_snd coordinates_coe split_preserves_volume)
open KFCausalEuclideanConfiguration (Space euclideanPullback euclideanPullback_coe)
open KFCausalPhysicalMixedCoordinates (pairedState pairedState_position_coe mixedCoordinates mixedCoordinates_functions_coe)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalPairedModeCoordinates (scale scale_square)
open KFCausalReciprocalGaussianFourier (product product_memLp product_integrable product_fourier)
open KFCausalReciprocalGaussianStates (spectator spectator_memLp)
open KFCausalGaussianSliceDomain (gaussian gaussian_continuous gaussian_memLp_iff)
open KFCausalChargeGaussianGeometry (radius radius_coordinates radius_flow)
open KFCausalChargeZeroSwapWitness (imbalance imbalanceRaw imbalance_flow)
open KFCausalNormalizedChargeFlow (flowEquiv dilate)
open KFCausalChargedPairCoordinates (pairPolynomial)
open KFCausalQuarticChargeProfiles (chargedRadius)

def quadratic (w : ℝ) (q : Transverse) : ℝ :=
  ((q 0-q 1)^2+(q 2-q 3)^2)/(2*w)+w*((q 0+q 1)^2+(q 2+q 3)^2)/2

def configurationDensity (α β w : ℝ) (g : ℝ → ℂ) (x : Configuration) : ℂ :=
  g x.1*Complex.exp (-((α*quadratic w x.2+β*(x.2 4)^2:ℝ):ℂ))
def coordinateDensity (α β w c : ℝ) (g : ℝ → ℂ) (x : Joint 2 4) : ℂ :=
  (Real.pi*w/α:ℝ)*g (x (.inr 0))*
    Complex.exp (-((α*w*radius c x+β*(x (.inr 3))^2:ℝ):ℂ))

theorem coordinateDensity_continuous (α β w c : ℝ) (g : ℝ → ℂ) (hc : Continuous g) :
    Continuous (coordinateDensity α β w c g) := by
  unfold coordinateDensity
  simp only [radius_coordinates]
  fun_prop

theorem coordinateDensity_flow (α β w c : ℝ) (hc : c ≠ 0) (g : ℝ → ℂ)
    (θ : ℝ) (x : Joint 2 4) :
    coordinateDensity α β w c g (flowEquiv c hc θ x) = coordinateDensity α β w c g x := by
  simp only [coordinateDensity,radius_flow,
    KFCausalNormalizedChargeFlow.flow_clock,KFCausalNormalizedChargeFlow.flow_neutral]

private theorem exponent_product (A B C D E z : ℂ) :
    (Complex.exp A*Complex.exp B)*(z*Complex.exp C*Complex.exp D*Complex.exp E) =
      z*Complex.exp (A+B+C+D+E) := by
  simp only [Complex.exp_add]
  ring

theorem paired_density (α β w : ℝ) (g : ℝ → ℂ) (x : Configuration) :
    product (α/w) (α/w) (WithLp.toLp 2 ![scale*(x.2 0-x.2 1),scale*(x.2 2-x.2 3)])*
      spectator (α*w) (α*w) β g
        (WithLp.toLp 2 ![x.1,scale*(x.2 0+x.2 1),scale*(x.2 2+x.2 3),x.2 4]) =
      configurationDensity α β w g x := by
  change
    (gaussian (α/w:ℝ) (scale*(x.2 0-x.2 1))*
      gaussian (α/w:ℝ) (scale*(x.2 2-x.2 3)))*
    (g x.1*gaussian (α*w:ℝ) (scale*(x.2 0+x.2 1))*
      gaussian (α*w:ℝ) (scale*(x.2 2+x.2 3))*
      gaussian (β:ℂ) (x.2 4)) = _
  simp only [gaussian]
  rw [exponent_product]
  unfold configurationDensity
  congr 1
  congr 1
  unfold quadratic
  push_cast
  have hs : (scale:ℂ)^2 = (1/2:ℂ) := by
    rw [← Complex.ofReal_pow,scale_square]
    norm_num
  ring_nf
  rw [hs]
  ring

theorem mixed_density (α β w c : ℝ) (hα : 0 < α) (hw : 0 < w)
    (hmatch : Real.pi^2/α = α*c^2) (g : ℝ → ℂ) (x : Joint 2 4) :
    (𝓕 (product (α/w) (α/w))) (split 2 4 x).1*
      spectator (α*w) (α*w) β g (split 2 4 x).2 =
      coordinateDensity α β w c g x := by
  rw [product_fourier _ _ (div_pos hα hw) (div_pos hα hw)]
  have hs : Real.sqrt (Real.pi/(α/w))*Real.sqrt (Real.pi/(α/w)) = Real.pi*w/α := by
    rw [Real.mul_self_sqrt (div_pos Real.pi_pos (div_pos hα hw)).le]
    field_simp
  have hf : Real.pi^2/(α/w) = α*w*c^2 := by
    calc
      _ = (Real.pi^2/α)*w := by field_simp
      _ = _ := by rw [hmatch]; ring
  rw [hs,hf]
  change (Real.pi*w/α:ℝ)*
    (gaussian (α*w*c^2:ℝ) (x (.inl 0))*
      gaussian (α*w*c^2:ℝ) (x (.inl 1)))*
    (g (x (.inr 0))*gaussian (α*w:ℝ) (x (.inr 1))*
      gaussian (α*w:ℝ) (x (.inr 2))*
      gaussian (β:ℂ) (x (.inr 3))) = _
  simp only [gaussian]
  rw [mul_assoc,exponent_product]
  simp only [coordinateDensity,radius_coordinates,mul_assoc]
  congr 2
  congr 1
  push_cast
  ring

variable (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 0 < w)
  (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)

def state : Hilbert :=
  pairedState ((product_memLp (α/w) (α/w) (div_pos hα hw) (div_pos hα hw)).toLp
    (product (α/w) (α/w)))
    ((spectator_memLp (α*w) (α*w) β (mul_pos hα hw) (mul_pos hα hw) hβ g hc hg).toLp
      (spectator (α*w) (α*w) β g))

theorem state_configuration_coe :
    state α β w hα hβ hw g hc hg =ᵐ[volume] configurationDensity α β w g := by
  have hp := pairedState_position_coe (product (α/w) (α/w)) (spectator (α*w) (α*w) β g)
    (product_memLp (α/w) (α/w) (div_pos hα hw) (div_pos hα hw))
    (spectator_memLp (α*w) (α*w) β (mul_pos hα hw) (mul_pos hα hw) hβ g hc hg)
  have he : (fun x : Space => (state α β w hα hβ hw g hc hg)
      (KFCausalEuclideanConfiguration.split x)) =ᵐ[volume]
      fun x => configurationDensity α β w g (KFCausalEuclideanConfiguration.split x) := by
    filter_upwards [euclideanPullback_coe (state α β w hα hβ hw g hc hg),hp] with x hx hp
    exact hx.symm.trans (hp.trans (paired_density α β w g (KFCausalEuclideanConfiguration.split x)))
  have ht := KFCausalEuclideanConfiguration.split_preserves_volume.symm.quasiMeasurePreserving.ae he
  filter_upwards [ht] with x hx
  simpa only [MeasurableEquiv.apply_symm_apply] using hx

theorem state_coordinates_coe (c : ℝ) (hmatch : Real.pi^2/α = α*c^2) :
    chargeCoordinates (state α β w hα hβ hw g hc hg) =ᵐ[volume] coordinateDensity α β w c g := by
  have hm := mixedCoordinates_functions_coe (product (α/w) (α/w)) (spectator (α*w) (α*w) β g)
    (product_integrable (α/w) (α/w) (div_pos hα hw) (div_pos hα hw))
    (product_memLp (α/w) (α/w) (div_pos hα hw) (div_pos hα hw))
    (spectator_memLp (α*w) (α*w) β (mul_pos hα hw) (mul_pos hα hw) hβ g hc hg)
  filter_upwards [coordinates_coe 2 4 (mixedCoordinates (state α β w hα hβ hw g hc hg)),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae hm] with x hx hm
  exact (hx.trans hm).trans (mixed_density α β w c hα hw hmatch g x)

theorem state_ne_zero (hg0 : g 0 ≠ 0) :
    state α β w hα hβ hw g hc hg ≠ 0 := by
  intro hz
  have he : configurationDensity α β w g =ᵐ[volume] (fun _ => (0:ℂ)) := by
    filter_upwards [state_configuration_coe α β w hα hβ hw g hc hg,
      Lp.coeFn_zero ℂ 2 (volume : Measure Configuration)] with x hx h0
    rw [hz] at hx
    exact hx.symm.trans h0
  have hcont : Continuous (configurationDensity α β w g) := by
    unfold configurationDensity quadratic
    fun_prop
  have heq := Measure.eq_of_ae_eq he hcont continuous_const
  apply hg0
  simpa [configurationDensity,quadratic,chargedRadius,pairPolynomial] using congrFun heq (0,0)

#print axioms coordinateDensity_continuous
#print axioms coordinateDensity_flow
#print axioms paired_density
#print axioms mixed_density
#print axioms state_configuration_coe
#print axioms state_coordinates_coe
#print axioms state_ne_zero
end
end UnifiedTheory.Audit.KFCausalPairedGaussianStates
