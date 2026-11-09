/- Actual Gaussian Hilbert states with reciprocal charged widths.
The partial Fourier representative is an invariant function of the two
standing-plane radii, so the entire positive-width family has zero charge.
No ordered-energy domain or response bound is asserted here. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianFourier
import UnifiedTheory.Audit.KFCausalPairedQuarticCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianStates
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
open KFCausalReciprocalGaussianFourier (product product_memLp product_integrable reciprocal_fourier)
open KFCausalGaussianSliceDomain (gaussian gaussian_continuous gaussian_memLp_iff)
open KFCausalChargeGaussianGeometry (radius radius_coordinates radius_flow)
open KFCausalChargeZeroSwapWitness (imbalance imbalanceRaw imbalance_flow)
open KFCausalNormalizedChargeFlow (flowEquiv dilate)
open KFCausalChargedPairCoordinates (pairPolynomial)
open KFCausalQuarticChargeProfiles (chargedRadius)

def quadratic (w : ℝ) (q : Transverse) : ℝ :=
  ((w+1/w)/2)*chargedRadius q+(1/w-w)*pairPolynomial q
def coordinateQuadratic (w c : ℝ) (x : Joint 2 4) : ℝ :=
  ((w+1/w)/2)*radius c x+((1/w-w)/2)*imbalance c x

theorem coordinateQuadratic_coordinates (w c : ℝ) (x : Joint 2 4) :
    coordinateQuadratic w c x =
      (1/w)*(c^2*(x (.inl 0))^2+(x (.inr 1))^2)+
        w*(c^2*(x (.inl 1))^2+(x (.inr 2))^2) := by
  unfold coordinateQuadratic imbalance imbalanceRaw dilate
  rw [radius_coordinates]
  dsimp
  ring

theorem coordinateQuadratic_flow (w c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Joint 2 4) :
    coordinateQuadratic w c (flowEquiv c hc θ x) = coordinateQuadratic w c x := by
  simp only [coordinateQuadratic,radius_flow,imbalance_flow]

def spectator (a b β : ℝ) (g : ℝ → ℂ) (v : Block 4) : ℂ :=
  g (v 0)*gaussian (a:ℂ) (v 1)*gaussian (b:ℂ) (v 2)*gaussian (β:ℂ) (v 3)

theorem spectator_memLp (a b β : ℝ) (ha : 0 < a) (hb : 0 < b) (hβ : 0 < β)
    (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) :
    MemLp (spectator a b β g) 2 volume := by
  let f : Fin 4 → ℝ → ℂ := ![g,gaussian (a:ℂ),gaussian (b:ℂ),gaussian (β:ℂ)]
  have hfc : ∀ i, Continuous (f i) := by
    intro i
    fin_cases i
    · exact hc
    all_goals exact gaussian_continuous _
  have hfm : ∀ i, MemLp (f i) 2 volume := by
    intro i
    fin_cases i
    · exact hg
    · exact (gaussian_memLp_iff _).mpr ha
    · exact (gaussian_memLp_iff _).mpr hb
    · exact (gaussian_memLp_iff _).mpr hβ
  convert KFCausalChargeGaussianProducts.block_product_memLp 4 f hfc hfm using 1
  ext v
  simp only [spectator,f,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  change g (v 0)*gaussian (a:ℂ) (v 1)*gaussian (b:ℂ) (v 2)*gaussian (β:ℂ) (v 3) =
    g (v 0)*(gaussian (a:ℂ) (v 1)*(gaussian (b:ℂ) (v 2)*gaussian (β:ℂ) (v 3)))
  ring

def configurationDensity (α β w : ℝ) (g : ℝ → ℂ) (x : Configuration) : ℂ :=
  g x.1*Complex.exp (-((α*quadratic w x.2+β*(x.2 4)^2:ℝ):ℂ))
def coordinateDensity (α β w c : ℝ) (g : ℝ → ℂ) (x : Joint 2 4) : ℂ :=
  (Real.pi/α:ℝ)*g (x (.inr 0))*
    Complex.exp (-((α*coordinateQuadratic w c x+β*(x (.inr 3))^2:ℝ):ℂ))

theorem coordinateDensity_continuous (α β w c : ℝ) (g : ℝ → ℂ) (hc : Continuous g) :
    Continuous (coordinateDensity α β w c g) := by
  unfold coordinateDensity
  simp only [coordinateQuadratic_coordinates]
  fun_prop

theorem coordinateDensity_flow (α β w c : ℝ) (hc : c ≠ 0) (g : ℝ → ℂ)
    (θ : ℝ) (x : Joint 2 4) :
    coordinateDensity α β w c g (flowEquiv c hc θ x) = coordinateDensity α β w c g x := by
  simp only [coordinateDensity,coordinateQuadratic_flow,
    KFCausalNormalizedChargeFlow.flow_clock,KFCausalNormalizedChargeFlow.flow_neutral]

private theorem exponent_product (A B C D E z : ℂ) :
    (Complex.exp A*Complex.exp B)*(z*Complex.exp C*Complex.exp D*Complex.exp E) =
      z*Complex.exp (A+B+C+D+E) := by
  simp only [Complex.exp_add]
  ring

theorem paired_density (α β w : ℝ) (g : ℝ → ℂ) (x : Configuration) :
    product (α*w) (α/w) (WithLp.toLp 2 ![scale*(x.2 0-x.2 1),scale*(x.2 2-x.2 3)])*
      spectator (α/w) (α*w) β g
        (WithLp.toLp 2 ![x.1,scale*(x.2 0+x.2 1),scale*(x.2 2+x.2 3),x.2 4]) =
      configurationDensity α β w g x := by
  change
    (gaussian (α*w:ℝ) (scale*(x.2 0-x.2 1))*
      gaussian (α/w:ℝ) (scale*(x.2 2-x.2 3)))*
    (g x.1*gaussian (α/w:ℝ) (scale*(x.2 0+x.2 1))*
      gaussian (α*w:ℝ) (scale*(x.2 2+x.2 3))*
      gaussian (β:ℂ) (x.2 4)) = _
  simp only [gaussian]
  rw [exponent_product]
  unfold configurationDensity
  congr 1
  congr 1
  unfold quadratic chargedRadius pairPolynomial
  push_cast
  have hs : (scale:ℂ)^2 = (1/2:ℂ) := by
    rw [← Complex.ofReal_pow,scale_square]
    norm_num
  ring_nf
  rw [hs]
  ring

theorem mixed_density (α β w c : ℝ) (hα : 0 < α) (hw : 0 < w)
    (hmatch : Real.pi^2/α = α*c^2) (g : ℝ → ℂ) (x : Joint 2 4) :
    (𝓕 (product (α*w) (α/w))) (split 2 4 x).1*
      spectator (α/w) (α*w) β g (split 2 4 x).2 =
      coordinateDensity α β w c g x := by
  rw [reciprocal_fourier α w c hα hw hmatch]
  change (Real.pi/α:ℝ)*
    (gaussian ((α/w)*c^2:ℝ) (x (.inl 0))*
      gaussian ((α*w)*c^2:ℝ) (x (.inl 1)))*
    (g (x (.inr 0))*gaussian (α/w:ℝ) (x (.inr 1))*
      gaussian (α*w:ℝ) (x (.inr 2))*
      gaussian (β:ℂ) (x (.inr 3))) = _
  simp only [gaussian]
  rw [mul_assoc,exponent_product]
  simp only [coordinateDensity,coordinateQuadratic_coordinates,mul_assoc]
  congr 2
  congr 1
  push_cast
  ring

variable (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 0 < w)
  (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)

def state : Hilbert :=
  pairedState ((product_memLp (α*w) (α/w) (mul_pos hα hw) (div_pos hα hw)).toLp
    (product (α*w) (α/w)))
    ((spectator_memLp (α/w) (α*w) β (div_pos hα hw) (mul_pos hα hw) hβ g hc hg).toLp
      (spectator (α/w) (α*w) β g))

theorem state_configuration_coe :
    state α β w hα hβ hw g hc hg =ᵐ[volume] configurationDensity α β w g := by
  have hp := pairedState_position_coe (product (α*w) (α/w)) (spectator (α/w) (α*w) β g)
    (product_memLp (α*w) (α/w) (mul_pos hα hw) (div_pos hα hw))
    (spectator_memLp (α/w) (α*w) β (div_pos hα hw) (mul_pos hα hw) hβ g hc hg)
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
  have hm := mixedCoordinates_functions_coe (product (α*w) (α/w)) (spectator (α/w) (α*w) β g)
    (product_integrable (α*w) (α/w) (mul_pos hα hw) (div_pos hα hw))
    (product_memLp (α*w) (α/w) (mul_pos hα hw) (div_pos hα hw))
    (spectator_memLp (α/w) (α*w) β (div_pos hα hw) (mul_pos hα hw) hβ g hc hg)
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
    unfold configurationDensity quadratic chargedRadius pairPolynomial
    fun_prop
  have heq := Measure.eq_of_ae_eq he hcont continuous_const
  apply hg0
  simpa [configurationDensity,quadratic,chargedRadius,pairPolynomial] using congrFun heq (0,0)

#print axioms coordinateQuadratic_coordinates
#print axioms coordinateQuadratic_flow
#print axioms spectator_memLp
#print axioms coordinateDensity_continuous
#print axioms coordinateDensity_flow
#print axioms paired_density
#print axioms mixed_density
#print axioms state_configuration_coe
#print axioms state_coordinates_coe
#print axioms state_ne_zero
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianStates
