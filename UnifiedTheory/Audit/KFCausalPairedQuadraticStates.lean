/- A tensor construction of the same paired quadratic physical packet.
Both the antisymmetric and symmetric quadratic factors have derived L2
membership, enabling the actual partial Fourier transform. -/
import UnifiedTheory.Audit.KFCausalPairedQuadraticFourier
import UnifiedTheory.Audit.KFCausalPhysicalGaussianCharge
import UnifiedTheory.Audit.KFCausalChargedPairCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalPairedQuadraticStates
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalEuclideanConfiguration (Space euclideanPullback euclideanPullback_coe)
open KFCausalChargeGaussianProducts (gaussian gaussian_memLp spectator spectator_memLp)
open KFCausalChargeGaussianIdentities (positionProfile configurationProfile paired_profile_identity)
open KFCausalPhysicalMixedCoordinates (pairedState pairedState_position_coe)
open KFCausalGaussianQuadraticFourier (moment moment_continuous moment_memLp)
open KFCausalPairedQuadraticFourier (difference difference_memLp difference_polynomial)
open KFCausalPairedModeCoordinates (scale scale_square)
open KFCausalChargedPairCoordinates (pairPolynomial)

def spectatorProduct (α β : ℝ) (g : ℝ → ℂ) (n m : ℕ) (v : Block 4) : ℂ :=
  g (v 0)*moment α n (v 1)*moment α m (v 2)*moment β 0 (v 3)

theorem spectatorProduct_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) (n m : ℕ) :
    MemLp (spectatorProduct α β g n m) 2 volume := by
  let f : Fin 4 → ℝ → ℂ := ![g,moment α n,moment α m,moment β 0]
  have hfc : ∀ i, Continuous (f i) := by
    intro i
    fin_cases i
    · exact hc
    all_goals exact moment_continuous _ _
  have hfm : ∀ i, MemLp (f i) 2 volume := by
    intro i
    fin_cases i
    · exact hg
    · exact moment_memLp α hα n
    · exact moment_memLp α hα m
    · exact moment_memLp β hβ 0
  change MemLp (fun v => spectatorProduct α β g n m v) 2 volume
  simpa only [f,spectatorProduct,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
    Matrix.cons_val_zero,Matrix.cons_val_succ,mul_assoc] using
    KFCausalChargeGaussianProducts.block_product_memLp 4 f hfc hfm

theorem spectatorProduct_zero (α β : ℝ) (g : ℝ → ℂ) (v : Block 4) :
    spectatorProduct α β g 0 0 v = spectator α β g v := by
  simp only [spectatorProduct,moment,pow_zero,one_mul,
    KFCausalGaussianSliceDomain.gaussian,spectator]
  rw [mul_assoc,mul_assoc,← Complex.exp_add,← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

def spectatorDifference (α β : ℝ) (g : ℝ → ℂ) (v : Block 4) : ℂ :=
  spectatorProduct α β g 2 0 v-spectatorProduct α β g 0 2 v

theorem spectatorDifference_polynomial (α β : ℝ) (g : ℝ → ℂ) (v : Block 4) :
    spectatorDifference α β g v =
      ((v 1:ℂ)^2-(v 2:ℂ)^2)*spectator α β g v := by
  rw [← spectatorProduct_zero]
  simp only [spectatorDifference,spectatorProduct,moment,pow_zero,one_mul]
  ring

theorem spectatorDifference_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) :
    MemLp (spectatorDifference α β g) 2 volume :=
  (spectatorProduct_memLp α β hα hβ g hc hg 2 0).sub
    (spectatorProduct_memLp α β hα hβ g hc hg 0 2)

variable (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
  (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)

def leftState : Hilbert :=
  pairedState ((gaussian_memLp 2 α hα).toLp (gaussian 2 α))
    ((spectatorDifference_memLp α β hα hβ g hc hg).toLp (spectatorDifference α β g))

def rightState : Hilbert :=
  pairedState ((difference_memLp α hα).toLp (difference α))
    ((spectator_memLp α β hα hβ g hc hg).toLp (spectator α β g))

def state : Hilbert := (1/2:ℂ) • (leftState α β hα hβ g hc hg-rightState α β hα hβ g hc hg)

def pairedConfigurationProfile (x : Configuration) : ℂ :=
  (pairPolynomial x.2:ℂ)*configurationProfile α β g x

def pairedPositionProfile (x : Space) : ℂ :=
  ((x 1:ℂ)*(x 2:ℂ)-(x 3:ℂ)*(x 4:ℂ))*positionProfile α β g x

theorem position_identity (x : Space) :
    (1/2:ℂ) *
      (gaussian 2 α (WithLp.toLp 2 ![scale*(x 1-x 2),scale*(x 3-x 4)]) *
        spectatorDifference α β g
          (WithLp.toLp 2 ![x 0,scale*(x 1+x 2),scale*(x 3+x 4),x 5]) -
      difference α (WithLp.toLp 2 ![scale*(x 1-x 2),scale*(x 3-x 4)]) *
        spectator α β g
          (WithLp.toLp 2 ![x 0,scale*(x 1+x 2),scale*(x 3+x 4),x 5])) =
      pairedPositionProfile α β g x := by
  rw [spectatorDifference_polynomial,difference_polynomial,pairedPositionProfile,
    ← paired_profile_identity]
  change (1/2:ℂ)*(gaussian 2 α _ *
      ((((scale*(x 1+x 2):ℝ):ℂ)^2-((scale*(x 3+x 4):ℝ):ℂ)^2)*spectator α β g _) -
    ((((scale*(x 1-x 2):ℝ):ℂ)^2-((scale*(x 3-x 4):ℝ):ℂ)^2)*gaussian 2 α _)*spectator α β g _) = _
  have hs : (scale:ℂ)^2 = (1/2:ℂ) := by
    rw [← Complex.ofReal_pow,scale_square]
    norm_num
  push_cast
  ring_nf
  rw [hs]
  ring

theorem state_position_coe :
    euclideanPullback (state α β hα hβ g hc hg) =ᵐ[volume] pairedPositionProfile α β g := by
  have hL := pairedState_position_coe (gaussian 2 α) (spectatorDifference α β g)
    (gaussian_memLp 2 α hα) (spectatorDifference_memLp α β hα hβ g hc hg)
  have hR := pairedState_position_coe (difference α) (spectator α β g)
    (difference_memLp α hα) (spectator_memLp α β hα hβ g hc hg)
  change euclideanPullback (leftState α β hα hβ g hc hg) =ᵐ[volume] _ at hL
  change euclideanPullback (rightState α β hα hβ g hc hg) =ᵐ[volume] _ at hR
  rw [state,map_smul,map_sub]
  filter_upwards [Lp.coeFn_smul (1/2:ℂ)
    (euclideanPullback (leftState α β hα hβ g hc hg)-
      euclideanPullback (rightState α β hα hβ g hc hg)),
    Lp.coeFn_sub (euclideanPullback (leftState α β hα hβ g hc hg))
      (euclideanPullback (rightState α β hα hβ g hc hg)),hL,hR] with x h0 h1 h2 h3
  rw [h0,Pi.smul_apply,smul_eq_mul,h1,Pi.sub_apply,h2,h3]
  exact position_identity α β g x

theorem configurationProfile_split (x : Space) :
    pairedConfigurationProfile α β g (KFCausalEuclideanConfiguration.split x) =
      pairedPositionProfile α β g x := by
  unfold pairedConfigurationProfile pairedPositionProfile
  rw [KFCausalChargeGaussianIdentities.configurationProfile_split]
  simp only [KFCausalEuclideanConfiguration.split_apply,pairPolynomial,
    Complex.ofReal_sub,Complex.ofReal_mul]
  rfl

theorem state_configuration_coe :
    state α β hα hβ g hc hg =ᵐ[volume] pairedConfigurationProfile α β g := by
  have ha : (fun x : Space =>
      (state α β hα hβ g hc hg) (KFCausalEuclideanConfiguration.split x)) =ᵐ[volume]
      fun x => pairedConfigurationProfile α β g (KFCausalEuclideanConfiguration.split x) := by
    filter_upwards [euclideanPullback_coe (state α β hα hβ g hc hg),
      state_position_coe α β hα hβ g hc hg] with x hx hp
    exact hx.symm.trans (hp.trans (configurationProfile_split α β g x).symm)
  have ht := KFCausalEuclideanConfiguration.split_preserves_volume.symm.quasiMeasurePreserving.ae ha
  filter_upwards [ht] with x hx
  simpa only [MeasurableEquiv.apply_symm_apply] using hx

#print axioms spectatorProduct_memLp
#print axioms spectatorProduct_zero
#print axioms spectatorDifference_polynomial
#print axioms spectatorDifference_memLp
#print axioms position_identity
#print axioms state_position_coe
#print axioms configurationProfile_split
#print axioms state_configuration_coe
end
end UnifiedTheory.Audit.KFCausalPairedQuadraticStates
