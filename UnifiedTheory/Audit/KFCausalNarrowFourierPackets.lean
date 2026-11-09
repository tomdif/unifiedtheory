/- Exact narrow-mode Fourier representatives of the actual reciprocal
packets, with arbitrary neutral exponential-polynomials and L2 clock profiles.
The width-dependent normalization is retained explicitly. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierCoordinates
import UnifiedTheory.Audit.KFCausalReciprocalNeutralSliceIntegrability
import UnifiedTheory.Audit.KFCausalNeutralLinePackets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNarrowFourierPackets
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalEuclideanConfiguration (Space euclideanPullback euclideanPullback_coe)
open KFCausalNarrowFourierCoordinates (pairedState pairedState_position_coe mixedCoordinates mixedCoordinates_functions_coe)
open KFCausalPairedModeCoordinates (scale scale_square)
open KFCausalReciprocalGaussianFourier (product product_memLp product_integrable product_fourier)
open KFCausalGaussianSliceDomain (gaussian gaussian_continuous gaussian_memLp_iff)
open KFCausalNeutralLinePackets (packet packet_memLp)
open KFCausalReciprocalGaussianStates (quadratic)

def spectator (a β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (v : Block 4) : ℂ :=
  g (v 0)*gaussian (a:ℂ) (v 1)*gaussian (a:ℂ) (v 2)*packet β b P (v 3)

theorem spectator_memLp (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) :
    MemLp (spectator a β b P g) 2 volume := by
  let f : Fin 4 → ℝ → ℂ := ![g,gaussian (a:ℂ),gaussian (a:ℂ),packet β b P]
  have hfc : ∀ i, Continuous (f i) := by
    intro i
    fin_cases i
    · exact hc
    · exact gaussian_continuous _
    · exact gaussian_continuous _
    · change Continuous (packet β b P)
      unfold packet KFCausalNeutralLinePackets.entire
      fun_prop
  have hfm : ∀ i, MemLp (f i) 2 volume := by
    intro i
    fin_cases i
    · exact hg
    · exact (gaussian_memLp_iff _).mpr ha
    · exact (gaussian_memLp_iff _).mpr ha
    · exact packet_memLp β hβ b P
  convert KFCausalChargeGaussianProducts.block_product_memLp 4 f hfc hfm using 1
  ext v
  simp only [spectator,f,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  change g (v 0)*gaussian (a:ℂ) (v 1)*gaussian (a:ℂ) (v 2)*packet β b P (v 3) =
    g (v 0)*(gaussian (a:ℂ) (v 1)*(gaussian (a:ℂ) (v 2)*packet β b P (v 3)))
  ring

def configurationDensity (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (x : Configuration) : ℂ :=
  g x.1*Complex.exp (-(α:ℂ)*(quadratic w x.2:ℂ))*packet β b P (x.2 4)

def chargedRadius (α : ℝ) (z : Block 2 × Block 4) : ℝ :=
  (Real.pi^2/α)*((z.1 0)^2+(z.1 1)^2)+α*((z.2 1)^2+(z.2 2)^2)

def coordinateDensity (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (z : Block 2 × Block 4) : ℂ :=
  ((Real.pi/α)*w:ℝ)*g (z.2 0)*Complex.exp (-(w:ℂ)*(chargedRadius α z:ℂ))*packet β b P (z.2 3)

theorem chargedRadius_nonnegative (α : ℝ) (hα : 0 < α) (z : Block 2 × Block 4) :
    0 ≤ chargedRadius α z := by unfold chargedRadius; positivity

theorem narrow_normalization (α w : ℝ) (hα : 0 < α) (hw : 0 < w) :
    Real.sqrt (Real.pi/(α/w))*Real.sqrt (Real.pi/(α/w)) = (Real.pi/α)*w := by
  rw [← pow_two,Real.sq_sqrt (div_pos Real.pi_pos (div_pos hα hw)).le]
  field_simp

theorem narrow_fourier (α w : ℝ) (hα : 0 < α) (hw : 0 < w) (u : Block 2) :
    (𝓕 (product (α/w) (α/w))) u =
      ((Real.pi/α)*w:ℝ)*product ((Real.pi^2/α)*w) ((Real.pi^2/α)*w) u := by
  rw [product_fourier _ _ (div_pos hα hw) (div_pos hα hw),narrow_normalization α w hα hw]
  have he : Real.pi^2/(α/w) = (Real.pi^2/α)*w := by field_simp
  rw [he]

private theorem exponent_product (A B C D z t : ℂ) :
    (Complex.exp A*Complex.exp B)*(z*Complex.exp C*Complex.exp D*t) =
      z*Complex.exp (A+B+C+D)*t := by
  simp only [Complex.exp_add]
  ring

theorem paired_density (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (x : Configuration) :
    product (α/w) (α/w) (WithLp.toLp 2 ![scale*(x.2 0+x.2 1),scale*(x.2 2-x.2 3)])*
      spectator (α*w) β b P g
        (WithLp.toLp 2 ![x.1,scale*(x.2 0-x.2 1),scale*(x.2 2+x.2 3),x.2 4]) =
      configurationDensity α β w b P g x := by
  change
    (gaussian (α/w:ℝ) (scale*(x.2 0+x.2 1))*gaussian (α/w:ℝ) (scale*(x.2 2-x.2 3)))*
    (g x.1*gaussian (α*w:ℝ) (scale*(x.2 0-x.2 1))*
      gaussian (α*w:ℝ) (scale*(x.2 2+x.2 3))*packet β b P (x.2 4)) = _
  simp only [gaussian]
  rw [exponent_product]
  unfold configurationDensity
  congr 2
  congr 1
  unfold quadratic KFCausalQuarticChargeProfiles.chargedRadius KFCausalChargedPairCoordinates.pairPolynomial
  push_cast
  have hs : (scale:ℂ)^2 = (1/2:ℂ) := by rw [← Complex.ofReal_pow,scale_square]; norm_num
  ring_nf
  rw [hs]
  ring

theorem mixed_density (α β w : ℝ) (hα : 0 < α) (hw : 0 < w)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (z : Block 2 × Block 4) :
    (𝓕 (product (α/w) (α/w))) z.1*spectator (α*w) β b P g z.2 =
      coordinateDensity α β w b P g z := by
  rw [narrow_fourier α w hα hw]
  unfold product spectator gaussian
  rw [mul_assoc,exponent_product]
  unfold coordinateDensity chargedRadius
  simp only [mul_assoc]
  congr 2
  congr 1
  push_cast
  ring

theorem factor_zero (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (q : KFCausalTransverseDilationFlow.Transverse) :
    KFCausalReciprocalNeutralSliceIntegrability.factor α β w 1 b P 0 q =
      Complex.exp (-(α:ℂ)*(quadratic w q:ℂ))*packet β b P (q 4) := by
  simp only [KFCausalReciprocalNeutralSliceIntegrability.factor,pow_zero,one_mul,
    KFCausalReciprocalGaussianCoordinates.exponent,one_pow,mul_one,sub_self,mul_zero,zero_mul,
    add_zero,KFCausalNeutralExponentialProfiles.exponentialProfile,
    KFCausalRelativeGaussianDifferential.position,ite_true,packet,KFCausalNeutralLinePackets.entire]
  simp only [sub_eq_add_neg,Complex.exp_add,neg_mul]
  ring

variable (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 0 < w)
  (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)

def state : Hilbert :=
  pairedState ((product_memLp (α/w) (α/w) (div_pos hα hw) (div_pos hα hw)).toLp
    (product (α/w) (α/w)))
    ((spectator_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg).toLp (spectator (α*w) β b P g))

theorem state_configuration_coe :
    state α β w hα hβ hw b P g hc hg =ᵐ[volume] configurationDensity α β w b P g := by
  have hp := pairedState_position_coe (product (α/w) (α/w)) (spectator (α*w) β b P g)
    (product_memLp (α/w) (α/w) (div_pos hα hw) (div_pos hα hw))
    (spectator_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg)
  have he : (fun x : Space => (state α β w hα hβ hw b P g hc hg)
      (KFCausalEuclideanConfiguration.split x)) =ᵐ[volume]
      fun x => configurationDensity α β w b P g (KFCausalEuclideanConfiguration.split x) := by
    filter_upwards [euclideanPullback_coe (state α β w hα hβ hw b P g hc hg),hp] with x hx hp
    exact hx.symm.trans (hp.trans (paired_density α β w b P g (KFCausalEuclideanConfiguration.split x)))
  have ht := KFCausalEuclideanConfiguration.split_preserves_volume.symm.quasiMeasurePreserving.ae he
  filter_upwards [ht] with x hx
  simpa only [MeasurableEquiv.apply_symm_apply] using hx

theorem state_coordinates_coe :
    mixedCoordinates (state α β w hα hβ hw b P g hc hg) =ᵐ[volume]
      coordinateDensity α β w b P g := by
  have hm := mixedCoordinates_functions_coe (product (α/w) (α/w)) (spectator (α*w) β b P g)
    (product_integrable (α/w) (α/w) (div_pos hα hw) (div_pos hα hw))
    (product_memLp (α/w) (α/w) (div_pos hα hw) (div_pos hα hw))
    (spectator_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg)
  filter_upwards [hm] with z hz
  exact hz.trans (mixed_density α β w hα hw b P g z)

#print axioms spectator_memLp
#print axioms chargedRadius_nonnegative
#print axioms narrow_normalization
#print axioms narrow_fourier
#print axioms paired_density
#print axioms mixed_density
#print axioms factor_zero
#print axioms state_configuration_coe
#print axioms state_coordinates_coe
end
end UnifiedTheory.Audit.KFCausalNarrowFourierPackets
