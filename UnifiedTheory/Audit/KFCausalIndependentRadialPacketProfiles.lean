/- Physical profiles with two independent charge-radial widths. The
sqrt(wL/wR) physical prefactor exactly cancels the Fourier determinant.
These definitions leave the neutral Gaussian and physical operators fixed. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianStates
import UnifiedTheory.Audit.KFCausalNeutralLinePackets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalIndependentRadialPacketProfiles
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalEuclideanProductCoordinates (Block Joint split)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalPairedModeCoordinates (scale scale_square)
open KFCausalReciprocalGaussianFourier (product product_fourier)
open KFCausalGaussianSliceDomain (gaussian gaussian_continuous gaussian_memLp_iff)
open KFCausalNeutralLinePackets (packet packet_memLp)
open KFCausalChargeGaussianGeometry (radius radius_flow)
open KFCausalChargeZeroSwapWitness (imbalance imbalance_flow)
open KFCausalNormalizedChargeFlow (flowEquiv)

def prefactor (wL wR : ℝ) : ℝ := Real.sqrt (wL/wR)
def chargedQuadratic (wL wR : ℝ) (q : Transverse) : ℝ :=
  wL*(scale*(q 0-q 1))^2+(scale*(q 2-q 3))^2/wR+
    (scale*(q 0+q 1))^2/wL+wR*(scale*(q 2+q 3))^2

def chargeQuadratic (wL wR c : ℝ) (x : Joint 2 4) : ℝ :=
  ((1/wL+wR)/2)*radius c x+((1/wL-wR)/2)*imbalance c x

def spectator (α β wL wR : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (v : Block 4) : ℂ :=
  g (v 0)*gaussian (α/wL:ℝ) (v 1)*gaussian (α*wR:ℝ) (v 2)*packet β b P (v 3)

def pairedProfile (α β wL wR : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (x : Block 2 × Block 4) : ℂ :=
  (prefactor wL wR:ℂ)*product (α*wL) (α/wR) x.1*spectator α β wL wR b P g x.2

def configurationProfile (α β wL wR : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (x : Configuration) : ℂ :=
  (prefactor wL wR:ℂ)*g x.1*Complex.exp (-(α:ℂ)*(chargedQuadratic wL wR x.2:ℂ))*packet β b P (x.2 4)

def chargeProfile (α β wL wR c : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (x : Joint 2 4) : ℂ :=
  (Real.pi/α:ℝ)*g (x (.inr 0))*Complex.exp (-(α:ℂ)*(chargeQuadratic wL wR c x:ℂ))*
    packet β b P (x (.inr 3))

theorem chargeQuadratic_coordinates (wL wR c : ℝ) (x : Joint 2 4) :
    chargeQuadratic wL wR c x =
      (1/wL)*(c^2*(x (.inl 0))^2+(x (.inr 1))^2)+
        wR*(c^2*(x (.inl 1))^2+(x (.inr 2))^2) := by
  unfold chargeQuadratic imbalance KFCausalChargeZeroSwapWitness.imbalanceRaw KFCausalNormalizedChargeFlow.dilate
  rw [KFCausalChargeGaussianGeometry.radius_coordinates]
  dsimp
  ring

theorem chargedQuadratic_diagonal (w : ℝ) (q : Transverse) :
    chargedQuadratic w w q=KFCausalReciprocalGaussianStates.quadratic w q := by
  unfold chargedQuadratic KFCausalReciprocalGaussianStates.quadratic
    KFCausalQuarticChargeProfiles.chargedRadius KFCausalChargedPairCoordinates.pairPolynomial
  ring_nf
  rw [scale_square]
  ring

theorem prefactor_diagonal (w : ℝ) (hw : 0 < w) : prefactor w w=1 := by
  simp [prefactor,div_self hw.ne']

theorem fourier_normalization (α wL wR : ℝ) (hα : 0 < α) (hL : 0 < wL) (hR : 0 < wR) :
    prefactor wL wR*(Real.sqrt (Real.pi/(α*wL))*Real.sqrt (Real.pi/(α/wR)))=Real.pi/α := by
  unfold prefactor
  rw [← mul_assoc,← Real.sqrt_mul (div_pos hL hR).le,
    ← Real.sqrt_mul (mul_nonneg (div_pos hL hR).le (div_pos Real.pi_pos (mul_pos hα hL)).le)]
  have he : (wL/wR)*(Real.pi/(α*wL))*(Real.pi/(α/wR))=(Real.pi/α)^2 := by
    field_simp
  rw [he,Real.sqrt_sq (div_pos Real.pi_pos hα).le]

theorem spectator_memLp (α β wL wR : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hL : 0 < wL) (hR : 0 < wR) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (hc : Continuous g) (hg : MemLp g 2 volume) : MemLp (spectator α β wL wR b P g) 2 volume := by
  let f : Fin 4 → ℝ → ℂ := ![g,gaussian (α/wL:ℝ),gaussian (α*wR:ℝ),packet β b P]
  have hf : ∀ i, Continuous (f i) := by
    intro i
    fin_cases i
    · exact hc
    · exact gaussian_continuous _
    · exact gaussian_continuous _
    · change Continuous (packet β b P)
      unfold packet KFCausalNeutralLinePackets.entire
      fun_prop
  have hm : ∀ i, MemLp (f i) 2 volume := by
    intro i
    fin_cases i
    · exact hg
    · exact (gaussian_memLp_iff _).mpr (div_pos hα hL)
    · exact (gaussian_memLp_iff _).mpr (mul_pos hα hR)
    · exact packet_memLp β hβ b P
  convert KFCausalChargeGaussianProducts.block_product_memLp 4 f hf hm using 1
  ext v
  simp [spectator,f,Fin.prod_univ_succ,mul_assoc]

theorem paired_configuration (α β wL wR : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (x : Configuration) :
    pairedProfile α β wL wR b P g
      (WithLp.toLp 2 ![scale*(x.2 0-x.2 1),scale*(x.2 2-x.2 3)],
       WithLp.toLp 2 ![x.1,scale*(x.2 0+x.2 1),scale*(x.2 2+x.2 3),x.2 4]) =
      configurationProfile α β wL wR b P g x := by
  simp only [pairedProfile,product,spectator,gaussian,configurationProfile,chargedQuadratic]
  push_cast
  have he : -(α:ℂ)*((wL:ℂ)*((scale:ℂ)*((x.2 0:ℂ)-(x.2 1:ℂ)))^2+
      ((scale:ℂ)*((x.2 2:ℂ)-(x.2 3:ℂ)))^2/(wR:ℂ)+
      ((scale:ℂ)*((x.2 0:ℂ)+(x.2 1:ℂ)))^2/(wL:ℂ)+
      (wR:ℂ)*((scale:ℂ)*((x.2 2:ℂ)+(x.2 3:ℂ)))^2) =
    -((α:ℂ)*(wL:ℂ))*((scale:ℂ)*((x.2 0:ℂ)-(x.2 1:ℂ)))^2+
    -((α:ℂ)/(wR:ℂ))*((scale:ℂ)*((x.2 2:ℂ)-(x.2 3:ℂ)))^2+
    -((α:ℂ)/(wL:ℂ))*((scale:ℂ)*((x.2 0:ℂ)+(x.2 1:ℂ)))^2+
    -((α:ℂ)*(wR:ℂ))*((scale:ℂ)*((x.2 2:ℂ)+(x.2 3:ℂ)))^2 := by ring
  rw [he]
  simp only [Complex.exp_add]
  ring

theorem fourier_profile (α β wL wR c : ℝ) (hα : 0 < α) (hL : 0 < wL) (hR : 0 < wR)
    (hmatch : Real.pi^2/α=α*c^2) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (x : Joint 2 4) :
    (prefactor wL wR:ℂ)*(𝓕 (product (α*wL) (α/wR))) (split 2 4 x).1*
      spectator α β wL wR b P g (split 2 4 x).2=chargeProfile α β wL wR c b P g x := by
  rw [product_fourier _ _ (mul_pos hα hL) (div_pos hα hR)]
  have h1 : Real.pi^2/(α*wL)=(α/wL)*c^2 := by rw [← div_div,hmatch]; ring
  have h2 : Real.pi^2/(α/wR)=(α*wR)*c^2 := by
    calc
      _ = (Real.pi^2/α)*wR := by field_simp
      _ = _ := by rw [hmatch]; ring
  rw [h1,h2]
  have hn : (prefactor wL wR:ℂ)*
      ((Real.sqrt (Real.pi/(α*wL))*Real.sqrt (Real.pi/(α/wR)):ℝ):ℂ)=(Real.pi/α:ℝ) := by
    exact_mod_cast fourier_normalization α wL wR hα hL hR
  rw [← mul_assoc,hn]
  simp only [product,spectator,gaussian,chargeProfile,chargeQuadratic_coordinates]
  push_cast
  rw [show -(α:ℂ)*((1/(wL:ℂ))*((c:ℂ)^2*(x (.inl 0):ℂ)^2+(x (.inr 1):ℂ)^2)+
      (wR:ℂ)*((c:ℂ)^2*(x (.inl 1):ℂ)^2+(x (.inr 2):ℂ)^2)) =
    -(((α:ℂ)/(wL:ℂ))*(c:ℂ)^2)*(x (.inl 0):ℂ)^2+
    -(((α:ℂ)*(wR:ℂ))*(c:ℂ)^2)*(x (.inl 1):ℂ)^2+
    -((α:ℂ)/(wL:ℂ))*(x (.inr 1):ℂ)^2+
    -((α:ℂ)*(wR:ℂ))*(x (.inr 2):ℂ)^2 by ring]
  simp only [Complex.exp_add,KFCausalEuclideanProductCoordinates.split_fst,
    KFCausalEuclideanProductCoordinates.split_snd]
  ring

theorem chargeProfile_flow (α β wL wR c : ℝ) (hc : c ≠ 0) (b : ℂ) (P : Polynomial ℂ)
    (g : ℝ → ℂ) (θ : ℝ) (x : Joint 2 4) :
    chargeProfile α β wL wR c b P g (flowEquiv c hc θ x)=chargeProfile α β wL wR c b P g x := by
  simp only [chargeProfile,chargeQuadratic,radius_flow,imbalance_flow,
    KFCausalNormalizedChargeFlow.flow_clock,KFCausalNormalizedChargeFlow.flow_neutral]

#print axioms chargeQuadratic_coordinates
#print axioms chargedQuadratic_diagonal
#print axioms prefactor_diagonal
#print axioms fourier_normalization
#print axioms spectator_memLp
#print axioms paired_configuration
#print axioms fourier_profile
#print axioms chargeProfile_flow
end
end UnifiedTheory.Audit.KFCausalIndependentRadialPacketProfiles
