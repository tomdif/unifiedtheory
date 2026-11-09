/- Gaussian L2 envelopes for the charged quotient and its derivative in
actual narrow Fourier coordinates. Constants may depend on degree and the
fixed family; this is not an energy-relative estimate uniform over states. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierPackets
import UnifiedTheory.Audit.KFCausalClusteredWidthChargedJet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNarrowFourierChargedBounds
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalNarrowFourierPackets (chargedRadius spectator)
open KFCausalNeutralLinePackets (packet)
open KFCausalClusteredWidthProfiles (quotient)
open KFCausalClusteredWidthChargedJet (jet limitJet)

def powerConstant (n : ℕ) : ℝ := 2^n*(n.factorial:ℝ)

theorem powerConstant_positive (n : ℕ) : 0 < powerConstant n := by unfold powerConstant; positivity

theorem power_exp_bound (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    t^n*Real.exp (-t) ≤ powerConstant n*Real.exp (-t/2) := by
  have hn : 0 < (n.factorial:ℝ) := by positivity
  have he := (div_le_iff₀ hn).mp (Real.pow_div_factorial_le_exp (t/2) (by positivity : 0 ≤ t/2) n)
  have hp : t^n ≤ powerConstant n*Real.exp (t/2) := by
    calc
      t^n = 2^n*(t/2)^n := by rw [← mul_pow]; congr 1; ring
      _ ≤ 2^n*(Real.exp (t/2)*(n.factorial:ℝ)) := mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by unfold powerConstant; ring
  have hb := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-t)).le
  have hh : Real.exp (t/2)*Real.exp (-t) = Real.exp (-t/2) := by rw [← Real.exp_add]; congr 1; ring
  simpa only [mul_assoc,hh] using hb

def base (α β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (z : Block 2 × Block 4) : ℂ :=
  g (z.2 0)*Complex.exp (-(chargedRadius α z:ℂ)/2)*packet β b P (z.2 3)

def moment (n : ℕ) (α β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (z : Block 2 × Block 4) : ℂ :=
  g (z.2 0)*((chargedRadius α z:ℂ)^n*Complex.exp (-(chargedRadius α z:ℂ)))*packet β b P (z.2 3)

def charged (n : ℕ) (δ α β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (z : Block 2 × Block 4) : ℂ :=
  g (z.2 0)*(Complex.exp (-(chargedRadius α z:ℂ))*quotient δ (chargedRadius α z:ℂ)^n)*packet β b P (z.2 3)

def slope (n : ℕ) (δ α β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (z : Block 2 × Block 4) : ℂ :=
  g (z.2 0)*jet n δ (chargedRadius α z:ℂ)*packet β b P (z.2 3)

def limitSlope (n : ℕ) (α β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (z : Block 2 × Block 4) : ℂ :=
  g (z.2 0)*limitJet n (chargedRadius α z:ℂ)*packet β b P (z.2 3)

theorem base_product (α β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (z : Block 2 × Block 4) :
    base α β b P g z =
      KFCausalReciprocalGaussianFourier.product (Real.pi^2/(2*α)) (Real.pi^2/(2*α)) z.1*
        spectator (α/2) β b P g z.2 := by
  unfold base KFCausalReciprocalGaussianFourier.product spectator KFCausalGaussianSliceDomain.gaussian
  have he (A B C D s t : ℂ) :
      (Complex.exp A*Complex.exp B)*(s*Complex.exp C*Complex.exp D*t) =
        s*Complex.exp (A+B+C+D)*t := by simp only [Complex.exp_add]; ring
  rw [he]
  congr 2
  congr 1
  unfold chargedRadius
  push_cast
  ring

theorem base_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) :
    MemLp (base α β b P g) 2 volume := by
  have hm := KFCausalL2TensorEmbedding.product_memLp volume volume _ _
    (KFCausalReciprocalGaussianFourier.product_memLp (Real.pi^2/(2*α)) (Real.pi^2/(2*α))
      (by positivity) (by positivity))
    (KFCausalNarrowFourierPackets.spectator_memLp (α/2) β (by positivity) hβ b P g hc hg)
  exact hm.ae_eq (Filter.Eventually.of_forall (fun z => (base_product α β b P g z).symm))

theorem moment_bound (n : ℕ) (α β : ℝ) (hα : 0 < α)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (z : Block 2 × Block 4) :
    ‖moment n α β b P g z‖ ≤ powerConstant n*‖base α β b P g z‖ := by
  have hz := KFCausalNarrowFourierPackets.chargedRadius_nonnegative α hα z
  have he := power_exp_bound n (chargedRadius α z) hz
  simp only [moment,base,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz,
    Complex.norm_exp,Complex.neg_re,Complex.ofReal_re,Complex.div_ofNat_re]
  nlinarith [mul_le_mul_of_nonneg_left he (norm_nonneg (g (z.2 0))),
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (norm_nonneg (g (z.2 0))))
      (norm_nonneg (packet β b P (z.2 3)))]

theorem moment_memLp (n : ℕ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) :
    MemLp (moment n α β b P g) 2 volume := by
  have hcont : Continuous (moment n α β b P g) := by
    unfold moment chargedRadius packet KFCausalNeutralLinePackets.entire
    fun_prop
  apply ((base_memLp α β hα hβ b P g hc hg).const_mul (powerConstant n:ℂ)).of_le hcont.aestronglyMeasurable
  filter_upwards [] with z
  simpa only [Pi.mul_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (powerConstant_positive n)] using moment_bound n α β hα b P g z

theorem charged_bound (n : ℕ) (δ α β : ℝ) (hδ : 0 < δ) (hα : 0 < α)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (z : Block 2 × Block 4) :
    ‖charged n δ α β b P g z‖ ≤ ‖moment n α β b P g z‖ := by
  have hz : 0 ≤ (chargedRadius α z:ℂ).re := KFCausalNarrowFourierPackets.chargedRadius_nonnegative α hα z
  have hq := pow_le_pow_left₀ (norm_nonneg _) (KFCausalClusteredWidthProfiles.quotient_norm_le δ _ hδ hz) n
  simp only [charged,moment,norm_mul,norm_pow]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hq (norm_nonneg (Complex.exp (-(chargedRadius α z:ℂ))))

theorem slope_bound (n : ℕ) (δ α β : ℝ) (hδ : 0 < δ) (hα : 0 < α)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (z : Block 2 × Block 4) :
    ‖slope n δ α β b P g z‖ ≤ (n:ℝ)*‖moment (n-1) α β b P g z‖+‖moment n α β b P g z‖ := by
  have hz : 0 ≤ (chargedRadius α z:ℂ).re := KFCausalNarrowFourierPackets.chargedRadius_nonnegative α hα z
  have hj := KFCausalClusteredWidthChargedJet.jet_norm_le n δ hδ (chargedRadius α z:ℂ) hz
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj (norm_nonneg (g (z.2 0))))
    (norm_nonneg (packet β b P (z.2 3)))
  simp only [slope,moment,norm_mul,norm_pow,Complex.norm_exp,Complex.neg_re]
  convert hb using 1
  ring

theorem charged_tendsto (n : ℕ) (α β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (z : Block 2 × Block 4) :
    Tendsto (fun δ => charged n δ α β b P g z) (𝓝[>] 0) (𝓝 (moment n α β b P g z)) := by
  have ht := (((KFCausalClusteredWidthProfiles.quotient_tendsto (chargedRadius α z:ℂ)).pow n).const_mul
    (Complex.exp (-(chargedRadius α z:ℂ)))).const_mul (g (z.2 0)) |>.mul_const (packet β b P (z.2 3))
  simpa only [charged,moment,mul_comm] using ht

theorem slope_tendsto (n : ℕ) (α β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (z : Block 2 × Block 4) :
    Tendsto (fun δ => slope n δ α β b P g z) (𝓝[>] 0) (𝓝 (limitSlope n α β b P g z)) :=
  ((KFCausalClusteredWidthChargedJet.jet_tendsto n (chargedRadius α z:ℂ)).const_mul (g (z.2 0))).mul_const
    (packet β b P (z.2 3))

#print axioms powerConstant_positive
#print axioms power_exp_bound
#print axioms base_product
#print axioms base_memLp
#print axioms moment_bound
#print axioms moment_memLp
#print axioms charged_bound
#print axioms slope_bound
#print axioms charged_tendsto
#print axioms slope_tendsto
end
end UnifiedTheory.Audit.KFCausalNarrowFourierChargedBounds
