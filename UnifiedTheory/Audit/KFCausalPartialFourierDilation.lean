/- Partial Fourier transformation under a positive dilation depending
on the spectator coordinates. Compact spectator support and ordinary
L1/L2 hypotheses supply the full joint integrability, so the formula
identifies the actual partial Fourier unitary on these coupled states. -/
import UnifiedTheory.Audit.KFCausalPartialFourierIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalPartialFourierDilation
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPartialFourier (leftFourier)
open UnifiedTheory.Audit.KFCausalPartialFourierSlices (leftIntegral)
open UnifiedTheory.Audit.KFCausalPartialFourierIntegral (leftFourier_toLp_coe)

variable (n m : ℕ)

theorem fourier_dilation (a : Block n → ℂ) (R : ℝ) (hR : 0 < R) (ξ : Block n) :
    (𝓕 (fun x : Block n => a (R • x))) ξ = ((R^n)⁻¹:ℝ) • (𝓕 a) (R⁻¹ • ξ) := by
  let A : Block n → ℂ := fun x => (Real.fourierChar (-inner ℝ x (R⁻¹ • ξ)):ℂ)*a x
  have he : ∀ x : Block n, inner ℝ (R • x) (R⁻¹ • ξ) = inner ℝ x ξ := by
    intro x
    rw [real_inner_smul_left,real_inner_smul_right]
    field_simp
  calc
    _ = ∫ x : Block n, A (R • x) := by
      rw [Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [A,he,Circle.smul_def,smul_eq_mul]
    _ = ((R^n)⁻¹:ℝ) • ∫ x : Block n, A x := by
      simpa only [finrank_euclideanSpace_fin] using
        Measure.integral_comp_smul_of_nonneg (volume : Measure (Block n)) A R (hR := hR.le)
    _ = _ := rfl

def scaledProduct (a : Block n → ℂ) (R : Block m → ℝ) (b : Block m → ℂ)
    (w : Block n × Block m) : ℂ := a (R w.2 • w.1)*b w.2

theorem scaledProduct_continuous (a : Block n → ℂ) (ha : Continuous a)
    (R : Block m → ℝ) (hR : Continuous R) (b : Block m → ℂ) (hb : Continuous b) :
    Continuous (scaledProduct n m a R b) := by
  unfold scaledProduct
  fun_prop

theorem leftIntegral_scaledProduct (a : Block n → ℂ) (R : Block m → ℝ)
    (hR : ∀ y, 0 < R y) (b : Block m → ℂ) (w : Block n × Block m) :
    leftIntegral n m (scaledProduct n m a R b) w =
      (((R w.2)^n)⁻¹:ℝ) • ((𝓕 a) ((R w.2)⁻¹ • w.1)*b w.2) := by
  have he : leftIntegral n m (scaledProduct n m a R b) w =
      (𝓕 (fun x : Block n => a (R w.2 • x))) w.1*b w.2 := by
    simp only [leftIntegral,scaledProduct,Real.fourier_eq,Circle.smul_def,smul_eq_mul]
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [he,fourier_dilation n a (R w.2) (hR w.2)]
  exact smul_mul_assoc _ _ _

theorem norm_power_integrable (k : ℕ) (hk : k ≠ 0)
    (a : Block n → ℂ) (ha : Continuous a) (hai : Integrable (fun x => ‖a x‖^k))
    (R : Block m → ℝ) (hR : Continuous R) (hpos : ∀ y, 0 < R y)
    (b : Block m → ℂ) (hb : Continuous b) (hbc : HasCompactSupport b) :
    Integrable (fun w : Block n × Block m => ‖scaledProduct n m a R b w‖^k) := by
  have hc := scaledProduct_continuous n m a ha R hR b hb
  rw [Measure.volume_eq_prod (Block n) (Block m)]
  apply (integrable_prod_iff' (hc.norm.pow k).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with y
    simpa only [scaledProduct,norm_mul,mul_pow] using
      (hai.comp_smul (hpos y).ne').mul_const (‖b y‖^k)
  · have hcont : Continuous (fun y : Block m => ((R y)^n)⁻¹*‖b y‖^k) :=
      ((hR.pow n).inv₀ (fun y => pow_ne_zero n (hpos y).ne')).mul (hb.norm.pow k)
    have hbpow : HasCompactSupport (fun y : Block m => ‖b y‖^k) :=
      hbc.comp_left (g := fun z : ℂ => ‖z‖^k) (by simp [hk])
    have hcompact : HasCompactSupport (fun y : Block m => ((R y)^n)⁻¹*‖b y‖^k) := hbpow.mul_left
    have hi := (hcont.integrable_of_hasCompactSupport (μ := volume) hcompact).const_mul (∫ x : Block n, ‖a x‖^k)
    convert hi using 1
    funext y
    simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) k),scaledProduct,norm_mul,mul_pow]
    rw [integral_mul_const]
    have he := Measure.integral_comp_smul_of_nonneg (volume : Measure (Block n))
      (fun x => ‖a x‖^k) (R y) (hR := (hpos y).le)
    simp only [finrank_euclideanSpace_fin,smul_eq_mul] at he
    rw [he]
    ring

theorem scaledProduct_integrable (a : Block n → ℂ) (ha : Continuous a) (hai : Integrable a)
    (R : Block m → ℝ) (hR : Continuous R) (hpos : ∀ y, 0 < R y)
    (b : Block m → ℂ) (hb : Continuous b) (hbc : HasCompactSupport b) :
    Integrable (scaledProduct n m a R b) := by
  apply (integrable_norm_iff (scaledProduct_continuous n m a ha R hR b hb).aestronglyMeasurable).mp
  simpa only [pow_one] using norm_power_integrable n m 1 (by decide) a ha
    (by simpa only [pow_one] using hai.norm) R hR hpos b hb hbc

theorem scaledProduct_memLp (a : Block n → ℂ) (ha : Continuous a) (ha2 : MemLp a 2)
    (R : Block m → ℝ) (hR : Continuous R) (hpos : ∀ y, 0 < R y)
    (b : Block m → ℂ) (hb : Continuous b) (hbc : HasCompactSupport b) :
    MemLp (scaledProduct n m a R b) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (scaledProduct_continuous n m a ha R hR b hb).aestronglyMeasurable).mpr
  exact norm_power_integrable n m 2 (by decide) a ha
    ((memLp_two_iff_integrable_sq_norm ha2.1).mp ha2) R hR hpos b hb hbc

theorem leftFourier_scaledProduct (a : Block n → ℂ) (ha : Continuous a)
    (ha1 : Integrable a) (ha2 : MemLp a 2)
    (R : Block m → ℝ) (hR : Continuous R) (hpos : ∀ y, 0 < R y)
    (b : Block m → ℂ) (hb : Continuous b) (hbc : HasCompactSupport b) :
    leftFourier n m ((scaledProduct_memLp n m a ha ha2 R hR hpos b hb hbc).toLp (scaledProduct n m a R b)) =ᵐ[volume]
      fun w => (((R w.2)^n)⁻¹:ℝ) • ((𝓕 a) ((R w.2)⁻¹ • w.1)*b w.2) := by
  filter_upwards [leftFourier_toLp_coe n m (scaledProduct n m a R b)
    (scaledProduct_continuous n m a ha R hR b hb)
    (scaledProduct_integrable n m a ha ha1 R hR hpos b hb hbc)
    (scaledProduct_memLp n m a ha ha2 R hR hpos b hb hbc)] with w hw
  exact hw.trans (leftIntegral_scaledProduct n m a R hpos b w)

#print axioms fourier_dilation
#print axioms scaledProduct_continuous
#print axioms leftIntegral_scaledProduct
#print axioms norm_power_integrable
#print axioms scaledProduct_integrable
#print axioms scaledProduct_memLp
#print axioms leftFourier_scaledProduct

end
end UnifiedTheory.Audit.KFCausalPartialFourierDilation
