/- Relative entropy controls actual bounded-observable response for positive
continuous probability densities. No mixing or spectral estimate is assumed. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsOscillation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactDensityEntropy
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

theorem scalar_hellinger_le (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (Real.sqrt p - Real.sqrt q)^2 ≤ p * Real.log (p / q) - p + q := by
  have hs := Real.log_le_sub_one_of_pos
    (div_pos (Real.sqrt_pos.mpr hq) (Real.sqrt_pos.mpr hp))
  rw [Real.log_div (Real.sqrt_pos.mpr hq).ne' (Real.sqrt_pos.mpr hp).ne',
    Real.log_sqrt hq.le, Real.log_sqrt hp.le] at hs
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*p by positivity)
  have he : (2*p) * (Real.sqrt q / Real.sqrt p - 1) =
      2 * Real.sqrt p * Real.sqrt q - 2*p := by
    have hx : p * (Real.sqrt q / Real.sqrt p) = Real.sqrt p * Real.sqrt q := by
      calc
        _ = (Real.sqrt p)^2 * (Real.sqrt q / Real.sqrt p) := by rw [Real.sq_sqrt hp.le]
        _ = _ := by field_simp
    rw [mul_sub, mul_one, mul_assoc, hx]
    ring
  rw [he] at hh
  rw [Real.log_div hp.ne' hq.ne']
  nlinarith [Real.sq_sqrt hp.le, Real.sq_sqrt hq.le]

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def entropy (p q : X → ℝ) : ℝ := ∫ x, p x * Real.log (p x / q x) ∂μ

theorem continuous_integrable (f : X → ℝ) (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem hellinger_le_entropy (p q : X → ℝ) (hp : Continuous p) (hq : Continuous q)
    (hp0 : ∀ x, 0 < p x) (hq0 : ∀ x, 0 < q x)
    (hpm : (∫ x, p x ∂μ) = 1) (hqm : (∫ x, q x ∂μ) = 1) :
    (∫ x, (Real.sqrt (p x) - Real.sqrt (q x))^2 ∂μ) ≤ entropy μ p q := by
  have hl : Continuous (fun x => p x * Real.log (p x / q x)) :=
    hp.mul ((hp.div hq (fun x => (hq0 x).ne')).log
      (fun x => (div_pos (hp0 x) (hq0 x)).ne'))
  have h := integral_mono (continuous_integrable μ _ ((hp.sqrt.sub hq.sqrt).pow 2))
    (continuous_integrable μ _ ((hl.sub hp).add hq))
    (fun x => scalar_hellinger_le (p x) (q x) (hp0 x) (hq0 x))
  have hadd := integral_add ((continuous_integrable μ _ hl).sub
    (continuous_integrable μ _ hp)) (continuous_integrable μ _ hq)
  have hsub := integral_sub (continuous_integrable μ _ hl) (continuous_integrable μ _ hp)
  simp only [Pi.add_apply, Pi.sub_apply] at h hadd hsub
  rw [hadd, hsub, hpm, hqm] at h
  simpa only [sub_add_cancel, entropy] using h

theorem entropy_nonneg (p q : X → ℝ) (hp : Continuous p) (hq : Continuous q)
    (hp0 : ∀ x, 0 < p x) (hq0 : ∀ x, 0 < q x)
    (hpm : (∫ x, p x ∂μ) = 1) (hqm : (∫ x, q x ∂μ) = 1) :
    0 ≤ entropy μ p q :=
  (integral_nonneg (fun x => sq_nonneg (Real.sqrt (p x)-Real.sqrt (q x)))).trans
    (hellinger_le_entropy μ p q hp hq hp0 hq0 hpm hqm)

theorem integral_product_sq (a b : X → ℝ) (ha : Continuous a) (hb : Continuous b) :
    (∫ x, a x * b x ∂μ)^2 ≤ (∫ x, (a x)^2 ∂μ) * (∫ x, (b x)^2 ∂μ) := by
  let A : C(X, ℝ) := ⟨a, ha⟩
  let B : C(X, ℝ) := ⟨b, hb⟩
  let u := ContinuousMap.toLp 2 μ ℝ A
  let v := ContinuousMap.toLp 2 μ ℝ B
  have hi : ⟪u, v⟫ = ∫ x, a x * b x ∂μ := by
    rw [ContinuousMap.inner_toLp]
    simp only [A, B, ContinuousMap.coe_mk, starRingEnd_apply, star_trivial, mul_comm]
  have hu : ‖u‖^2 = ∫ x, (a x)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, ContinuousMap.inner_toLp]
    simp only [A, ContinuousMap.coe_mk, starRingEnd_apply, star_trivial, pow_two]
  have hv : ‖v‖^2 = ∫ x, (b x)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, ContinuousMap.inner_toLp]
    simp only [B, ContinuousMap.coe_mk, starRingEnd_apply, star_trivial, pow_two]
  rw [← hi, ← hu, ← hv, ← mul_pow]
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (abs_real_inner_le_norm u v)

theorem response_sq_le_entropy (p q f : X → ℝ)
    (hp : Continuous p) (hq : Continuous q) (hf : Continuous f)
    (hp0 : ∀ x, 0 < p x) (hq0 : ∀ x, 0 < q x)
    (hpm : (∫ x, p x ∂μ) = 1) (hqm : (∫ x, q x ∂μ) = 1)
    (lo hi : ℝ) (hfb : ∀ x, f x ∈ Set.Icc lo hi) :
    ((∫ x, p x * f x ∂μ) - (∫ x, q x * f x ∂μ))^2 ≤
      (hi-lo)^2 * entropy μ p q := by
  let a := fun x => Real.sqrt (p x) - Real.sqrt (q x)
  let b := fun x => (f x - (hi+lo)/2) * (Real.sqrt (p x) + Real.sqrt (q x))
  have ha : Continuous a := hp.sqrt.sub hq.sqrt
  have hb : Continuous b := (hf.sub continuous_const).mul (hp.sqrt.add hq.sqrt)
  have he : (∫ x, a x * b x ∂μ) =
      (∫ x, p x * f x ∂μ) - (∫ x, q x * f x ∂μ) := by
    have hpw := continuous_integrable μ _ hp
    have hqw := continuous_integrable μ _ hq
    calc
      _ = ∫ x, (p x * f x - q x * f x) - ((hi+lo)/2) * (p x-q x) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [a, b]
        calc
          _ = (f x-(hi+lo)/2) * ((Real.sqrt (p x))^2-(Real.sqrt (q x))^2) := by ring
          _ = _ := by rw [Real.sq_sqrt (hp0 x).le, Real.sq_sqrt (hq0 x).le]; ring
      _ = _ := by
        have houter := integral_sub ((continuous_integrable μ _ (hp.mul hf)).sub
          (continuous_integrable μ _ (hq.mul hf))) ((hpw.sub hqw).const_mul ((hi+lo)/2))
        have hinner := integral_sub (continuous_integrable μ _ (hp.mul hf))
          (continuous_integrable μ _ (hq.mul hf))
        have hpq := integral_sub hpw hqw
        simp only [Pi.sub_apply, Pi.mul_apply] at houter hinner hpq
        rw [houter, hinner, integral_const_mul, hpq, hpm, hqm]
        ring
  have hb2 : (∫ x, (b x)^2 ∂μ) ≤ (hi-lo)^2 := by
    have hx (x : X) : (b x)^2 ≤ ((hi-lo)^2/2) * (p x + q x) := by
      have hf2 : (f x-(hi+lo)/2)^2 ≤ (hi-lo)^2/4 := by
        have hx := hfb x
        nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]
      have hs : (Real.sqrt (p x)+Real.sqrt (q x))^2 ≤ 2*(p x+q x) := by
        nlinarith [sq_nonneg (Real.sqrt (p x)-Real.sqrt (q x)),
          Real.sq_sqrt (hp0 x).le, Real.sq_sqrt (hq0 x).le]
      dsimp [b]
      rw [mul_pow]
      nlinarith [mul_le_mul hf2 hs (sq_nonneg _) (by positivity : 0 ≤ (hi-lo)^2/4)]
    have h := integral_mono (continuous_integrable μ _ (hb.pow 2))
      (continuous_integrable μ _ (continuous_const.mul (hp.add hq))) hx
    have hsum := integral_add (continuous_integrable μ _ hp) (continuous_integrable μ _ hq)
    simp only [Pi.add_apply, Pi.mul_apply] at h hsum
    rw [integral_const_mul, hsum, hpm, hqm] at h
    nlinarith
  have hc := integral_product_sq μ a b ha hb
  rw [he] at hc
  calc
    _ ≤ _ := hc
    _ ≤ (∫ x, (a x)^2 ∂μ) * (hi-lo)^2 :=
      mul_le_mul_of_nonneg_left hb2 (integral_nonneg (fun x => sq_nonneg _))
    _ ≤ entropy μ p q * (hi-lo)^2 := mul_le_mul_of_nonneg_right
      (hellinger_le_entropy μ p q hp hq hp0 hq0 hpm hqm) (sq_nonneg _)
    _ = _ := mul_comm _ _

end
end UnifiedTheory.Clay.YangMills.CompactDensityEntropy
