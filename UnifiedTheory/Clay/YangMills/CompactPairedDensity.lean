/- Exact paired-density response and harmonic overlap. The coefficient
retains the actual normalized contrast rather than a likelihood cap. -/
import UnifiedTheory.Clay.YangMills.CompactDensityEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CompactPairedDensity
noncomputable section
open MeasureTheory CompactDensityEntropy

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem weighted_product_sq (w a b : X → ℝ) (hw : Continuous w) (ha : Continuous a)
    (hb : Continuous b) (hw0 : ∀ x, 0 ≤ w x) :
    (∫ x, w x * a x * b x ∂μ) ^ 2 ≤
      (∫ x, w x * (a x) ^ 2 ∂μ) * (∫ x, w x * (b x) ^ 2 ∂μ) := by
  have hh := integral_product_sq μ (fun x => Real.sqrt (w x) * a x)
    (fun x => Real.sqrt (w x) * b x) (hw.sqrt.mul ha) (hw.sqrt.mul hb)
  have he (x : X) : (Real.sqrt (w x) * a x) * (Real.sqrt (w x) * b x) =
      w x * a x * b x := by
    calc
      _ = (Real.sqrt (w x)) ^ 2 * a x * b x := by ring
      _ = _ := by rw [Real.sq_sqrt (hw0 x)]
  have hs (c : X → ℝ) (x : X) : (Real.sqrt (w x) * c x) ^ 2 = w x * (c x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hw0 x)]
  simpa only [he, hs] using hh

theorem contrast_pairing (p q f : X → ℝ) (hp : Continuous p) (hq : Continuous q)
    (hf : Continuous f) (hp0 : ∀ x, 0 < p x) (hq0 : ∀ x, 0 < q x)
    (hpair : (∫ x, q x * f x ∂μ) = -(∫ x, p x * f x ∂μ)) :
    (∫ x, ((p x+q x)/2) * ((p x-q x)/(p x+q x)) * f x ∂μ) =
      ∫ x, p x * f x ∂μ := by
  have he (x : X) : ((p x+q x)/2) * ((p x-q x)/(p x+q x)) * f x =
      (p x*f x-q x*f x)/2 := by
    field_simp [(add_pos (hp0 x) (hq0 x)).ne']
  simp_rw [he]
  rw [integral_div, integral_sub
    (continuous_integrable μ (fun x => p x*f x) (hp.mul hf))
    (continuous_integrable μ (fun x => q x*f x) (hq.mul hf)), hpair]
  ring

theorem mixture_even (p q F : X → ℝ) (hp : Continuous p) (hq : Continuous q)
    (hF : Continuous F) (he : (∫ x, q x * F x ∂μ) = ∫ x, p x * F x ∂μ) :
    (∫ x, ((p x+q x)/2) * F x ∂μ) = ∫ x, p x * F x ∂μ := by
  have hx (x : X) : ((p x+q x)/2)*F x = (p x*F x+q x*F x)/2 := by ring
  simp_rw [hx]
  rw [integral_div, integral_add
    (continuous_integrable μ (fun x => p x*F x) (hp.mul hF))
    (continuous_integrable μ (fun x => q x*F x) (hq.mul hF)), he]
  ring

theorem odd_response (p q f : X → ℝ) (hp : Continuous p) (hq : Continuous q)
    (hf : Continuous f) (hp0 : ∀ x, 0 < p x) (hq0 : ∀ x, 0 < q x)
    (hfirst : (∫ x, q x * f x ∂μ) = -(∫ x, p x * f x ∂μ))
    (hsecond : (∫ x, q x * (f x) ^ 2 ∂μ) = ∫ x, p x * (f x) ^ 2 ∂μ) :
    (∫ x, p x * f x ∂μ) ^ 2 ≤
      (∫ x, ((p x+q x)/2) * ((p x-q x)/(p x+q x)) ^ 2 ∂μ) *
        (∫ x, p x * (f x) ^ 2 ∂μ) := by
  have hh := weighted_product_sq μ (fun x => (p x+q x)/2)
    (fun x => (p x-q x)/(p x+q x)) f ((hp.add hq).div_const 2)
    ((hp.sub hq).div (hp.add hq) (fun x => (add_pos (hp0 x) (hq0 x)).ne')) hf
    (fun x => (div_pos (add_pos (hp0 x) (hq0 x)) (by norm_num)).le)
  rw [contrast_pairing μ p q f hp hq hf hp0 hq0 hfirst,
    mixture_even μ p q (fun x => (f x) ^ 2) hp hq (hf.pow 2) hsecond] at hh
  exact hh

theorem overlap_identity (p q : X → ℝ) (hp : Continuous p) (hq : Continuous q)
    (hp0 : ∀ x, 0 < p x) (hq0 : ∀ x, 0 < q x)
    (hpm : (∫ x, p x ∂μ) = 1) (hqm : (∫ x, q x ∂μ) = 1) :
    1 - (∫ x, ((p x+q x)/2) * ((p x-q x)/(p x+q x)) ^ 2 ∂μ) =
      ∫ x, 2*p x*q x/(p x+q x) ∂μ := by
  have hc := (hp.sub hq).div (hp.add hq) (fun x => (add_pos (hp0 x) (hq0 x)).ne')
  have ho : Continuous (fun x => 2*p x*q x/(p x+q x)) :=
    ((continuous_const.mul hp).mul hq).div (hp.add hq)
    (fun x => (add_pos (hp0 x) (hq0 x)).ne')
  have he (x : X) : ((p x+q x)/2) * ((p x-q x)/(p x+q x)) ^ 2 +
      2*p x*q x/(p x+q x) = (p x+q x)/2 := by
    field_simp [(add_pos (hp0 x) (hq0 x)).ne']
    ring
  have hh := integral_add
    (continuous_integrable μ (fun x => ((p x+q x)/2) * ((p x-q x)/(p x+q x)) ^ 2)
      (((hp.add hq).div_const 2).mul (hc.pow 2)))
    (continuous_integrable μ (fun x => 2*p x*q x/(p x+q x)) ho)
  simp only [he] at hh
  rw [integral_div, integral_add (continuous_integrable μ p hp)
    (continuous_integrable μ q hq), hpm, hqm] at hh
  linarith

end
end UnifiedTheory.Clay.YangMills.CompactPairedDensity
