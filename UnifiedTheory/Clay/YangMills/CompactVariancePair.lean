/- Exact two-output variance identity for positive continuous densities.
The unnormalized formula is a two-by-two moment determinant. -/
import UnifiedTheory.Clay.YangMills.CompactLikelihoodVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactVariancePair
noncomputable section
open MeasureTheory CompactDensityEntropy

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def pairMoment (p f : C(X, ℝ)) : ℝ :=
  ∫ v, ∫ w, p v*p w*(f v-f w)^2 ∂μ ∂μ

/-- Exact unnormalized second-moment determinant; positivity is not needed. -/
theorem pair_identity (p f : C(X, ℝ)) :
    pairMoment μ p f = 2*((∫ v, p v ∂μ)*(∫ v, p v*(f v)^2 ∂μ)-
      (∫ v, p v*f v ∂μ)^2) := by
  have hp := continuous_integrable μ _ p.continuous
  have hf := continuous_integrable μ _ (p.continuous.mul f.continuous)
  have hff := continuous_integrable μ _ (p.continuous.mul (f.continuous.pow 2))
  have hi (v : X) : (∫ w, p v*p w*(f v-f w)^2 ∂μ) =
      p v*(f v)^2*(∫ w, p w ∂μ) + p v*(∫ w, p w*(f w)^2 ∂μ) -
        2*(p v*f v)*(∫ w, p w*f w ∂μ) := by
    have he (w : X) : p v*p w*(f v-f w)^2 =
        (p v*(f v)^2)*p w + p v*(p w*(f w)^2) - (2*(p v*f v))*(p w*f w) := by ring
    simp_rw [he]
    have hs := integral_sub ((hp.const_mul (p v*(f v)^2)).add (hff.const_mul (p v)))
      (hf.const_mul (2*(p v*f v)))
    have ha := integral_add (hp.const_mul (p v*(f v)^2)) (hff.const_mul (p v))
    simp only [Pi.add_apply, Pi.mul_apply] at hs ha
    rw [hs, ha, integral_const_mul, integral_const_mul, integral_const_mul]
  unfold pairMoment
  simp_rw [hi]
  have hs := integral_sub ((hff.mul_const (∫ w, p w ∂μ)).add
    (hp.mul_const (∫ w, p w*(f w)^2 ∂μ)))
    ((hf.const_mul 2).mul_const (∫ w, p w*f w ∂μ))
  have ha := integral_add (hff.mul_const (∫ w, p w ∂μ))
    (hp.mul_const (∫ w, p w*(f w)^2 ∂μ))
  simp only [Pi.add_apply, Pi.mul_apply] at hs ha
  rw [hs, ha, integral_mul_const, integral_mul_const, integral_mul_const, integral_const_mul]
  ring

/-- The normalized formula does not require any comparison or independence assumption. -/
theorem normalized_pair (p f : C(X, ℝ)) (hp : (∫ v, p v ∂μ) = 1) :
    pairMoment μ p f / 2 = (∫ v, p v*(f v)^2 ∂μ)-(∫ v, p v*f v ∂μ)^2 := by
  rw [pair_identity, hp]
  ring

/-- The iterated pair integral is also its actual product-measure integral. -/
theorem pair_prod [SecondCountableTopology X] (p f : C(X, ℝ)) :
    pairMoment μ p f = ∫ z : X × X, p z.1*p z.2*(f z.1-f z.2)^2 ∂μ.prod μ := by
  symm
  exact integral_prod _ (continuous_integrable (μ.prod μ) _ (by fun_prop))

end
end UnifiedTheory.Clay.YangMills.CompactVariancePair
