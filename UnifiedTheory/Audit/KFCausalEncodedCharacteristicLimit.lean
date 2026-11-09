/- Limits restricted to a linear frequency family retain normalization,
conjugation symmetry and a positive classical difference kernel. -/
import UnifiedTheory.Audit.KFCausalCanonicalWeylLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalEncodedCharacteristicLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation (Hilbert)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [Measure.IsAddHaarMeasure μ]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (L : V →L[ℝ] Frequency (X := X))

theorem gram_tendsto (h : ℕ → ℝ) (hz : Tendsto h atTop (𝓝 0))
    (f : ℕ → Hilbert μ) (hn : ∀ n, ‖f n‖ = 1)
    (χ : V → ℂ)
    (hc : ∀ z, Tendsto (fun n => characteristic μ (h n) (f n) (L z)) atTop (𝓝 (χ z)))
    (z w : V) :
    Tendsto (fun n => inner ℂ (operator μ (h n) (L z) (f n)) (operator μ (h n) (L w) (f n)))
      atTop (𝓝 (χ (w-z))) := by
  have hb (n : ℕ) := gram_error μ (h n) (f n) (L z) (L w)
  simp only [hn,one_pow,mul_one] at hb
  have hbound : Tendsto (fun n => |h n| * |((L w).1-(L z).1) (L z).2|) atTop (𝓝 0) := by
    simpa only [abs_zero,zero_mul] using hz.abs.mul_const |((L w).1-(L z).1) (L z).2|
  have hd : Tendsto (fun n => inner ℂ (operator μ (h n) (L z) (f n)) (operator μ (h n) (L w) (f n))-
      characteristic μ (h n) (f n) (L w-L z)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) hb hbound)
  have ht := hc (w-z)
  rw [map_sub] at ht
  simpa only [sub_add_cancel,zero_add] using hd.add ht

theorem limit_zero (h : ℕ → ℝ) (f : ℕ → Hilbert μ) (hn : ∀ n, ‖f n‖ = 1)
    (χ : V → ℂ)
    (hc : ∀ z, Tendsto (fun n => characteristic μ (h n) (f n) (L z)) atTop (𝓝 (χ z))) : χ 0 = 1 := by
  have he (n : ℕ) : characteristic μ (h n) (f n) (L 0) = 1 := by
    simp only [map_zero,characteristic,operator_zero,inner_self_eq_norm_sq_to_K,hn]
    norm_num
  have ht := hc 0
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem limit_bound (h : ℕ → ℝ) (f : ℕ → Hilbert μ) (hn : ∀ n, ‖f n‖ = 1)
    (χ : V → ℂ)
    (hc : ∀ z, Tendsto (fun n => characteristic μ (h n) (f n) (L z)) atTop (𝓝 (χ z)))
    (z : V) : ‖χ z‖ ≤ 1 := by
  apply le_of_tendsto' (hc z).norm
  intro n
  simpa only [hn,one_pow] using characteristic_bound μ (h n) (f n) (L z)

theorem limit_conjugate (h : ℕ → ℝ) (hz : Tendsto h atTop (𝓝 0))
    (f : ℕ → Hilbert μ) (hn : ∀ n, ‖f n‖ = 1)
    (χ : V → ℂ)
    (hc : ∀ z, Tendsto (fun n => characteristic μ (h n) (f n) (L z)) atTop (𝓝 (χ z)))
    (z : V) : χ (-z) = starRingEnd ℂ (χ z) := by
  have hg := gram_tendsto μ L h hz f hn χ hc z 0
  simp only [map_zero,operator_zero,zero_sub] at hg
  have ht := (Complex.continuous_conj.tendsto (χ z)).comp (hc z)
  simp only [characteristic,Function.comp_def,inner_conj_symm] at ht
  exact tendsto_nhds_unique hg ht

theorem limit_positive_kernel (h : ℕ → ℝ) (hz : Tendsto h atTop (𝓝 0))
    (f : ℕ → Hilbert μ) (hn : ∀ n, ‖f n‖ = 1)
    (χ : V → ℂ)
    (hc : ∀ z, Tendsto (fun n => characteristic μ (h n) (f n) (L z)) atTop (𝓝 (χ z)))
    (N : ℕ) (z : Fin N → V) (c : Fin N → ℂ) :
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*χ (z j-z i)).re ∧
      (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*χ (z j-z i)).im = 0 := by
  have ht : Tendsto (fun n => ∑ i, ∑ j, starRingEnd ℂ (c i)*c j*
      inner ℂ (operator μ (h n) (L (z i)) (f n)) (operator μ (h n) (L (z j)) (f n)))
      atTop (𝓝 (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*χ (z j-z i))) :=
    tendsto_finset_sum _ (fun i _ => tendsto_finset_sum _ (fun j _ =>
      (gram_tendsto μ L h hz f hn χ hc (z i) (z j)).const_mul _))
  constructor
  · apply ge_of_tendsto' (Complex.continuous_re.tendsto _ |>.comp ht)
    intro n
    simp only [Function.comp_def]
    rw [KFCausalCanonicalWeylLimit.gram_sum_identity]
    simp only [← Complex.ofReal_pow,Complex.ofReal_re]
    positivity
  · have hi := (Complex.continuous_im.tendsto _).comp ht
    simp only [Function.comp_def,KFCausalCanonicalWeylLimit.gram_sum_identity,
      ← Complex.ofReal_pow,Complex.ofReal_im] at hi
    exact tendsto_nhds_unique hi tendsto_const_nhds

#print axioms gram_tendsto
#print axioms limit_zero
#print axioms limit_bound
#print axioms limit_conjugate
#print axioms limit_positive_kernel

end
end UnifiedTheory.Audit.KFCausalEncodedCharacteristicLimit
