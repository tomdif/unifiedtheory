/- Every pointwise small-hbar limit of normalized-state characteristics
has a normalized positive classical difference kernel. Existence and
continuity of such a limit, and its dynamical identification, are separate. -/
import UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalCanonicalWeylLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation (Hilbert)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [Measure.IsAddHaarMeasure μ]

theorem gram_tendsto (h : ℕ → ℝ) (hz : Tendsto h atTop (𝓝 0))
    (f : ℕ → Hilbert μ) (hn : ∀ n, ‖f n‖ = 1)
    (χ : Frequency (X := X) → ℂ)
    (hc : ∀ z, Tendsto (fun n => characteristic μ (h n) (f n) z) atTop (𝓝 (χ z)))
    (z w : Frequency (X := X)) :
    Tendsto (fun n => inner ℂ (operator μ (h n) z (f n)) (operator μ (h n) w (f n)))
      atTop (𝓝 (χ (w-z))) := by
  have hb (n : ℕ) := gram_error μ (h n) (f n) z w
  simp only [hn,one_pow,mul_one] at hb
  have hbound : Tendsto (fun n => |h n| * |(w.1-z.1) z.2|) atTop (𝓝 0) := by
    simpa only [abs_zero,zero_mul] using hz.abs.mul_const |(w.1-z.1) z.2|
  have hd : Tendsto (fun n => inner ℂ (operator μ (h n) z (f n)) (operator μ (h n) w (f n))-
      characteristic μ (h n) (f n) (w-z)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) hb hbound)
  simpa only [sub_add_cancel,zero_add] using hd.add (hc (w-z))

theorem limit_zero (h : ℕ → ℝ) (f : ℕ → Hilbert μ) (hn : ∀ n, ‖f n‖ = 1)
    (χ : Frequency (X := X) → ℂ)
    (hc : ∀ z, Tendsto (fun n => characteristic μ (h n) (f n) z) atTop (𝓝 (χ z))) : χ 0 = 1 := by
  have he (n : ℕ) : characteristic μ (h n) (f n) 0 = 1 := by
    simp only [characteristic,operator_zero,inner_self_eq_norm_sq_to_K,hn]
    norm_num
  have ht := hc 0
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem limit_bound (h : ℕ → ℝ) (f : ℕ → Hilbert μ) (hn : ∀ n, ‖f n‖ = 1)
    (χ : Frequency (X := X) → ℂ)
    (hc : ∀ z, Tendsto (fun n => characteristic μ (h n) (f n) z) atTop (𝓝 (χ z)))
    (z : Frequency (X := X)) : ‖χ z‖ ≤ 1 := by
  apply le_of_tendsto' (hc z).norm
  intro n
  simpa only [hn,one_pow] using characteristic_bound μ (h n) (f n) z

theorem limit_conjugate (h : ℕ → ℝ) (hz : Tendsto h atTop (𝓝 0))
    (f : ℕ → Hilbert μ) (hn : ∀ n, ‖f n‖ = 1)
    (χ : Frequency (X := X) → ℂ)
    (hc : ∀ z, Tendsto (fun n => characteristic μ (h n) (f n) z) atTop (𝓝 (χ z)))
    (z : Frequency (X := X)) : χ (-z) = starRingEnd ℂ (χ z) := by
  have hg := gram_tendsto μ h hz f hn χ hc z 0
  simp only [operator_zero,zero_sub] at hg
  have ht := (Complex.continuous_conj.tendsto (χ z)).comp (hc z)
  simp only [characteristic,Function.comp_def,inner_conj_symm] at ht
  exact tendsto_nhds_unique hg ht

theorem gram_sum_identity (h : ℝ) (f : Hilbert μ) (N : ℕ)
    (z : Fin N → Frequency (X := X)) (c : Fin N → ℂ) :
    (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*
      inner ℂ (operator μ h (z i) f) (operator μ h (z j) f)) =
      (‖∑ i, c i • operator μ h (z i) f‖:ℂ)^2 := by
  calc
    _ = inner ℂ (∑ i, c i • operator μ h (z i) f) (∑ i, c i • operator μ h (z i) f) := by
      rw [sum_inner]
      simp only [inner_sum,inner_smul_left,inner_smul_right]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := inner_self_eq_norm_sq_to_K _

theorem limit_positive_kernel (h : ℕ → ℝ) (hz : Tendsto h atTop (𝓝 0))
    (f : ℕ → Hilbert μ) (hn : ∀ n, ‖f n‖ = 1)
    (χ : Frequency (X := X) → ℂ)
    (hc : ∀ z, Tendsto (fun n => characteristic μ (h n) (f n) z) atTop (𝓝 (χ z)))
    (N : ℕ) (z : Fin N → Frequency (X := X)) (c : Fin N → ℂ) :
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*χ (z j-z i)).re ∧
      (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*χ (z j-z i)).im = 0 := by
  have ht : Tendsto (fun n => ∑ i, ∑ j, starRingEnd ℂ (c i)*c j*
      inner ℂ (operator μ (h n) (z i) (f n)) (operator μ (h n) (z j) (f n)))
      atTop (𝓝 (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*χ (z j-z i))) :=
    tendsto_finset_sum _ (fun i _ => tendsto_finset_sum _ (fun j _ =>
      (gram_tendsto μ h hz f hn χ hc (z i) (z j)).const_mul _))
  constructor
  · apply ge_of_tendsto' (Complex.continuous_re.tendsto _ |>.comp ht)
    intro n
    simp only [Function.comp_def]
    rw [gram_sum_identity]
    simp only [← Complex.ofReal_pow,Complex.ofReal_re]
    positivity
  · have hi := (Complex.continuous_im.tendsto _).comp ht
    simp only [Function.comp_def,gram_sum_identity,← Complex.ofReal_pow,Complex.ofReal_im] at hi
    exact tendsto_nhds_unique hi tendsto_const_nhds

#print axioms gram_tendsto
#print axioms limit_zero
#print axioms limit_bound
#print axioms limit_conjugate
#print axioms gram_sum_identity
#print axioms limit_positive_kernel

end
end UnifiedTheory.Audit.KFCausalCanonicalWeylLimit
