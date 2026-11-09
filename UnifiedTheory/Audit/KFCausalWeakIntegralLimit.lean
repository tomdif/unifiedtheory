/- Passing a scalar evolution equation through an actual sequence by
Lebesgue dominated convergence. The derivative bounds provide an integrable
dominator on every finite interval. -/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalWeakIntegralLimit
open Filter MeasureTheory Set
open scoped Topology

theorem integral_derivative_limit (F G : ℕ → ℝ → ℂ) (f g : ℝ → ℂ) (s t C : ℝ)
    (hd : ∀ n z, HasDerivAt (F n) (G n z) z)
    (hc : ∀ n, Continuous (G n))
    (hb : ∀ n z, z ∈ uIcc s t → ‖G n z‖ ≤ C)
    (hf : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (f z)))
    (hg : ∀ z, Tendsto (fun n => G n z) atTop (𝓝 (g z))) :
    (∫ z in s..t, g z) = f t-f s := by
  have hi : Tendsto (fun n => ∫ z in s..t, G n z) atTop (𝓝 (∫ z in s..t, g z)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    · exact Filter.Eventually.of_forall (fun n => (hc n).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun n => Filter.Eventually.of_forall
        (fun z hz => hb n z (uIoc_subset_uIcc hz)))
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall (fun z _ => hg z)
  have he (n : ℕ) : (∫ z in s..t, G n z) = F n t-F n s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hd n z) ((hc n).intervalIntegrable _ _)
  have hj : Tendsto (fun n => ∫ z in s..t, G n z) atTop (𝓝 (f t-f s)) := by
    simpa only [he] using (hf t).sub (hf s)
  exact tendsto_nhds_unique hi hj

theorem intervalIntegrable_limit (G : ℕ → ℝ → ℂ) (g : ℝ → ℂ) (s t C : ℝ)
    (hc : ∀ n, Continuous (G n))
    (hb : ∀ n z, z ∈ uIcc s t → ‖G n z‖ ≤ C)
    (hg : ∀ z, Tendsto (fun n => G n z) atTop (𝓝 (g z))) :
    IntervalIntegrable g volume s t := by
  rw [intervalIntegrable_iff]
  have hm : AEStronglyMeasurable g (volume.restrict (uIoc s t)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hc n).aestronglyMeasurable)
      (Filter.Eventually.of_forall hg)
  have hi : Integrable (fun _ : ℝ => C) (volume.restrict (uIoc s t)) :=
    intervalIntegrable_iff.mp intervalIntegrable_const
  apply hi.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with z hz
  exact le_of_tendsto (hg z).norm (Filter.Eventually.of_forall
    (fun n => hb n z (uIoc_subset_uIcc hz)))

#print axioms integral_derivative_limit
#print axioms intervalIntegrable_limit

end UnifiedTheory.Audit.KFCausalWeakIntegralLimit
