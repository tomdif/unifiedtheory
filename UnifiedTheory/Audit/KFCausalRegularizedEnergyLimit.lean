/- A pointwise limit of regularized energies is conserved when their
continuous derivatives have an integrable uniform bound and converge to
zero. This is the scalar dominated-convergence step of the energy identity. -/
import UnifiedTheory.Audit.KFCausalWeakIntegralLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularizedEnergyLimit
open Filter MeasureTheory Set
open scoped Topology

theorem conserved_of_regularized_energies (E D : ℕ → ℝ → ℝ) (e : ℝ → ℝ) (s t C : ℝ)
    (hd : ∀ n z, HasDerivAt (E n) (D n z) z)
    (hc : ∀ n, Continuous (D n))
    (hb : ∀ n z, z ∈ uIcc s t → ‖D n z‖ ≤ C)
    (he : ∀ z, Tendsto (fun n => E n z) atTop (𝓝 (e z)))
    (hzero : ∀ z, Tendsto (fun n => D n z) atTop (𝓝 0)) : e t = e s := by
  have hi : Tendsto (fun n => ∫ z in s..t, D n z) atTop (𝓝 (0:ℝ)) := by
    have hh := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (a := s) (b := t) (μ := volume) (f := fun _ => (0:ℝ)) (fun _ => C)
      (Filter.Eventually.of_forall (fun n => (hc n).aestronglyMeasurable))
      (Filter.Eventually.of_forall (fun n => Filter.Eventually.of_forall
        (fun z hz => hb n z (uIoc_subset_uIcc hz)))) intervalIntegrable_const
      (Filter.Eventually.of_forall (fun z _ => hzero z))
    simpa only [intervalIntegral.integral_zero] using hh
  have hid (n : ℕ) : (∫ z in s..t, D n z) = E n t-E n s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hd n z) ((hc n).intervalIntegrable _ _)
  have hj : Tendsto (fun n => ∫ z in s..t, D n z) atTop (𝓝 (e t-e s)) := by
    simpa only [hid] using (he t).sub (he s)
  exact sub_eq_zero.mp (tendsto_nhds_unique hj hi)

#print axioms conserved_of_regularized_energies

end UnifiedTheory.Audit.KFCausalRegularizedEnergyLimit
