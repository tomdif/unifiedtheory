/- A quantitative positive-mass fiber of an actual finite measurable
partition. No lower bound on neighborhood mass is assumed. -/
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FinitePartitionMass
noncomputable section
open MeasureTheory

variable {X I : Type*} [MeasurableSpace X] [Fintype I] [Nonempty I]
  (μ : Measure X) [IsProbabilityMeasure μ] (s : X → I)
  (hs : ∀ i, MeasurableSet (s ⁻¹' {i}))

include hs in
theorem fiber_mass_sum : (∑ i, μ.real (s ⁻¹' {i})) = 1 := by
  have h := sum_measureReal_preimage_singleton (μ := μ) Finset.univ (fun i _ => hs i)
  simpa using h

include hs in
theorem exists_large_fiber : ∃ i, 1 / (Fintype.card I : ℝ) ≤ μ.real (s ⁻¹' {i}) := by
  classical
  have hc : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  by_contra h
  push_neg at h
  have hh := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => h i)
  have he : (∑ _ : I, 1 / (Fintype.card I : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [fiber_mass_sum μ s hs, he] at hh
  exact (lt_irrefl (1 : ℝ)) hh

include hs in
theorem exists_representative :
    ∃ x : X, 1 / (Fintype.card I : ℝ) ≤ μ.real (s ⁻¹' {s x}) := by
  obtain ⟨i,hi⟩ := exists_large_fiber μ s hs
  have hc : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hp : 0 < μ.real (s ⁻¹' {i}) := (div_pos zero_lt_one hc).trans_le hi
  obtain ⟨x,hx⟩ := nonempty_of_measureReal_ne_zero (ne_of_gt hp)
  have hx' : s x = i := hx
  exact ⟨x, by simpa only [hx'] using hi⟩

end
end UnifiedTheory.Clay.YangMills.FinitePartitionMass
