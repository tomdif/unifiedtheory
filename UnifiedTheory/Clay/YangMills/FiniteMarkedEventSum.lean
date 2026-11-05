/- Counting endpoint events by marked witnesses, before integration. This
retains endpoint multiplicity without paying the number of ambient vertices. -/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FiniteMarkedEventSum
noncomputable section
open MeasureTheory

variable {X V I : Type*} [Fintype V] [Fintype I]

theorem pointwise (S : I → Finset V) (E : V → Set X) (H : I → Set X)
    (hcover : ∀ q x, x ∈ E q → ∃ i, q ∈ S i ∧ x ∈ H i)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (x : X) :
    (∑ q, (E q).indicator f x) ≤ ∑ i, ((S i).card : ℝ) * (H i).indicator f x := by
  classical
  have hq (q : V) : (E q).indicator f x ≤
      ∑ i : I, if q ∈ S i then (H i).indicator f x else 0 := by
    by_cases hx : x ∈ E q
    · obtain ⟨i,hqi,hxi⟩ := hcover q x hx
      have h := Finset.single_le_sum (s := Finset.univ) (a := i)
        (f := fun j => if q ∈ S j then (H j).indicator f x else 0)
        (fun j _ => by
          dsimp only
          split_ifs
          · exact Set.indicator_nonneg (fun y _ => hf y) x
          · exact le_rfl) (Finset.mem_univ i)
      simpa only [if_pos hqi, Set.indicator_of_mem hxi, Set.indicator_of_mem hx] using h
    · rw [Set.indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun i _ => by
        split_ifs
        · exact Set.indicator_nonneg (fun y _ => hf y) x
        · exact le_rfl)
  apply (Finset.sum_le_sum (fun q _ => hq q)).trans_eq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem integral_sum [MeasurableSpace X] (μ : Measure X)
    (S : I → Finset V) (E : V → Set X) (H : I → Set X)
    (hE : ∀ q, MeasurableSet (E q)) (hH : ∀ i, MeasurableSet (H i))
    (hcover : ∀ q x, x ∈ E q → ∃ i, q ∈ S i ∧ x ∈ H i)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (hi : Integrable f μ) :
    (∑ q, ∫ x, (E q).indicator f x ∂μ) ≤
      ∑ i, ((S i).card : ℝ) * ∫ x, (H i).indicator f x ∂μ := by
  have hleft := integrable_finset_sum Finset.univ (fun q _ => hi.indicator (hE q))
  have hright := integrable_finset_sum Finset.univ
    (fun i _ => (hi.indicator (hH i)).const_mul ((S i).card : ℝ))
  have h := integral_mono hleft hright (pointwise S E H hcover f hf)
  rw [integral_finset_sum _ (fun q _ => hi.indicator (hE q)),
    integral_finset_sum _ (fun i _ => (hi.indicator (hH i)).const_mul ((S i).card : ℝ))] at h
  simpa only [integral_const_mul] using h

end
end UnifiedTheory.Clay.YangMills.FiniteMarkedEventSum
