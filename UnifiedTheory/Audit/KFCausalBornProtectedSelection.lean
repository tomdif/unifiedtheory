/-
  Exact preservation of protected records during microscopic selection.

  Inspired by moment-preserving residual corrections, this is finite
  probability algebra, not an imported Navier--Stokes or Einstein theorem.
  Conditional centering constructs a probability correction that preserves
  the whole protected-record law and decreases a chosen defect exactly.
-/

import UnifiedTheory.Audit.KFCausalBornMicroscopicSelection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornProtectedSelection
noncomputable section
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

def recordFiber (H : ι → κ) (k : κ) : Finset ι :=
  Finset.univ.filter fun i => H i = k

def fiberMean (p G : ι → ℝ) (H : ι → κ) (k : κ) : ℝ :=
  (∑ i ∈ recordFiber H k, p i * G i) / ∑ i ∈ recordFiber H k, p i

def conditionalResidual (p G : ι → ℝ) (H : ι → κ) (i : ι) : ℝ :=
  G i - fiberMean p G H (H i)

def protectedStep (p r : ι → ℝ) (epsilon : ℝ) (i : ι) : ℝ :=
  p i * (1 - epsilon * r i)

theorem conditionalResidual_fiber_centered (p G : ι → ℝ) (H : ι → κ)
    (hp : ∀ i, 0 < p i) (k : κ) :
    ∑ i ∈ recordFiber H k, p i * conditionalResidual p G H i = 0 := by
  by_cases hEmpty : recordFiber H k = ∅
  · simp [hEmpty]
  · have hmass : 0 < ∑ i ∈ recordFiber H k, p i :=
      Finset.sum_pos (fun i _ => hp i) (Finset.nonempty_iff_ne_empty.mpr hEmpty)
    calc
      _ = ∑ i ∈ recordFiber H k, p i * (G i - fiberMean p G H k) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hh : H i = k := (Finset.mem_filter.mp hi).2
        simp [conditionalResidual, hh]
      _ = (∑ i ∈ recordFiber H k, p i * G i) -
          (∑ i ∈ recordFiber H k, p i) * fiberMean p G H k := by
        simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      _ = 0 := by
        unfold fiberMean
        field_simp
        ring

theorem centered_annihilates_record_observable (p r : ι → ℝ) (H : ι → κ)
    (hcenter : ∀ k, ∑ i ∈ recordFiber H k, p i * r i = 0)
    (f : κ → ℝ) :
    ∑ i, p i * r i * f (H i) = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ.image H)
    (fun i hi => Finset.mem_image_of_mem H hi)]
  change ∑ k ∈ Finset.univ.image H,
    ∑ i ∈ recordFiber H k, p i * r i * f (H i) = 0
  apply Finset.sum_eq_zero
  intro k _
  calc
    _ = ∑ i ∈ recordFiber H k, p i * r i * f k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = (∑ i ∈ recordFiber H k, p i * r i) * f k :=
      (Finset.sum_mul _ _ _).symm
    _ = 0 := by rw [hcenter, zero_mul]

/-- Exact for finite epsilon: preserves all functions and all moments of
the protected record, not only its first two response coefficients. -/
theorem protectedStep_preserves_record_observables (p r : ι → ℝ)
    (H : ι → κ) (epsilon : ℝ)
    (hcenter : ∀ k, ∑ i ∈ recordFiber H k, p i * r i = 0)
    (f : κ → ℝ) :
    ∑ i, protectedStep p r epsilon i * f (H i) = ∑ i, p i * f (H i) := by
  have hz := centered_annihilates_record_observable p r H hcenter f
  calc
    _ = (∑ i, p i * f (H i)) - epsilon * ∑ i, p i * r i * f (H i) := by
      simp only [protectedStep, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hz, mul_zero, sub_zero]

theorem protectedStep_normalized (p r : ι → ℝ) (H : ι → κ) (epsilon : ℝ)
    (hcenter : ∀ k, ∑ i ∈ recordFiber H k, p i * r i = 0)
    (hsum : ∑ i, p i = 1) :
    ∑ i, protectedStep p r epsilon i = 1 := by
  have h := protectedStep_preserves_record_observables p r H epsilon hcenter (fun _ => 1)
  simpa using h.trans (by simpa using hsum)

omit [Fintype ι] in
/-- A positive margin supplies full support without an exceptional fallback. -/
theorem protectedStep_pos (p r : ι → ℝ) (epsilon : ℝ)
    (hp : ∀ i, 0 < p i) (hsmall : ∀ i, epsilon * r i < 1) (i : ι) :
    0 < protectedStep p r epsilon i := by
  exact mul_pos (hp i) (sub_pos.mpr (hsmall i))

omit [Fintype ι] in
/-- Finite residuals always admit a positive step with a strict positivity
margin. This discharges the small-step condition without extra dynamics. -/
theorem exists_positive_protected_step_size [Finite ι] (r : ι → ℝ) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ i, epsilon * r i < 1 := by
  letI := Fintype.ofFinite ι
  let M : ℝ := ∑ i, |r i|
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => abs_nonneg (r i)
  have hd : 0 < 2 * (1 + M) := by positivity
  refine ⟨1 / (2 * (1 + M)), by positivity, ?_⟩
  intro i
  have hi : r i ≤ M :=
    (le_abs_self _).trans (Finset.single_le_sum
      (fun j _ => abs_nonneg (r j)) (Finset.mem_univ i))
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  apply (div_lt_one hd).2
  linarith

theorem conditionalResidual_defect_pairing (p G : ι → ℝ) (H : ι → κ)
    (hp : ∀ i, 0 < p i) :
    ∑ i, p i * conditionalResidual p G H i * G i =
      ∑ i, p i * conditionalResidual p G H i ^ 2 := by
  have hz := centered_annihilates_record_observable p
    (conditionalResidual p G H) H (conditionalResidual_fiber_centered p G H hp)
    (fiberMean p G H)
  calc
    _ = (∑ i, p i * conditionalResidual p G H i ^ 2) +
        ∑ i, p i * conditionalResidual p G H i * fiberMean p G H (H i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      unfold conditionalResidual
      ring
    _ = _ := by rw [hz, add_zero]

/-- The gain is exactly the within-record variance times the step size.
This is a change of expectation over one fixed parent's alternatives. -/
theorem protectedStep_exact_defect_descent (p G : ι → ℝ) (H : ι → κ)
    (epsilon : ℝ) (hp : ∀ i, 0 < p i) :
    ∑ i, protectedStep p (conditionalResidual p G H) epsilon i * G i =
      (∑ i, p i * G i) - epsilon * ∑ i, p i * conditionalResidual p G H i ^ 2 := by
  calc
    _ = (∑ i, p i * G i) - epsilon *
        ∑ i, p i * conditionalResidual p G H i * G i := by
      simp only [protectedStep, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [conditionalResidual_defect_pairing p G H hp]

theorem protectedStep_strict_defect_descent (p G : ι → ℝ) (H : ι → κ)
    (epsilon : ℝ) (hp : ∀ i, 0 < p i) (he : 0 < epsilon)
    (hvar : 0 < ∑ i, p i * conditionalResidual p G H i ^ 2) :
    ∑ i, protectedStep p (conditionalResidual p G H) epsilon i * G i <
      ∑ i, p i * G i := by
  rw [protectedStep_exact_defect_descent p G H epsilon hp]
  exact sub_lt_self _ (mul_pos he hvar)

/-- The protected correction has a full-support scalar coherent/Born lift.
No physical identification of H or G is smuggled into this finite theorem. -/
theorem protectedStep_has_coherent_born_lift (n : ℕ)
    (p G : Fin (n + 1) → ℝ) (H : Fin (n + 1) → κ)
    (epsilon : ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hsmall : ∀ i, epsilon * conditionalResidual p G H i < 1) :
    ∃ b : Fin (n + 1) → ℂ,
      (∑ i, b i) = 1 ∧
      ∀ i, Complex.normSq (b i) = protectedStep p (conditionalResidual p G H) epsilon i := by
  apply KFCausalBornMicroscopicSelection.exists_coherent_prescribed_born
  · intro i
    exact (protectedStep_pos p _ epsilon hp hsmall i).le
  · exact protectedStep_normalized p _ H epsilon
      (conditionalResidual_fiber_centered p G H hp) hsum

#print axioms conditionalResidual_fiber_centered
#print axioms protectedStep_preserves_record_observables
#print axioms protectedStep_exact_defect_descent
#print axioms exists_positive_protected_step_size
#print axioms protectedStep_has_coherent_born_lift

end
end UnifiedTheory.Audit.KFCausalBornProtectedSelection
