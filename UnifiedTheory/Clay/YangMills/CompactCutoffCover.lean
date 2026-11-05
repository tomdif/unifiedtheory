/- Continuous square partitions cover overlapping regions without charging
an L2 residual separately for every member of the cover. -/
import UnifiedTheory.Clay.YangMills.CompactDensityEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactCutoffCover
noncomputable section

variable {X I : Type*} [TopologicalSpace X] [Fintype I]

def squareSum (χ : I → C(X, ℝ)) : C(X, ℝ) := ∑ i, χ i ^ 2

def normalizer (χ : I → C(X, ℝ)) : C(X, ℝ) :=
  ⟨fun x => Real.sqrt (max 1 (squareSum χ x)),
    (continuous_const.max (squareSum χ).continuous).sqrt⟩

theorem normalizer_ge_one (χ : I → C(X, ℝ)) (x : X) : 1 ≤ normalizer χ x := by
  change 1 ≤ Real.sqrt (max 1 (squareSum χ x))
  exact (Real.one_le_sqrt).mpr (le_max_left _ _)

def weight (χ : I → C(X, ℝ)) (i : I) : C(X, ℝ) :=
  ⟨fun x => χ i x / normalizer χ x,
    (χ i).continuous.div (normalizer χ).continuous
      (fun x => (lt_of_lt_of_le zero_lt_one (normalizer_ge_one χ x)).ne')⟩

theorem weight_range (χ : I → C(X, ℝ)) (hχ : ∀ i x, χ i x ∈ Set.Icc 0 1)
    (i : I) (x : X) : weight χ i x ∈ Set.Icc 0 1 := by
  have hd := normalizer_ge_one χ x
  change χ i x / normalizer χ x ∈ Set.Icc 0 1
  refine ⟨div_nonneg (hχ i x).1 (by linarith), ?_⟩
  apply (div_le_one (by linarith : 0 < normalizer χ x)).mpr
  exact (hχ i x).2.trans hd

theorem weight_zero (χ : I → C(X, ℝ)) (i : I) (x : X) (h : χ i x = 0) :
    weight χ i x = 0 := by simp only [weight, ContinuousMap.coe_mk, h, zero_div]

theorem sum_square (χ : I → C(X, ℝ)) (x : X) :
    (∑ i, (weight χ i x)^2) = squareSum χ x / max 1 (squareSum χ x) := by
  simp only [weight, ContinuousMap.coe_mk, div_pow, ← Finset.sum_div]
  rw [show (normalizer χ x)^2 = max 1 (squareSum χ x) from
    Real.sq_sqrt (le_trans zero_le_one (le_max_left _ _))]
  congr 1
  simp only [squareSum, ContinuousMap.sum_apply, ContinuousMap.pow_apply]

theorem sum_square_le (χ : I → C(X, ℝ)) (x : X) : ∑ i, (weight χ i x)^2 ≤ 1 := by
  rw [sum_square]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr (le_max_right _ _)

/-- Any cutoff equal to one makes the square partition cover the point exactly. -/
theorem sum_square_one (χ : I → C(X, ℝ)) (x : X) (h : ∃ i, χ i x = 1) :
    ∑ i, (weight χ i x)^2 = 1 := by
  obtain ⟨i,hi⟩ := h
  have hs : 1 ≤ squareSum χ x := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (χ j x))
      (Finset.mem_univ i)
    simpa only [hi, one_pow, squareSum, ContinuousMap.sum_apply,
      ContinuousMap.pow_apply] using hh
  rw [sum_square, max_eq_right hs, div_self (by linarith : squareSum χ x ≠ 0)]

theorem weight_eq_of_values (χ : I → C(X, ℝ)) (x y : X) (h : ∀ i, χ i x = χ i y)
    (i : I) : weight χ i x = weight χ i y := by
  have hs : squareSum χ x = squareSum χ y := by
    simp only [squareSum, ContinuousMap.sum_apply, ContinuousMap.pow_apply, h]
  simp only [weight, normalizer, ContinuousMap.coe_mk, h, hs]

end
end UnifiedTheory.Clay.YangMills.CompactCutoffCover
