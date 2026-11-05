/-
A constructed finite-matrix influence Green kernel and its spatial decay.
Nonnegative local influences with row sum at most alpha<1 yield summable path
powers, an actual Neumann inverse identity, a volume-independent row bound,
and alpha^distance/(1-alpha) decay from the finite-range condition.
The local degree theorem derives row bounds from local coefficient bounds.

This module does not assume or prove a Gibbs comparison theorem: identifying
its matrix with actual conditional influences and transferring this Green bound
to correlations are separate statements. No physical time or continuum limit
is introduced.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FiniteInfluenceDecay
noncomputable section
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Weighted finite influence paths, with the length-zero identity path included. -/
def paths (C : V → V → ℝ) : ℕ → V → V → ℝ
  | 0, i, j => if i = j then 1 else 0
  | k + 1, i, j => ∑ v, C i v * paths C k v j

theorem paths_eq_matrix_power (C : V → V → ℝ) (k : ℕ) :
    Matrix.of (paths C k) = (Matrix.of C) ^ k := by
  induction k with
  | zero => ext i j; simp [paths, Matrix.one_apply]
  | succ k ih =>
    ext i j
    simp only [pow_succ', Matrix.mul_apply]
    change (∑ v, C i v * paths C k v j) = ∑ v, C i v * (Matrix.of C ^ k) v j
    simp only [← ih, Matrix.of_apply]

theorem paths_nonneg (C : V → V → ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (k : ℕ) (i j : V) : 0 ≤ paths C k i j := by
  induction k generalizing i with
  | zero => simp only [paths]; split <;> norm_num
  | succ k ih => exact Finset.sum_nonneg (fun v _ => mul_nonneg (hC i v) (ih v))

/-- A uniform row-sum bound propagates to every path length, independent of the number of sites. -/
theorem paths_row_bound (C : V → V → ℝ) (α : ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hα : 0 ≤ α) (hrow : ∀ i, ∑ j, C i j ≤ α) (k : ℕ) (i : V) :
    (∑ j, paths C k i j) ≤ α ^ k := by
  induction k generalizing i with
  | zero => simp [paths]
  | succ k ih =>
    calc
      (∑ j, paths C (k + 1) i j) = ∑ v, C i v * ∑ j, paths C k v j := by
        simp only [paths, Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ ∑ v, C i v * α ^ k :=
        Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (ih v) (hC i v))
      _ = (∑ v, C i v) * α ^ k := by rw [Finset.sum_mul]
      _ ≤ α * α ^ k := mul_le_mul_of_nonneg_right (hrow i) (pow_nonneg hα _)
      _ = α ^ (k + 1) := (pow_succ' α k).symm

theorem paths_entry_bound (C : V → V → ℝ) (α : ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hα : 0 ≤ α) (hrow : ∀ i, ∑ j, C i j ≤ α) (k : ℕ) (i j : V) :
    paths C k i j ≤ α ^ k := by
  apply (Finset.single_le_sum (fun v _ => paths_nonneg C hC k i v) (Finset.mem_univ j)).trans
  exact paths_row_bound C α hC hα hrow k i

/-- Finite-range influence cannot reach a site faster than the path length. -/
theorem paths_vanish_before_distance (C : V → V → ℝ) (dist : V → V → ℕ)
    (hself : ∀ i, dist i i = 0) (htri : ∀ i j k, dist i k ≤ dist i j + dist j k)
    (hlocal : ∀ i j, 1 < dist i j → C i j = 0) (k : ℕ) (i j : V)
    (hfar : k < dist i j) : paths C k i j = 0 := by
  induction k generalizing i with
  | zero =>
    have hne : i ≠ j := by intro h; subst j; rw [hself] at hfar; omega
    simp [paths, hne]
  | succ k ih =>
    apply Finset.sum_eq_zero
    intro v _
    by_cases h : 1 < dist i v
    · rw [hlocal i v h, zero_mul]
    · have hv : k < dist v j := by
        have ht := htri i v j
        omega
      rw [ih v hv, mul_zero]

theorem paths_summable (C : V → V → ℝ) (α : ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hα : 0 ≤ α) (hα1 : α < 1) (hrow : ∀ i, ∑ j, C i j ≤ α) (i j : V) :
    Summable (fun k => paths C k i j) :=
  Summable.of_nonneg_of_le (fun k => paths_nonneg C hC k i j)
    (fun k => paths_entry_bound C α hC hα hrow k i j)
    (summable_geometric_of_lt_one hα hα1)

/-- The actual convergent finite-matrix Neumann path sum. -/
def green (C : V → V → ℝ) (i j : V) : ℝ := ∑' k, paths C k i j

/-- Explicit geometric spatial decay of the constructed path sum. -/
theorem green_distance_bound (C : V → V → ℝ) (α : ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hα : 0 ≤ α) (hα1 : α < 1) (hrow : ∀ i, ∑ j, C i j ≤ α)
    (dist : V → V → ℕ) (hself : ∀ i, dist i i = 0)
    (htri : ∀ i j k, dist i k ≤ dist i j + dist j k)
    (hlocal : ∀ i j, 1 < dist i j → C i j = 0) (i j : V) :
    green C i j ≤ α ^ dist i j / (1 - α) := by
  have hs := paths_summable C α hC hα hα1 hrow i j
  have hz : ∑ k ∈ Finset.range (dist i j), paths C k i j = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact paths_vanish_before_distance C dist hself htri hlocal k i j (Finset.mem_range.mp hk)
  have he := hs.sum_add_tsum_nat_add (dist i j)
  rw [hz, zero_add] at he
  unfold green
  rw [← he]
  have hgeo : Summable (fun k : ℕ => α ^ (k + dist i j)) :=
    (summable_geometric_of_lt_one hα hα1).comp_injective (fun _ _ h => Nat.add_right_cancel h)
  calc
    (∑' k, paths C (k + dist i j) i j) ≤ ∑' k, α ^ (k + dist i j) :=
      Summable.tsum_le_tsum (fun k => paths_entry_bound C α hC hα hrow _ i j)
        (hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)) hgeo
    _ = α ^ dist i j / (1 - α) := by
      simp_rw [pow_add]
      rw [tsum_mul_right, tsum_geometric_of_abs_lt_one (by simpa [abs_of_nonneg hα] using hα1)]
      ring

/-- The constructed Green kernel is nonnegative. -/
theorem green_nonneg (C : V → V → ℝ) (hC : ∀ i j, 0 ≤ C i j) (i j : V) :
    0 ≤ green C i j := tsum_nonneg (fun k => paths_nonneg C hC k i j)

/-- The total Green response is volume independent. -/
theorem green_row_bound (C : V → V → ℝ) (α : ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hα : 0 ≤ α) (hα1 : α < 1) (hrow : ∀ i, ∑ j, C i j ≤ α) (i : V) :
    (∑ j, green C i j) ≤ 1 / (1 - α) := by
  have he := Summable.tsum_finsetSum (fun j (_ : j ∈ (Finset.univ : Finset V)) =>
    paths_summable C α hC hα hα1 hrow i j)
  have hs : Summable (fun k => ∑ j, paths C k i j) :=
    Summable.of_nonneg_of_le
      (fun k => Finset.sum_nonneg (fun j _ => paths_nonneg C hC k i j))
      (fun k => paths_row_bound C α hC hα hrow k i)
      (summable_geometric_of_lt_one hα hα1)
  unfold green
  rw [← he]
  calc
    (∑' k, ∑ j, paths C k i j) ≤ ∑' k : ℕ, α ^ k :=
      Summable.tsum_le_tsum (fun k => paths_row_bound C α hC hα hrow k i) hs
        (summable_geometric_of_lt_one hα hα1)
    _ = 1 / (1 - α) := by
      rw [tsum_geometric_of_abs_lt_one (by simpa [abs_of_nonneg hα] using hα1), one_div]

/-- The infinite path sum satisfies its actual Neumann equation. -/
theorem green_neumann (C : V → V → ℝ) (α : ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hα : 0 ≤ α) (hα1 : α < 1) (hrow : ∀ i, ∑ j, C i j ≤ α) (i j : V) :
    green C i j = (if i = j then 1 else 0) + ∑ v, C i v * green C v j := by
  have hs := paths_summable C α hC hα hα1 hrow i j
  unfold green
  rw [hs.tsum_eq_zero_add]
  simp only [paths]
  rw [Summable.tsum_finsetSum (fun v (_ : v ∈ (Finset.univ : Finset V)) =>
    (paths_summable C α hC hα hα1 hrow v j).mul_left (C i v))]
  simp only [tsum_mul_left]

/-- A genuine inverse identity for the finite matrix, not an assumed resolvent. -/
theorem green_resolves (C : V → V → ℝ) (α : ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hα : 0 ≤ α) (hα1 : α < 1) (hrow : ∀ i, ∑ j, C i j ≤ α) :
    ((1 : Matrix V V ℝ) - Matrix.of C) * Matrix.of (green C) = 1 := by
  have he : Matrix.of (green C) = 1 + Matrix.of C * Matrix.of (green C) := by
    ext i j
    simpa only [Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.of_apply] using
      green_neumann C α hC hα hα1 hrow i j
  rw [sub_mul, one_mul]
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he)

omit [DecidableEq V] in
/-- A degree bound and a local influence size give the row bound without a volume factor. -/
theorem local_degree_row_bound (C : V → V → ℝ) (neighbors : V → Finset V)
    (δ : ℝ) (D : ℕ) (hδ : 0 ≤ δ)
    (hC : ∀ i j, C i j ≤ δ) (hsupport : ∀ i j, j ∉ neighbors i → C i j = 0)
    (hdegree : ∀ i, (neighbors i).card ≤ D) (i : V) :
    (∑ j, C i j) ≤ D * δ := by
  have he : ∑ j, C i j = ∑ j ∈ neighbors i, C i j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    exact hsupport i j hj
  rw [he]
  calc
    (∑ j ∈ neighbors i, C i j) ≤ ∑ _j ∈ neighbors i, δ :=
      Finset.sum_le_sum (fun j _ => hC i j)
    _ = (neighbors i).card * δ := by simp
    _ ≤ D * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree i) hδ

end
end UnifiedTheory.Clay.YangMills.FiniteInfluenceDecay
