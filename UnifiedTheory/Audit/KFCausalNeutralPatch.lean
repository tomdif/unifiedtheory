/-
  Finite support for first-patch nucleation in a specified Markov model.
  Graph enumeration, mixing, and the physical bath limit are not supplied
  by these lemmas. See NEUTRAL_PATCH_NUCLEATION.md for the exact partition.
-/
import UnifiedTheory.Audit.KFCausalReservoirGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalNeutralPatch
noncomputable section
open scoped BigOperators Matrix

/-- A maximum-level path is neutral until its first strict improvement. -/
theorem first_drop (d : ℕ → ℕ) (top finish : ℕ)
    (hbound : ∀ i ≤ finish, d i ≤ top) (hend : d finish < top) :
    ∃ k ≤ finish, d k < top ∧ ∀ i < k, d i = top := by
  have hex : ∃ k, k ≤ finish ∧ d k < top := ⟨finish, le_rfl, hend⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro i hi
  have hmin := Nat.find_min hex hi
  have hfinish := (Nat.find_spec hex).1
  have hib : i ≤ finish := by omega
  have hd := hbound i hib
  omega

/-- The 150 outward stubs of a good ball need at least 25 outside sites. -/
theorem minimum_patch_carrier (n : ℕ) (hn : 63 ≤ n)
    (hstubs : 150 ≤ 6 * (n - 63)) : 88 ≤ n := by omega

/-- A row with one possible source cannot convert off-diagonal input
entries into its output population. Partial graph flips have this form. -/
theorem single_source_population {X : Type*} [Fintype X] [DecidableEq X]
    (M rho : Matrix X X ℂ) (i j : X)
    (hrow : ∀ k, k ≠ j → M i k = 0) :
    (M * rho * Mᴴ) i i = M i j * rho j j * star (M i j) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · rw [Matrix.conjTranspose_apply, Matrix.mul_apply, Finset.sum_eq_single j]
    · intro k _ hk
      simp [hrow k hk]
    · simp
  · intro k _ hk
    simp [Matrix.conjTranspose_apply, hrow k hk]
  · simp

/-- Disjoint columns make the loss Gram matrix diagonal. -/
theorem disjoint_columns_gram {X : Type*} [Fintype X]
    (M : Matrix X X ℂ) (i j : X)
    (hdisjoint : ∀ k, M k i = 0 ∨ M k j = 0) : (Mᴴ * M) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rcases hdisjoint k with h | h <;> simp [Matrix.conjTranspose_apply, h]

/-- For the resulting classical populations, nonincreasing jumps give
nonpositive bare graph-energy drift. -/
theorem nonpositive_energy_drift {X : Type*} [Fintype X]
    (rate : X → X → ℝ) (prob energy : X → ℝ)
    (hr : ∀ i j, 0 ≤ rate i j) (hp : ∀ j, 0 ≤ prob j)
    (hdrop : ∀ i j, rate i j ≠ 0 → energy i ≤ energy j) :
    (∑ i, ∑ j, rate i j * prob j * (energy i - energy j)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  apply Finset.sum_nonpos
  intro j _
  by_cases h : rate i j = 0
  · simp [h]
  · exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (hr i j) (hp j)) (sub_nonpos.mpr (hdrop i j h))

/-- A mixing estimate at half the event mass gives a hitting opportunity. -/
theorem mixing_event_lower_bound (mass actual error : ℝ)
    (hmix : |actual - mass| ≤ error) (he : error ≤ mass / 2) :
    mass / 2 ≤ actual := by
  have h := abs_le.mp hmix
  linarith

/-- Iterate a uniform block survival bound. -/
theorem block_survival (survival : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hzero : survival 0 ≤ 1)
    (hstep : ∀ k, survival (k + 1) ≤ q * survival k) :
    ∀ k, survival k ≤ q ^ k := by
  intro k
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
    calc
      survival (k + 1) ≤ q * survival k := hstep k
      _ ≤ q * q ^ k := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (k + 1) := by ring

/-- The geometric-block mean bound with success at least half event mass. -/
theorem mean_hitting_bound (mean block success mass : ℝ)
    (hb : 0 ≤ block) (hm : 0 < mass) (hs : mass / 2 ≤ success)
    (hmean : mean ≤ block / success) : mean ≤ 2 * block / mass := by
  have hpos : 0 < success := by linarith
  apply le_trans hmean
  apply (div_le_div_iff₀ hpos hm).mpr
  nlinarith [mul_le_mul_of_nonneg_left hs hb]

#print axioms first_drop
#print axioms minimum_patch_carrier
#print axioms single_source_population
#print axioms disjoint_columns_gram
#print axioms nonpositive_energy_drift
#print axioms mixing_event_lower_bound
#print axioms block_survival
#print axioms mean_hitting_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPatch
