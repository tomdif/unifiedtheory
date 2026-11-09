/- Exact state counting for the existing finite occupation simplex.
The grading is total occupation, not an assumed energy spectrum. -/
import UnifiedTheory.Audit.KFCausalFiniteOccupationLadders
import UnifiedTheory.QSeries.WeightedEuler
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalOccupationSeries
noncomputable section
open scoped BigOperators
open KFCausalFiniteOccupationLadders
open UnifiedTheory.QSeries PowerSeries Matrix

/-- An actual shell of the retained occupation basis. -/
abbrev Shell (m R n : ℕ) := {v : Active m R // total v.val = n}

/-- Removing the coordinate cutoff loses no states when `n ≤ R`. -/
def shellEquivNatSum (m R n : ℕ) (hn : n ≤ R) :
    Shell m R n ≃ {v : Fin m → ℕ // ∑ a, v a = n} where
  toFun v := ⟨fun a => (v.val.val a : ℕ), v.property⟩
  invFun v := ⟨⟨fun a => ⟨v.val a, by
    have h := Finset.single_le_sum (f := v.val) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ a)
    rw [v.property] at h
    omega⟩, by simpa [total] using v.property.le.trans hn⟩, v.property⟩
  left_inv v := by rfl
  right_inv v := by rfl

/-- Stars and bars, proved for the model's basis rather than postulated degeneracies. -/
theorem card_shell (m R n : ℕ) (hm : 0 < m) (hn : n ≤ R) :
    Fintype.card (Shell m R n) = (m - 1 + n).choose (m - 1) := by
  let e := (shellEquivNatSum m R n hn).trans (Sym.equivNatSumOfFintype (Fin m) n).symm
  rw [Fintype.card_congr e, Sym.card_sym_eq_choose, Fintype.card_fin]
  have h : m + n - 1 = m - 1 + n := by omega
  rw [h, ← Nat.choose_symm (show m - 1 ≤ m - 1 + n by omega)]
  congr 1
  omega

/-- Exactly `m` modes of occupation weight one; no higher-weight modes are added. -/
def occupationMultiplicity (m k : ℕ) : ℕ := if k = 1 then m else 0

theorem occupation_partial (m N : ℕ) :
    weightedEulerPartial (occupationMultiplicity m) (N + 1) = (invOneSubPow ℤ m).val := by
  induction N with
  | zero => simp [weightedEulerPartial, eulerFactor, occupationMultiplicity]
  | succ N ih =>
    rw [weightedEulerPartial_succ, ih]
    simp [eulerFactor, occupationMultiplicity, invOneSubPow_zero]

theorem occupation_euler (m : ℕ) :
    weightedEuler (occupationMultiplicity m) = (invOneSubPow ℤ m).val := by
  ext n
  rw [coeff_weightedEuler _ (Nat.le_succ n), occupation_partial]

/-- The infinite Euler product counts every retained shell exactly, below the cutoff. -/
theorem card_shell_eq_euler_coeff (m R n : ℕ) (hm : 0 < m) (hn : n ≤ R) :
    (Fintype.card (Shell m R n) : ℤ) =
      coeff n (weightedEuler (occupationMultiplicity m)) := by
  rw [card_shell m R n hm hn, occupation_euler,
    invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ m hm, coeff_mk]

/-- Dimension of complex amplitudes on the actual shell. -/
theorem shell_dimension_eq_euler_coeff (m R n : ℕ) (hm : 0 < m) (hn : n ≤ R) :
    (Module.finrank ℂ (Shell m R n → ℂ) : ℤ) =
      coeff n (weightedEuler (occupationMultiplicity m)) := by
  rw [Module.finrank_fintype_fun_eq_card]
  exact card_shell_eq_euler_coeff m R n hm hn

/-- Finite occupation character: sum over the existing states, with multiplicity one. -/
def occupationCharacter (m R : ℕ) : PowerSeries ℤ :=
  ∑ v : Active m R, X ^ total v.val

theorem coeff_occupationCharacter (m R n : ℕ) :
    coeff n (occupationCharacter m R) = (Fintype.card (Shell m R n) : ℤ) := by
  classical
  simp [occupationCharacter, coeff_X_pow, Shell, Fintype.card_subtype, eq_comm]

theorem occupationCharacter_matches_euler (m R n : ℕ) (hm : 0 < m) (hn : n ≤ R) :
    coeff n (occupationCharacter m R) = coeff n (weightedEuler (occupationMultiplicity m)) := by
  rw [coeff_occupationCharacter]
  exact card_shell_eq_euler_coeff m R n hm hn

theorem occupationCharacter_above_cutoff (m R n : ℕ) (hn : R < n) :
    coeff n (occupationCharacter m R) = 0 := by
  classical
  simp only [occupationCharacter, map_sum, coeff_X_pow]
  apply Finset.sum_eq_zero
  intro v _
  have h : total v.val ≠ n := by have := v.property; omega
  simp [Ne.symm h]

/-- The sum of the model's unit-weight annihilator squares is its number operator.
This uses the exact finite-capacity ladder identity, including the top shell. -/
theorem ladder_number_operator (m R : ℕ) :
    (∑ a : Fin m, (compress (annihilator (R := R) (fun _ => 1) a))ᴴ *
      compress (annihilator (fun _ => 1) a)) =
      Matrix.diagonal (fun v : Active m R => (total v.val : ℂ)) := by
  simp_rw [active_adjoint_square]
  ext i j
  simp only [Matrix.sum_apply]
  by_cases hij : i = j
  · subst j
    simp only [diagonal_apply_eq, weight, if_pos i.property]
    simp [total, Nat.cast_sum]
  · simp [hij]

end
end UnifiedTheory.Audit.KFCausalOccupationSeries
