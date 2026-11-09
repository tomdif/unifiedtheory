/-
  LayerA/MacMahonBridge.lean — MacMahon product vs solid partition counts

  MacMahon conjectured that the number of solid (3D) partitions of n equals
  the coefficient of q^n in ∏_{k≥1} (1 - q^k)^{-k(k+1)/2}.

  This is TRUE through n = 5 and FAILS at n = 6:
    MacMahon product gives 141, actual solid partition count is 140.

  **Free-field interpretation (Amanov–Yeliussizov 2023):**
  The MacMahon product counts solid partitions by corner-hook volume.
  The correction R(q) = D₃(q)/M₃(q) encodes the interaction between
  harmonic oscillators at lattice sites coupled by the monotonicity
  constraint.

  The MacMahon coefficients below are now computed from a genuine infinite
  weighted Euler product, with a proved coefficient bridge. The `solid3`
  values remain an explicitly recorded reference table: this file does not
  verify an enumeration of actual solid partitions.

  The legacy `gap_independent` declarations at the end are elementary
  arithmetic identities. They do not identify a physical transfer operator
  or prove that its spectral gap is insensitive to an interaction.

  Status: ZERO sorrys. ZERO custom axioms.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Basic
import UnifiedTheory.QSeries.WeightedEuler

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.MacMahonBridge

/-! ### MacMahon product coefficients for d = 3

  These are the coefficients of ∏_{k≥1} (1 - q^k)^{-k(k+1)/2},
  defined and computable for every n. -/

/-- Coefficients of the MacMahon product formula for d = 3 solid partitions. -/
def mac3 (n : ℕ) : ℕ := QSeries.macMahonCoefficient n

/-- The computed number is the coefficient of the actual infinite product. -/
theorem mac3_eq_product_coeff (n : ℕ) :
    PowerSeries.coeff n QSeries.macMahonProduct = (mac3 n : ℤ) :=
  QSeries.coeff_macMahonProduct n

/-! ### Actual solid partition counts -/

/-- Reference values from OEIS A000293, entered as data through degree six.
This definition is not a formal combinatorial enumeration. -/
def solid3 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 4
  | 3 => 10
  | 4 => 26
  | 5 => 59
  | 6 => 140
  | _ => 0  -- only defined through n = 6

/-! ### Agreement through n = 5 -/

theorem mac_eq_solid_through_5 : ∀ n : ℕ, n ≤ 5 → mac3 n = solid3 n := by
  intro n hn
  interval_cases n <;> decide

/-! ### First discrepancy at n = 6 -/

theorem mac3_six : mac3 6 = 141 := by decide

/-- The coefficient algorithm also covers degrees beyond the old table. -/
theorem mac3_seven : mac3 7 = 310 := by decide

theorem solid3_six : solid3 6 = 140 := by rfl

theorem first_discrepancy : mac3 6 = 141 ∧ solid3 6 = 140 ∧ mac3 6 ≠ solid3 6 := by
  refine ⟨rfl, rfl, ?_⟩
  rw [mac3_six, solid3_six]
  norm_num

/-! ### The correction at n = 6 -/

theorem correction_at_6 : mac3 6 - solid3 6 = 1 := by
  rw [mac3_six, solid3_six]

/-! ### MacMahon overcounts: mac3 ≥ solid3 through n = 6 -/

theorem mac_ge_solid : ∀ n : ℕ, n ≤ 6 → solid3 n ≤ mac3 n := by
  intro n hn
  interval_cases n <;> decide

/-! ### Spectral gap independence

  These retained compatibility lemmas have only the arithmetic scope of
  their statements. A spectral interpretation requires an independent
  identification with the eigenvalues of the intended operator. -/

/-- Arithmetic comparison retained from the finite model. No operator occurs
in this statement, so it does not itself prove a spectral-gap bound. -/
theorem gap_independent (m : ℕ) (hm : 4 ≤ m) (hm' : m ≤ 100) :
    3 * (m + 1) ≤ 5 * m := by omega

/-- Bookkeeping for the reference discrepancy, retained under its legacy name.
This is not a theorem about invariance of a physical spectral gap. -/
theorem gap_independent_of_correction :
    ∀ n : ℕ, n ≤ 6 → (mac3 n - solid3 n) + solid3 n = mac3 n := by
  intro n hn
  interval_cases n <;> decide

end UnifiedTheory.LayerA.MacMahonBridge
