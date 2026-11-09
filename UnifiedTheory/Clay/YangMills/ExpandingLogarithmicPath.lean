/- An explicit shrinking-mesh, expanding-volume logarithmic regulator path.
The variance prefactor diverges on this path; no Wilson moment premise is
included here. Actual-law lower bounds can therefore be applied separately. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ExpandingLogarithmicPath
noncomputable section
open Filter
open scoped Topology

def period (k : ℕ) : ℕ := 2 * (k + 1) ^ 3
def spacing (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1) ^ 2
def coupling (b : ℝ) (k : ℕ) : ℝ := 2 * b * Real.log ((k : ℝ) + 1)

theorem period_gt_one (k : ℕ) : 1 < period k := by
  unfold period
  have h : 1 ≤ (k + 1) ^ 3 := Nat.one_le_pow 3 (k + 1) (by omega)
  omega

instance periodNeZero (k : ℕ) : NeZero (period k) := ⟨by have := period_gt_one k; omega⟩
instance periodFact (k : ℕ) : Fact (1 < period k) := ⟨period_gt_one k⟩

theorem period_even (k : ℕ) : 2 ∣ period k := dvd_mul_right 2 _
theorem spacing_pos (k : ℕ) : 0 < spacing k := by unfold spacing; positivity

theorem cast_successor_tendsto :
    Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
  tendsto_atTop_mono (fun k => by linarith) tendsto_natCast_atTop_atTop

theorem spacing_tendsto : Tendsto spacing atTop (𝓝 0) := by
  have h := ((tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp
    cast_successor_tendsto).inv_tendsto_atTop
  convert h using 1
  funext k
  simp [spacing]

theorem physical_size (k : ℕ) : (period k : ℝ) * spacing k = 2 * ((k : ℝ) + 1) := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  simp only [period, spacing, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add,
    Nat.cast_one]
  field_simp

theorem physical_size_tendsto :
    Tendsto (fun k => (period k : ℝ) * spacing k) atTop atTop := by
  simp_rw [physical_size]
  exact cast_successor_tendsto.const_mul_atTop (by norm_num)

theorem coupling_tendsto (b : ℝ) (hb : 0 < b) : Tendsto (coupling b) atTop atTop :=
  (Real.tendsto_log_atTop.comp cast_successor_tendsto).const_mul_atTop (by positivity)

theorem coupling_log_spacing (b : ℝ) (k : ℕ) :
    coupling b k = b * Real.log (spacing k)⁻¹ := by
  unfold coupling spacing
  rw [one_div, inv_inv, Real.log_pow]
  ring

/-- Exact growth factor entering the physical second-moment lower bound. -/
theorem variance_prefactor (b : ℝ) (k : ℕ) :
    spacing k ^ (-8 : ℤ) / ((period k : ℝ) ^ 4 * coupling b k ^ 2) =
      ((k : ℝ) + 1) ^ 4 / (64 * b ^ 2 * Real.log ((k : ℝ) + 1) ^ 2) := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  simp only [spacing, period, coupling, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one, zpow_neg]
  field_simp
  ring

/-- A deliberately coarse polynomial lower bound already proves divergence. -/
theorem variance_prefactor_lower (b : ℝ) (hb : 0 < b) (k : ℕ) (hk : 1 ≤ k) :
    ((k : ℝ) + 1) ^ 2 / (64 * b ^ 2) ≤
      spacing k ^ (-8 : ℤ) / ((period k : ℝ) ^ 4 * coupling b k ^ 2) := by
  rw [variance_prefactor]
  have hx : 1 < (k : ℝ) + 1 := by exact_mod_cast (show 1 < k + 1 by omega)
  have hl : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos hx
  have hlog : Real.log ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (k : ℝ) + 1)
    linarith
  have hs : Real.log ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 :=
    pow_le_pow_left₀ hl.le hlog 2
  apply (div_le_div_iff₀ (by positivity : 0 < 64 * b ^ 2)
    (by positivity : 0 < 64 * b ^ 2 * Real.log ((k : ℝ) + 1) ^ 2)).mpr
  have h := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ (64 * b ^ 2) * ((k : ℝ) + 1) ^ 2 by positivity)
  nlinarith

theorem variance_prefactor_tendsto (b : ℝ) (hb : 0 < b) :
    Tendsto (fun k => spacing k ^ (-8 : ℤ) /
      ((period k : ℝ) ^ 4 * coupling b k ^ 2)) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (eventually_atTop.2 ⟨1, fun k hk => variance_prefactor_lower b hb k hk⟩)
  have h := ((tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp
    cast_successor_tendsto).const_mul_atTop
      (show 0 < (64 * b ^ 2)⁻¹ by positivity)
  simpa only [div_eq_mul_inv, Function.comp_apply, mul_comm] using h

/-- The divergence persists for every eventually positive coupling below a
fixed logarithmic upper bracket, not just the exact logarithmic path. -/
theorem variance_prefactor_tendsto_of_log_upper (β : ℕ → ℝ) (b : ℝ) (hb : 0 < b)
    (hpos : ∀ᶠ k in atTop, 0 < β k)
    (hupper : ∀ᶠ k in atTop, β k ≤ coupling b k) :
    Tendsto (fun k => spacing k ^ (-8 : ℤ) /
      ((period k : ℝ) ^ 4 * β k ^ 2)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (variance_prefactor_tendsto b hb)
  filter_upwards [hpos, hupper] with k hk hu
  have hn : 0 < (period k : ℝ) := by
    exact_mod_cast (show 0 < period k by have := period_gt_one k; omega)
  apply div_le_div_of_nonneg_left (by positivity)
    (by positivity : 0 < (period k : ℝ) ^ 4 * β k ^ 2)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk.le hu 2) (by positivity)

end
end UnifiedTheory.Clay.YangMills.ExpandingLogarithmicPath
