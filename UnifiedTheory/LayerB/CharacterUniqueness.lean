/-
  LayerB/CharacterUniqueness.lean — Every continuous character of (ℝ,+) is exponential

  THEOREM: If χ : ℝ → S¹ is continuous with χ(x+y) = χ(x)·χ(y),
  then ∃ α : ℝ, ∀ t, χ(t) = Circle.exp(α·t).

  PROOF: Construct α via stabilization of 2^k · arg(χ(1/2^k)).
  Show χ = Circle.exp(α·-) on dyadic rationals.
  Conclude by density of dyadics and continuity.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.RealVectorSpace

noncomputable section

namespace UnifiedTheory.LayerB.CharacterUniqueness

open Circle Real Complex

/-! ## Local additivity of arg on Circle -/

lemma arg_mul_real_of_small (z w : Circle)
    (hz : |arg (z : ℂ)| < π / 2) (hw : |arg (w : ℂ)| < π / 2) :
    arg ((z * w : Circle) : ℂ) = arg (z : ℂ) + arg (w : ℂ) := by
  rw [Circle.coe_mul]
  have hza := abs_lt.mp hz
  have hwa := abs_lt.mp hw
  exact Complex.arg_mul z.coe_ne_zero w.coe_ne_zero ⟨by linarith, by linarith⟩

lemma arg_char_double (χ : AddChar ℝ Circle) (s : ℝ)
    (hs : |arg (χ s : ℂ)| < π / 4) :
    arg (χ (2 * s) : ℂ) = 2 * arg (χ s : ℂ) := by
  have hmul : χ (2 * s) = χ s * χ s := by
    rw [show 2 * s = s + s by ring]; exact AddChar.map_add_eq_mul χ s s
  have hpi : π / 4 < π / 2 := by linarith [Real.pi_pos]
  conv_lhs => rw [show (χ (2 * s) : ℂ) = ((χ s * χ s : Circle) : ℂ) by rw [← hmul]]
  rw [arg_mul_real_of_small (χ s) (χ s) (lt_trans hs hpi) (lt_trans hs hpi)]
  ring

/-! ## Good radius -/

lemma exists_good_K (χ : AddChar ℝ Circle) (hχ : Continuous χ) :
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k → |arg (χ (1 / (2 : ℝ) ^ k) : ℂ)| < π / 4 := by
  have h0 : arg (χ 0 : ℂ) = 0 := by simp [AddChar.map_zero_eq_one, arg_one]
  -- arg(χ(·)) is continuous at 0
  have harg_cont : ContinuousAt (fun t : ℝ => arg (χ t : ℂ)) 0 := by
    show ContinuousAt (arg ∘ (fun t => (χ t : ℂ))) 0
    apply ContinuousAt.comp
    · have h1 : χ 0 = 1 := AddChar.map_zero_eq_one χ
      have : (χ 0 : ℂ) = (1 : Circle) := congr_arg Subtype.val h1
      rw [this, Circle.coe_one]
      exact continuousAt_arg (Or.inl (by norm_num))
    · exact (continuous_subtype_val.comp hχ).continuousAt
  -- 1/2^k → 0
  have hseq : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / 2 ^ k) Filter.atTop (nhds 0) := by
    simp_rw [one_div]
    exact (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)).congr (fun _ => rfl)
  -- Combine
  have hcont : Filter.Tendsto (fun k : ℕ => arg (χ (1 / (2 : ℝ) ^ k) : ℂ))
      Filter.atTop (nhds 0) := by
    rw [← h0]; exact harg_cont.tendsto.comp hseq
  rw [Metric.tendsto_atTop] at hcont
  obtain ⟨K₀, hK₀⟩ := hcont (π / 4) (by positivity)
  exact ⟨K₀, fun k hk => by
    have := hK₀ k hk; rwa [Real.dist_eq, sub_zero] at this⟩

/-! ## Stabilization -/

lemma lift_stabilize (χ : AddChar ℝ Circle) {K₀ : ℕ}
    (hK : ∀ k : ℕ, K₀ ≤ k → |arg (χ (1 / (2 : ℝ) ^ k) : ℂ)| < π / 4)
    {k : ℕ} (hk : K₀ ≤ k) :
    (2 : ℝ) ^ (k + 1) * arg (χ (1 / (2 : ℝ) ^ (k + 1)) : ℂ) =
    (2 : ℝ) ^ k * arg (χ (1 / (2 : ℝ) ^ k) : ℂ) := by
  have hk1 : K₀ ≤ k + 1 := Nat.le_succ_of_le hk
  have hs := hK (k + 1) hk1
  -- Use arg_char_double: arg(χ(2s)) = 2 * arg(χ(s)) when |arg(χ(s))| < π/4
  -- With s = 1/2^(k+1): 2s = 1/2^k.
  have hconv : 2 * (1 / (2 : ℝ) ^ (k + 1)) = 1 / (2 : ℝ) ^ k := by
    rw [pow_succ]; field_simp
  have h_double := arg_char_double χ (1 / (2 : ℝ) ^ (k + 1)) hs
  rw [hconv] at h_double
  -- h_double : arg(χ(1/2^k)) = 2 * arg(χ(1/2^(k+1)))
  -- Goal: 2^(k+1) * arg(χ(1/2^(k+1))) = 2^k * arg(χ(1/2^k))
  rw [h_double, pow_succ]
  ring

lemma lift_eq_stable (χ : AddChar ℝ Circle) {K₀ : ℕ}
    (hK : ∀ k : ℕ, K₀ ≤ k → |arg (χ (1 / (2 : ℝ) ^ k) : ℂ)| < π / 4)
    {k : ℕ} (hk : K₀ ≤ k) :
    (2 : ℝ) ^ k * arg (χ (1 / (2 : ℝ) ^ k) : ℂ) =
    (2 : ℝ) ^ K₀ * arg (χ (1 / (2 : ℝ) ^ K₀) : ℂ) := by
  induction k with
  | zero =>
    have : K₀ = 0 := Nat.eq_zero_of_le_zero hk; subst this; rfl
  | succ n ih =>
    by_cases hn : K₀ ≤ n
    · rw [lift_stabilize χ hK hn, ih hn]
    · have hK₀ : K₀ = n + 1 := by omega
      subst hK₀; rfl

/-! ## Dyadic agreement -/

lemma arg_char_eq_div (χ : AddChar ℝ Circle) {K₀ : ℕ}
    (hK : ∀ k : ℕ, K₀ ≤ k → |arg (χ (1 / (2 : ℝ) ^ k) : ℂ)| < π / 4)
    {k : ℕ} (hk : K₀ ≤ k) :
    arg (χ (1 / (2 : ℝ) ^ k) : ℂ) =
    ((2 : ℝ) ^ K₀ * arg (χ (1 / (2 : ℝ) ^ K₀) : ℂ)) / (2 : ℝ) ^ k := by
  rw [eq_div_iff (pow_ne_zero _ two_ne_zero), mul_comm]
  exact lift_eq_stable χ hK hk

lemma char_at_dyadic_unit (χ : AddChar ℝ Circle) {K₀ : ℕ}
    (hK : ∀ k : ℕ, K₀ ≤ k → |arg (χ (1 / (2 : ℝ) ^ k) : ℂ)| < π / 4)
    (k : ℕ) (hk : K₀ ≤ k) :
    χ (1 / (2 : ℝ) ^ k) =
    Circle.exp (((2 : ℝ) ^ K₀ * arg (χ (1 / (2 : ℝ) ^ K₀) : ℂ)) / (2 : ℝ) ^ k) := by
  rw [← arg_char_eq_div χ hK hk]
  exact (Circle.exp_arg _).symm

lemma char_at_dyadic (χ : AddChar ℝ Circle) {K₀ : ℕ}
    (hK : ∀ k : ℕ, K₀ ≤ k → |arg (χ (1 / (2 : ℝ) ^ k) : ℂ)| < π / 4)
    (k : ℕ) (hk : K₀ ≤ k) (n : ℤ) :
    χ ((n : ℝ) / (2 : ℝ) ^ k) =
    Circle.exp (((2 : ℝ) ^ K₀ * arg (χ (1 / (2 : ℝ) ^ K₀) : ℂ)) * ((n : ℝ) / (2 : ℝ) ^ k)) := by
  set α := (2 : ℝ) ^ K₀ * arg (χ (1 / (2 : ℝ) ^ K₀) : ℂ)
  -- n / 2^k = n • (1 / 2^k)
  have hconv : (n : ℝ) / (2 : ℝ) ^ k = n • (1 / (2 : ℝ) ^ k) := by
    simp [zsmul_eq_mul]; ring
  rw [hconv, AddChar.map_zsmul_eq_zpow, char_at_dyadic_unit χ hK k hk]
  have hconv2 : α * (↑n / (2 : ℝ) ^ k) = ↑n * (α / (2 : ℝ) ^ k) := by ring
  rw [show α * (n • (1 / (2 : ℝ) ^ k)) = n • (α / (2 : ℝ) ^ k) from by
    simp [zsmul_eq_mul]; ring]
  exact (Circle.exp_zsmul _ _).symm

/-! ## Density of dyadics -/

lemma denseRange_dyadic (K₀ : ℕ) :
    DenseRange (fun p : ℤ × {k : ℕ // K₀ ≤ k} => (p.1 : ℝ) / (2 : ℝ) ^ (p.2 : ℕ)) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- Choose k ≥ K₀ with 1/2^k < ε
  have htend : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) Filter.atTop (nhds 0) := by
    simp_rw [one_div]
    exact (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)).congr (fun _ => rfl)
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend ε hε
  set k := max N K₀
  have hk1 : K₀ ≤ k := le_max_right _ _
  have hk2 : 1 / (2 : ℝ) ^ k < ε := by
    have := hN k (le_max_left _ _)
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  set n := ⌊x * (2 : ℝ) ^ k⌋
  have h2k : (0 : ℝ) < 2 ^ k := pow_pos two_pos k
  refine ⟨(n : ℝ) / 2 ^ k, ⟨⟨n, ⟨k, hk1⟩⟩, rfl⟩, ?_⟩
  have h2k' : (2 : ℝ) ^ k ≠ 0 := ne_of_gt h2k
  rw [dist_comm, Real.dist_eq]
  -- |(n : ℝ) / 2^k - x| = |((n : ℝ) - x * 2^k) / 2^k|
  have : (n : ℝ) / 2 ^ k - x = ((n : ℝ) - x * 2 ^ k) / 2 ^ k := by
    field_simp
  rw [this, abs_div, abs_of_pos h2k]
  calc |↑n - x * 2 ^ k| / 2 ^ k ≤ 1 / 2 ^ k := by
        apply div_le_div_of_nonneg_right _ h2k.le
        rw [abs_le]
        have hfl : (n : ℝ) ≤ x * 2 ^ k := Int.floor_le (x * 2 ^ k)
        have hlt : x * 2 ^ k < (n : ℝ) + 1 := Int.lt_floor_add_one (x * 2 ^ k)
        constructor <;> linarith
    _ < ε := hk2

/-! ## The main theorem -/

theorem continuous_character_is_exp
    (χ : AddChar ℝ Circle) (hχ : Continuous χ) :
    ∃ α : ℝ, ∀ t : ℝ, χ t = Circle.exp (α * t) := by
  obtain ⟨K₀, hK⟩ := exists_good_K χ hχ
  set α := (2 : ℝ) ^ K₀ * arg (χ (1 / (2 : ℝ) ^ K₀) : ℂ)
  use α
  -- Both sides are continuous
  have hexp_cont : Continuous (fun t => Circle.exp (α * t)) :=
    Circle.exp.continuous.comp (continuous_const.mul continuous_id)
  -- They agree on dyadic rationals
  have hdyadic : ∀ (n : ℤ) (k : ℕ), K₀ ≤ k →
      χ ((n : ℝ) / (2 : ℝ) ^ k) = Circle.exp (α * ((n : ℝ) / (2 : ℝ) ^ k)) :=
    fun n k hk => char_at_dyadic χ hK k hk n
  -- Density argument
  have hdense := denseRange_dyadic K₀
  intro t
  have heq : (fun t => χ t) = (fun t => Circle.exp (α * t)) := by
    apply hdense.equalizer hχ hexp_cont
    ext ⟨n, ⟨k, hk⟩⟩
    simp only [Function.comp_apply]
    exact congr_arg Subtype.val (hdyadic n k hk)
  exact congr_fun heq t

end UnifiedTheory.LayerB.CharacterUniqueness
