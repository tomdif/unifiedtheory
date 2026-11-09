/- An obstruction to using the crude Haar-response upper coefficient.
Every valid ground-law factorization constant has A*N_links >= 1. The
resulting certified contraction bound can therefore approach one on a
logarithmic cutoff path, regardless of the chosen factorization constants.
This bounds the proof coefficient, not the actual transfer spectral ratio. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundVarianceBudget
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonHaarBudgetObstruction
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonPhysicalVariance WilsonHaarLinkResponse
open WilsonGroundVarianceBudget Filter
open scoped Topology

def scalarRate (k s : ℝ) : ℝ := s/(k+s)

theorem scalarRate_lt_one (k s : ℝ) (hk : 0 < k) (hs : 0 ≤ s) : scalarRate k s < 1 := by
  unfold scalarRate
  exact (div_lt_one (by linarith : 0 < k+s)).mpr (by linarith)

theorem scalarRate_deficit (k s : ℝ) (hk : 0 < k) (hs : 0 ≤ s) :
    1-scalarRate k s = k/(k+s) := by
  unfold scalarRate
  field_simp [show k+s ≠ 0 by linarith]
  ring

theorem scalarRate_lower (k s : ℝ) (hk : 0 < k) (hs : k ^ 2 ≤ s) :
    1-1/(k+1) ≤ scalarRate k s := by
  have hden : 0 < k+s := by nlinarith [sq_nonneg k]
  have he : 1-1/(k+1) = k/(k+1) := by
    field_simp [show k+1 ≠ 0 by linarith]
    ring
  rw [he, scalarRate]
  exact (div_le_div_iff₀ (by linarith : 0 < k+1) hden).mpr (by nlinarith)

def coupling (m : ℕ) : ℝ := Real.log ((m : ℝ)+2)/8

theorem coupling_nonneg (m : ℕ) : 0 ≤ coupling m := by
  unfold coupling
  exact div_nonneg (Real.log_nonneg (by have h := Nat.cast_nonneg (α := ℝ) m; linarith))
    (by norm_num)

theorem coupling_cost (m : ℕ) : (Real.exp (8*coupling m)-1)^2 = ((m : ℝ)+1)^2 := by
  have he : 8*coupling m = Real.log ((m : ℝ)+2) := by unfold coupling; ring
  rw [he, Real.exp_log (by positivity)]
  ring

variable (n : ℕ) [NeZero n]

def cost (β A : ℝ) : ℝ :=
  A*((Fintype.card (SpatialVertex n × Fin 3) : ℝ)*(Real.exp (8*β)-1)^2)

def rate (β A : ℝ) (k : ℕ) : ℝ := scalarRate k (cost n β A)

theorem cost_nonneg (β A : ℝ) (hA : 0 ≤ A) : 0 ≤ cost n β A := by
  unfold cost
  positivity

theorem cost_lower (β A : ℝ)
    (hbudget : 1 ≤ A * (Fintype.card (SpatialVertex n × Fin 3) : ℝ)) :
    (Real.exp (8*β)-1)^2 ≤ cost n β A := by
  have h := mul_le_mul_of_nonneg_right hbudget (sq_nonneg (Real.exp (8*β)-1))
  simpa only [one_mul, mul_assoc, cost] using h

/-- Necessary cost budget for obtaining a chosen strict contraction from this formula. -/
theorem necessary_budget (β A : ℝ) (hA : 0 ≤ A) (k : ℕ) (hk : 0 < k)
    (hbudget : 1 ≤ A * (Fintype.card (SpatialVertex n × Fin 3) : ℝ))
    (r : ℝ) (hr : r < 1) (hcap : rate n β A k ≤ r) :
    (1-r)*(Real.exp (8*β)-1)^2 ≤ r*k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hs := cost_nonneg n β A hA
  have hc : cost n β A ≤ r*((k : ℝ)+cost n β A) :=
    (div_le_iff₀ (by linarith : 0 < (k : ℝ)+cost n β A)).mp hcap
  have h := mul_le_mul_of_nonneg_left (cost_lower n β A hbudget)
    (by linarith : 0 ≤ 1-r)
  nlinarith

theorem logarithmic_lower (A : ℝ) (m : ℕ)
    (hbudget : 1 ≤ A * (Fintype.card (SpatialVertex n × Fin 3) : ℝ)) :
    1-1/((m : ℝ)+2) ≤ rate n (coupling m) A (m+1) := by
  have hc := cost_lower n (coupling m) A hbudget
  rw [coupling_cost] at hc
  have h := scalarRate_lower ((m : ℝ)+1) (cost n (coupling m) A) (by positivity) hc
  simpa only [rate, Nat.cast_add, Nat.cast_one, show (m : ℝ)+1+1 = (m : ℝ)+2 by ring] using h

variable [Fact (1 < n)]

/-- The actual factorization premise enforces the obstruction, with no positive-variance premise. -/
theorem actual_logarithmic_lower (A : ℝ) (hA : 0 ≤ A) (m : ℕ)
    (hfactor : ∀ f : C(Slice n, ℝ), (∀ h u, f (gaugeSlice h u) = f u) →
      variance n (coupling m) (coupling_nonneg m) f ≤
        A * totalConditionalVariance n (coupling m) (coupling_nonneg m) f) :
    1-1/((m : ℝ)+2) ≤ rate n (coupling m) A (m+1) :=
  logarithmic_lower n A m
    (factorization_budget n (coupling m) (coupling_nonneg m) A hA hfactor)

omit n [NeZero n] [Fact (1 < n)] in
/-- For every spatial-period sequence and every valid factorization constants,
the crude certified coefficient tends to one on this diagnostic logarithmic path. -/
theorem logarithmic_rate_tendsto (period : ℕ → ℕ) [∀ m, NeZero (period m)]
    (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hbudget : ∀ m, 1 ≤ A m * (Fintype.card (SpatialVertex (period m) × Fin 3) : ℝ)) :
    Tendsto (fun m => rate (period m) (coupling m) (A m) (m+1)) atTop (𝓝 1) := by
  have hz : Tendsto (fun m : ℕ => 1/((m : ℝ)+2)) atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    have he : (fun m : ℕ => 1/((m : ℝ)+2)) =
        ((fun m : ℕ => (1 : ℝ)/((m : ℝ)+1)) ∘ fun m : ℕ => m+1) := by
      funext m
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    rw [he]
    exact h
  have hl : Tendsto (fun m : ℕ => 1-1/((m : ℝ)+2)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hz
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
    (fun m => logarithmic_lower (period m) (A m) m (hbudget m))
    (fun m => (scalarRate_lt_one _ _ (by positivity)
      (cost_nonneg (period m) (coupling m) (A m) (hA m))).le)

omit n [NeZero n] [Fact (1 < n)] in
theorem actual_logarithmic_rate_tendsto (period : ℕ → ℕ) [∀ m, NeZero (period m)]
    [∀ m, Fact (1 < period m)] (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hfactor : ∀ m (f : C(Slice (period m), ℝ)),
      (∀ h u, f (gaugeSlice h u) = f u) →
        variance (period m) (coupling m) (coupling_nonneg m) f ≤
          A m * totalConditionalVariance (period m) (coupling m) (coupling_nonneg m) f) :
    Tendsto (fun m => rate (period m) (coupling m) (A m) (m+1)) atTop (𝓝 1) :=
  logarithmic_rate_tendsto period A hA (fun m => factorization_budget (period m)
    (coupling m) (coupling_nonneg m) (A m) (hA m) (hfactor m))

omit n [NeZero n] [Fact (1 < n)] in
/-- A fixed strict cap on this proof coefficient is impossible under the enforced budget. -/
theorem no_uniform_cap (period : ℕ → ℕ) [∀ m, NeZero (period m)]
    (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hbudget : ∀ m, 1 ≤ A m * (Fintype.card (SpatialVertex (period m) × Fin 3) : ℝ))
    (r : ℝ) (hr : r < 1) :
    ¬∀ m, rate (period m) (coupling m) (A m) (m+1) ≤ r := by
  intro h
  have hc := le_of_tendsto (logarithmic_rate_tendsto period A hA hbudget)
    (Filter.Eventually.of_forall h)
  exact (not_le_of_gt hr) hc

omit n [NeZero n] [Fact (1 < n)] in
/-- Discarding finitely many cutoffs cannot restore a fixed strict cap on this coefficient. -/
theorem no_eventual_cap (period : ℕ → ℕ) [∀ m, NeZero (period m)]
    (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hbudget : ∀ m, 1 ≤ A m * (Fintype.card (SpatialVertex (period m) × Fin 3) : ℝ))
    (r : ℝ) (hr : r < 1) :
    ¬∀ᶠ m in atTop, rate (period m) (coupling m) (A m) (m+1) ≤ r := by
  intro h
  exact (not_le_of_gt hr) (le_of_tendsto (logarithmic_rate_tendsto period A hA hbudget) h)

end
end UnifiedTheory.Clay.YangMills.WilsonHaarBudgetObstruction
