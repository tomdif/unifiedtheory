/- Normalization halves the exponential cost in the proved Haar upper
bound, but the sum over all links remains. A local physical source rules
out compensating this factor by a factorization constant of order 1/N. -/
import UnifiedTheory.Clay.YangMills.WilsonNormalizedResponse
import UnifiedTheory.Clay.YangMills.WilsonGroundLocalBudget
import UnifiedTheory.Clay.YangMills.WilsonHaarBudgetObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonNormalizedBudget
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonPhysicalVariance WilsonHaarLinkResponse
open WilsonNormalizedResponse WilsonHaarBudgetObstruction

theorem logarithmic_cap (m : ℕ) :
    haarCap (coupling m) = ((m : ℝ)+1)^2/(4*((m : ℝ)+2)) := by
  have he : 8*coupling m = Real.log ((m : ℝ)+2) := by unfold coupling; ring
  unfold haarCap rangeCoefficient
  rw [he, Real.exp_log (by positivity)]
  congr 2
  ring

theorem logarithmic_cap_upper (m : ℕ) : haarCap (coupling m) ≤ ((m : ℝ)+1)/4 := by
  rw [logarithmic_cap]
  apply (div_le_iff₀ (by positivity : 0 < 4*((m : ℝ)+2))).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

theorem logarithmic_cap_lower (m : ℕ) : ((m : ℝ)+1)/8 ≤ haarCap (coupling m) := by
  rw [logarithmic_cap]
  apply (le_div_iff₀ (by positivity : 0 < 4*((m : ℝ)+2))).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) m, sq_nonneg (m : ℝ)]

variable (n : ℕ) [NeZero n]

theorem link_count : Fintype.card (SpatialVertex n × Fin 3) = n^3*3 := by
  simp [SpatialVertex]

def cost (β A : ℝ) : ℝ :=
  A*((Fintype.card (SpatialVertex n × Fin 3) : ℝ)*haarCap β)

def rate (β A : ℝ) (k : ℕ) : ℝ := scalarRate k (cost n β A)

theorem cost_nonneg (β A : ℝ) (hA : 0 ≤ A) : 0 ≤ cost n β A :=
  mul_nonneg hA (mul_nonneg (Nat.cast_nonneg _) (haarCap_nonneg β))

/-- Exact necessary and sufficient budget for this improved proof coefficient. -/
theorem rate_le_iff (β A r : ℝ) (hA : 0 ≤ A) (k : ℕ) (hk : 0 < k) :
    rate n β A k ≤ r ↔ (1-r)*cost n β A ≤ r*(k : ℝ) := by
  have hs := cost_nonneg n β A hA
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold rate scalarRate
  rw [div_le_iff₀ (by linarith : 0 < (k : ℝ)+cost n β A)]
  constructor <;> intro h <;> nlinarith

/-- The improvement is a factor 4 exp(8 beta) in the combined upper cost. -/
theorem cost_eq_old_div (β A : ℝ) :
    cost n β A = WilsonHaarBudgetObstruction.cost n β A / (4*Real.exp (8*β)) := by
  unfold cost WilsonHaarBudgetObstruction.cost haarCap rangeCoefficient
  ring

/-- The old coupling-only obstruction is removed if the combined factorization
and link-count budget is bounded. No such budget is asserted for growing volume. -/
theorem bounded_budget_cap (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (m : ℕ)
    (hbudget : A * (Fintype.card (SpatialVertex n × Fin 3) : ℝ) ≤ C) :
    rate n (coupling m) A (m + 1) ≤ C/(4+C) := by
  have hc : cost n (coupling m) A ≤ C*((m : ℝ)+1)/4 := by
    have h1 := mul_le_mul_of_nonneg_right hbudget (haarCap_nonneg (coupling m))
    have h2 := mul_le_mul_of_nonneg_left (logarithmic_cap_upper m) hC
    unfold cost
    nlinarith
  apply (rate_le_iff n (coupling m) A (C/(4+C)) hA (m + 1) (by omega)).mpr
  have he : 1-C/(4+C) = 4/(4+C) := by
    field_simp [show 4+C ≠ 0 by linarith]
    ring
  rw [he, Nat.cast_add, Nat.cast_one]
  have h := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4/(4+C) by positivity)
  convert h using 1
  ring

/-- The stronger local-source budget leaves a volume obstruction even after normalization. -/
theorem logarithmic_volume_budget (A r : ℝ) (hA : 0 ≤ A) (hlocal : 1 ≤ 4 * A)
    (m : ℕ) (hr : r < 1) (hcap : rate n (coupling m) A (m + 1) ≤ r) :
    (1-r)*(Fintype.card (SpatialVertex n × Fin 3) : ℝ) ≤ 32*r := by
  have hc := (rate_le_iff n (coupling m) A r hA (m + 1) (by omega)).mp hcap
  have h1 := mul_le_mul_of_nonneg_left (logarithmic_cap_lower m)
    (show 0 ≤ A*(Fintype.card (SpatialVertex n × Fin 3) : ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_right hlocal
    (show 0 ≤ (Fintype.card (SpatialVertex n × Fin 3) : ℝ)*((m : ℝ)+1) by positivity)
  have hl : (Fintype.card (SpatialVertex n × Fin 3) : ℝ)*((m : ℝ)+1) ≤
      32*cost n (coupling m) A := by
    dsimp only [cost]
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left hl (show 0 ≤ 1-r by linarith)
  simp only [Nat.cast_add, Nat.cast_one] at hc
  have hmul : ((1-r)*(Fintype.card (SpatialVertex n × Fin 3) : ℝ))*((m : ℝ)+1) ≤
      (32*r)*((m : ℝ)+1) := by nlinarith
  exact (mul_le_mul_iff_left₀ (by positivity : 0 < (m : ℝ)+1)).mp hmul

variable [Fact (1 < n)]

theorem actual_logarithmic_volume_budget (A r : ℝ) (hA : 0 ≤ A) (m : ℕ)
    (hfactor : ∀ f : C(Slice n, ℝ), (∀ h u, f (gaugeSlice h u) = f u) →
      variance n (coupling m) (coupling_nonneg m) f ≤
        A * totalConditionalVariance n (coupling m) (coupling_nonneg m) f)
    (hr : r < 1) (hcap : rate n (coupling m) A (m + 1) ≤ r) :
    (1-r)*(Fintype.card (SpatialVertex n × Fin 3) : ℝ) ≤ 32*r :=
  logarithmic_volume_budget n A r hA
    (WilsonGroundLocalBudget.factorization_budget n _ _ A hA hfactor) m hr hcap

omit n [NeZero n] [Fact (1 < n)] in
/-- Unbounded spatial link counts preclude a uniform strict cap for this summed bound.
This is not a bound from below on the actual transfer spectral ratio. -/
theorem no_uniform_cap (period : ℕ → ℕ) [∀ m, NeZero (period m)]
    [∀ m, Fact (1 < period m)] (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hfactor : ∀ m (f : C(Slice (period m), ℝ)),
      (∀ h u, f (gaugeSlice h u) = f u) →
        variance (period m) (coupling m) (coupling_nonneg m) f ≤
          A m * totalConditionalVariance (period m) (coupling m) (coupling_nonneg m) f)
    (hvolume : ∀ C : ℝ, ∃ m, C < (Fintype.card (SpatialVertex (period m) × Fin 3) : ℝ))
    (r : ℝ) (hr : r < 1) :
    ¬∀ m, rate (period m) (coupling m) (A m) (m + 1) ≤ r := by
  intro hcap
  obtain ⟨m, hm⟩ := hvolume (32*r/(1-r))
  have h := actual_logarithmic_volume_budget (period m) (A m) r (hA m) m (hfactor m) hr (hcap m)
  have ht := (div_lt_iff₀ (show 0 < 1-r by linarith)).mp hm
  nlinarith

omit n [NeZero n] [Fact (1 < n)] in
theorem standard_volume_unbounded (C : ℝ) :
    ∃ m : ℕ, C < (Fintype.card (SpatialVertex (m + 2) × Fin 3) : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt C
  refine ⟨m, hm.trans_le ?_⟩
  rw [link_count]
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) m, sq_nonneg (m : ℝ),
    mul_nonneg (sq_nonneg (m : ℝ)) (Nat.cast_nonneg (α := ℝ) m)]

omit n [NeZero n] [Fact (1 < n)] in
theorem standard_volume_no_uniform_cap (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hfactor : ∀ m (f : C(Slice (m + 2), ℝ)),
      (∀ h u, f (gaugeSlice h u) = f u) →
        variance (m + 2) (coupling m) (coupling_nonneg m) f ≤
          A m * totalConditionalVariance (m + 2) (coupling m) (coupling_nonneg m) f)
    (r : ℝ) (hr : r < 1) :
    ¬∀ m, rate (m + 2) (coupling m) (A m) (m + 1) ≤ r := by
  letI : ∀ m : ℕ, Fact (1 < m+2) := fun m => ⟨by omega⟩
  exact no_uniform_cap (fun m => m+2) A hA hfactor standard_volume_unbounded r hr

end
end UnifiedTheory.Clay.YangMills.WilsonNormalizedBudget
