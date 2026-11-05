/- Even direct Haar coercivity cannot rescue the separately summed upper
coefficient on the growing-volume logarithmic diagnostic path. This is an
obstruction to that proof coefficient, never a lower bound on the true ratio. -/
import UnifiedTheory.Clay.YangMills.WilsonDirectHaarBudget
import UnifiedTheory.Clay.YangMills.WilsonNormalizedBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonDirectHaarObstruction
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonPhysicalVariance WilsonHaarLinkResponse
open WilsonNormalizedBudget Filter
open WilsonHaarBudgetObstruction (coupling coupling_nonneg scalarRate scalarRate_lt_one)

/-- A deliberately coarse elementary envelope is enough to test the volume budget. -/
theorem logarithmic_fourth_bound (m : ℕ) :
    (coupling m+1)^4 ≤ 4*((m : ℝ)+2)^2 := by
  have hx : 0 < (m : ℝ)+2 := by positivity
  have hl : 0 ≤ Real.log ((m : ℝ)+2) := Real.log_nonneg (by
    have h := Nat.cast_nonneg (α := ℝ) m
    linarith)
  have he := Real.pow_div_factorial_le_exp (Real.log ((m : ℝ)+2)) hl 2
  rw [Real.exp_log hx] at he
  norm_num at he
  have hs : (coupling m+1)^2 ≤ 2*((m : ℝ)+2) := by
    unfold coupling
    nlinarith [sq_nonneg (Real.log ((m : ℝ)+2)/8-1), Nat.cast_nonneg (α := ℝ) m]
  have h := (sq_le_sq₀ (sq_nonneg (coupling m+1)) (by positivity)).mpr hs
  nlinarith

variable (n : ℕ) [NeZero n]

theorem coefficient_budget (A D r : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hbudget : 1 ≤ D * A) (m : ℕ) (hr : r < 1)
    (hcap : rate n (coupling m) A (m + 1) ≤ r) :
    (1-r)*(Fintype.card (SpatialVertex n × Fin 3) : ℝ) ≤ 8*D*r := by
  have hc := (rate_le_iff n (coupling m) A r hA (m + 1) (by omega)).mp hcap
  have hB := mul_le_mul_of_nonneg_left (logarithmic_cap_lower m)
    (show 0 ≤ A*(Fintype.card (SpatialVertex n × Fin 3) : ℝ) by positivity)
  have hb : A*(Fintype.card (SpatialVertex n × Fin 3) : ℝ)*((m : ℝ)+1) ≤
      8*cost n (coupling m) A := by
    dsimp only [cost]
    nlinarith
  have hbd := mul_le_mul_of_nonneg_left hb hD
  have hn := mul_le_mul_of_nonneg_right hbudget
    (show 0 ≤ (Fintype.card (SpatialVertex n × Fin 3) : ℝ)*((m : ℝ)+1) by positivity)
  have hp : (Fintype.card (SpatialVertex n × Fin 3) : ℝ)*((m : ℝ)+1) ≤
      8*D*cost n (coupling m) A := by nlinarith
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1-r by linarith)
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 8*D by positivity)
  simp only [Nat.cast_add, Nat.cast_one] at hc'
  have hh : ((1-r)*(Fintype.card (SpatialVertex n × Fin 3) : ℝ))*((m : ℝ)+1) ≤
      (8*D*r)*((m : ℝ)+1) := by nlinarith
  exact (mul_le_mul_iff_left₀ (by positivity : 0 < (m : ℝ)+1)).mp hh

variable [Fact (1 < n)]

/-- This uses direct Haar coercivity, without any heat-bath factorization premise. -/
theorem actual_logarithmic_budget (A r : ℝ) (hA : 0 ≤ A) (m : ℕ)
    (hcoerce : ∀ f : C(Slice n, ℝ), (∀ h u, f (gaugeSlice h u) = f u) →
      variance n (coupling m) (coupling_nonneg m) f ≤
        A * totalEnergy n (coupling m) (coupling_nonneg m) f)
    (hr : r < 1) (hcap : rate n (coupling m) A (m + 1) ≤ r) :
    (1-r)*(Fintype.card (SpatialVertex n × Fin 3) : ℝ) ≤
      12288*(Real.exp 36+1)*(coupling m+1)^4*r := by
  have h := coefficient_budget n A (1536*(Real.exp 36+1)*(coupling m+1)^4) r hA
    (by positivity) (WilsonDirectHaarBudget.coercivity_budget n _ _ A hA hcoerce) m hr hcap
  nlinarith

omit n [NeZero n] [Fact (1 < n)] in
theorem standard_budget (A r : ℝ) (hA : 0 ≤ A) (m : ℕ)
    (hcoerce : ∀ f : C(Slice (m + 2), ℝ), (∀ h u, f (gaugeSlice h u) = f u) →
      variance (m + 2) (coupling m) (coupling_nonneg m) f ≤
        A * totalEnergy (m + 2) (coupling m) (coupling_nonneg m) f)
    (hr : r < 1) (hcap : rate (m + 2) (coupling m) A (m + 1) ≤ r) :
    (1-r)*((m : ℝ)+2) ≤ 16384*(Real.exp 36+1)*r := by
  letI : Fact (1 < m+2) := ⟨by omega⟩
  have hs := cost_nonneg (m + 2) (coupling m) A hA
  have hr0 : 0 ≤ r := (show 0 ≤ rate (m + 2) (coupling m) A (m + 1) by
    unfold rate scalarRate
    exact div_nonneg hs (by positivity)).trans hcap
  have h := actual_logarithmic_budget (m + 2) A r hA m hcoerce hr hcap
  rw [link_count] at h
  push_cast at h
  have hg := mul_le_mul_of_nonneg_right (logarithmic_fourth_bound m)
    (show 0 ≤ 12288*(Real.exp 36+1)*r by positivity)
  have hh : ((1-r)*((m : ℝ)+2))*((m : ℝ)+2)^2 ≤
      (16384*(Real.exp 36+1)*r)*((m : ℝ)+2)^2 := by nlinarith
  exact (mul_le_mul_iff_left₀ (by positivity : 0 < ((m : ℝ)+2)^2)).mp hh

omit n [NeZero n] [Fact (1 < n)] in
/-- An explicit lower bound on the certified coefficient, not on the actual transfer ratio. -/
theorem standard_rate_lower (A : ℝ) (hA : 0 ≤ A) (m : ℕ)
    (hcoerce : ∀ f : C(Slice (m + 2), ℝ), (∀ h u, f (gaugeSlice h u) = f u) →
      variance (m + 2) (coupling m) (coupling_nonneg m) f ≤
        A * totalEnergy (m + 2) (coupling m) (coupling_nonneg m) f) :
    ((m : ℝ)+2)/((m : ℝ)+2+16384*(Real.exp 36+1)) ≤
      rate (m + 2) (coupling m) A (m + 1) := by
  have hr : rate (m + 2) (coupling m) A (m + 1) < 1 :=
    scalarRate_lt_one _ _ (by positivity) (cost_nonneg (m + 2) (coupling m) A hA)
  have h := standard_budget A _ hA m hcoerce hr le_rfl
  apply (div_le_iff₀ (by positivity : 0 < (m : ℝ)+2+16384*(Real.exp 36+1))).mpr
  nlinarith

omit n [NeZero n] [Fact (1 < n)] in
theorem no_uniform_cap (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hcoerce : ∀ m (f : C(Slice (m + 2), ℝ)), (∀ h u, f (gaugeSlice h u) = f u) →
      variance (m + 2) (coupling m) (coupling_nonneg m) f ≤
        A m * totalEnergy (m + 2) (coupling m) (coupling_nonneg m) f)
    (r : ℝ) (hr : r < 1) :
    ¬∀ m, rate (m + 2) (coupling m) (A m) (m + 1) ≤ r := by
  intro hcap
  obtain ⟨m, hm⟩ := exists_nat_gt (16384*(Real.exp 36+1)*r/(1-r))
  have ht := (div_lt_iff₀ (show 0 < 1-r by linarith)).mp hm
  have h := standard_budget (A m) r (hA m) m (hcoerce m) hr (hcap m)
  nlinarith

omit n [NeZero n] [Fact (1 < n)] in
theorem no_eventual_cap (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hcoerce : ∀ m (f : C(Slice (m + 2), ℝ)), (∀ h u, f (gaugeSlice h u) = f u) →
      variance (m + 2) (coupling m) (coupling_nonneg m) f ≤
        A m * totalEnergy (m + 2) (coupling m) (coupling_nonneg m) f)
    (r : ℝ) (hr : r < 1) :
    ¬∀ᶠ m in atTop, rate (m + 2) (coupling m) (A m) (m + 1) ≤ r := by
  intro hcap
  obtain ⟨M, hM⟩ := eventually_atTop.mp hcap
  obtain ⟨m, hm⟩ := exists_nat_gt (max (16384*(Real.exp 36+1)*r/(1-r)) (M : ℝ))
  have hmM : M ≤ m := by
    have h : (M : ℝ) < m := lt_of_le_of_lt (le_max_right _ _) hm
    exact_mod_cast h.le
  have ht := (div_lt_iff₀ (show 0 < 1-r by linarith)).mp
    (lt_of_le_of_lt (le_max_left _ _) hm)
  have h := standard_budget (A m) r (hA m) m (hcoerce m) hr (hM m hmM)
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonDirectHaarObstruction
