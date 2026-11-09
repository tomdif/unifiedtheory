/- A continuous physical rate profile obtained by rearranging the actual
odd-source row response. It improves the earlier constant on an open
region, but its physical cutoff scaling is not asserted. -/
import UnifiedTheory.Clay.YangMills.WilsonPhysicalSeamResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSeamRateProfile
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonCenterTwist WilsonPhysicalVariance
open WilsonPhysicalSeamResponse

theorem fraction_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    a / (4+a) ≤ b / (4+b) := by
  apply (div_le_div_iff₀ (by linarith : 0 < 4+a) (by linarith : 0 < 4+b)).mpr
  nlinarith only [hab]

theorem fraction_lt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a < b) :
    a / (4+a) < b / (4+b) := by
  apply (div_lt_div_iff₀ (by linarith only [ha] : 0 < 4+a)
    (by linarith only [hb] : 0 < 4+b)).mpr
  nlinarith only [hab]

theorem likelihood_coefficient_lt (a b : ℝ) (ha : 1 ≤ a) (hab : a < b) :
    (a-1)^2/a < (b-1)^2/b := by
  apply (div_lt_div_iff₀ (by linarith : 0 < a) (by linarith : 0 < b)).mpr
  have hp : 0 < (b-a)*(a*b-1) := mul_pos (sub_pos.mpr hab) (by nlinarith)
  nlinarith only [hp]

variable (n : ℕ) [NeZero n]

def profile (i : Fin 3) (β : ℝ) : C(Slice n, ℝ) :=
  ⟨fun u => weight n i β u / (4 + weight n i β u),
    (weight_continuous n i β).div (continuous_const.add (weight_continuous n i β))
      (fun u => by have hw := weight_nonneg n i β u; linarith)⟩

theorem profile_nonneg (i : Fin 3) (β : ℝ) (u : Slice n) : 0 ≤ profile n i β u :=
  div_nonneg (weight_nonneg n i β u) (by have hw := weight_nonneg n i β u; linarith)

omit [NeZero n] in
theorem global_rate_fraction (β : ℝ) : WilsonCenterContraction.rate n β =
    WilsonCenterLikelihood.coefficient n β / (4 + WilsonCenterLikelihood.coefficient n β) := by
  have hp : 0 < 4 + WilsonCenterLikelihood.coefficient n β := by
    have hh := WilsonCenterLikelihood.coefficient_nonneg n β
    linarith
  apply (eq_div_iff hp.ne').mpr
  rw [mul_comm, WilsonCenterContraction.coefficient_identity]

theorem profile_le_global (i : Fin 3) (β : ℝ) (u : Slice n) :
    profile n i β u ≤ WilsonCenterContraction.rate n β := by
  rw [global_rate_fraction]
  exact fraction_le _ _ (weight_nonneg n i β u)
    (WilsonCenterLikelihood.coefficient_nonneg n β) (min_le_left _ _)

theorem profile_lt_one (i : Fin 3) (β : ℝ) (u : Slice n) : profile n i β u < 1 :=
  (profile_le_global n i β u).trans_lt (WilsonCenterContraction.rate_lt_one n β)

theorem profile_complement (i : Fin 3) (β : ℝ) (u : Slice n) :
    1 - profile n i β u = 4 / (4 + weight n i β u) := by
  have hp : 0 < 4 + weight n i β u := by
    have hw := weight_nonneg n i β u
    linarith
  change 1 - weight n i β u / (4 + weight n i β u) = _
  field_simp [hp.ne']
  ring

theorem profile_gauge (i : Fin 3) (β : ℝ) (u : Slice n) (h : SliceGauge n Q) :
    profile n i β (gaugeSlice h u) = profile n i β u := by
  simp only [profile, ContinuousMap.coe_mk, weight_gauge]

theorem profile_even (i : Fin 3) (β : ℝ) (u : Slice n) :
    profile n i β (twist n i u) = profile n i β u := by
  simp only [profile, ContinuousMap.coe_mk, weight_twist]

/-- This row estimate needs no unproved source-weighted integral bound. -/
theorem odd_square (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (hf : ∀ u, f (twist n i u) = -f u)
    (u : Slice n) :
    (step n β hβ f u)^2 ≤ profile n i β u * step n β hβ (f^2) u := by
  have hh := clipped_response n i β hβ u f hinv
  rw [WilsonCenterContraction.step_odd n i β hβ f hf u, rowVariance_formula] at hh
  change _ ≤ (weight n i β u / (4 + weight n i β u)) * step n β hβ (f^2) u
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show 0 < 4 + weight n i β u from by
    have hw := weight_nonneg n i β u; linarith)).mpr
  nlinarith only [hh]

/-- At positive coupling and periods at least four, the identity region gives a strict gain. -/
theorem profile_identity_lt (hn : 4 ≤ n) (i : Fin 3) (β : ℝ) (hβ : 0 < β) :
    profile n i β 1 < WilsonCenterContraction.rate n β := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi : Real.pi^2 < 4 * (n : ℝ) := by
    nlinarith only [Real.pi_lt_four, Real.pi_pos, hn4]
  have hcost : β * (Real.pi^2 * n) < 4 * β * (n : ℝ)^2 := by
    have hh := mul_lt_mul_of_pos_right hpi (mul_pos hβ (by linarith : 0 < (n : ℝ)))
    nlinarith only [hh]
  have ha : 1 ≤ scale n i β (1 : Slice n) := by
    apply Real.one_le_exp_iff.mpr
    rw [WilsonSeamGaugePenalty.penalty_identity, add_zero]
    positivity
  have hs : scale n i β (1 : Slice n) < WilsonCenterLikelihood.scale n β := by
    unfold scale WilsonCenterLikelihood.scale
    rw [WilsonSeamGaugePenalty.penalty_identity, add_zero]
    exact Real.exp_lt_exp.mpr hcost
  have hc : coefficient n i β (1 : Slice n) < WilsonCenterLikelihood.coefficient n β :=
    likelihood_coefficient_lt _ _ ha hs
  have hw : weight n i β (1 : Slice n) < WilsonCenterLikelihood.coefficient n β :=
    (min_le_right _ _).trans_lt hc
  rw [global_rate_fraction]
  exact fraction_lt _ _ (weight_nonneg n i β 1)
    (WilsonCenterLikelihood.coefficient_nonneg n β) hw

end
end UnifiedTheory.Clay.YangMills.WilsonSeamRateProfile
