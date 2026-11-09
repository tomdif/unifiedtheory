/- Quantitative scope of classical bracket recovery. The parameter bound
used by the current averaged quantum construction forces a positive floor
at fixed nonzero hbar. On bounded log-clock regions its canonical defect
therefore cannot vanish. Large positive log-clock and small-floor regimes
are distinguished explicitly. These are scalar symbol estimates, not
state localization or quantum-to-classical convergence theorems. -/
import UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectLimits
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect

def minimumFloor (hbar : ℝ) : ℝ := 3 * |hbar| / (2 * Real.pi)

theorem minimumFloor_positive (hbar : ℝ) (hh : hbar ≠ 0) :
    0 < minimumFloor hbar := by
  unfold minimumFloor
  exact div_pos (mul_pos (by norm_num) (abs_pos.mpr hh))
    (mul_pos (by norm_num) Real.pi_pos)

theorem minimumFloor_le (ε hbar : ℝ) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    minimumFloor hbar ≤ ε := by
  unfold minimumFloor
  apply (div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr
  linarith

theorem defect_lower_bound (ε k s S : ℝ) (hk : 0 < k) (hε : k ≤ ε) (hs : s ≤ S) :
    k / (Real.exp S + k) ≤ defect ε s := by
  have hε0 : 0 < ε := hk.trans_le hε
  have hc := clock_positive ε s hε0.le
  have hD : 0 < Real.exp S + k := by positivity
  unfold defect
  apply (div_le_div_iff₀ hD hc).mpr
  have hexp := Real.exp_le_exp.mpr hs
  have h1 := mul_nonneg (sub_nonneg.mpr hε) (Real.exp_pos S).le
  have h2 := mul_nonneg hk.le (sub_nonneg.mpr hexp)
  unfold clock
  nlinarith

/-- A positive lower bound uniform over all admissible floors and all s<=S. -/
theorem admissible_bracket_error_lower_bound (ε hbar s S p : ℝ)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (hs : s ≤ S) :
    0 < minimumFloor hbar / (Real.exp S + minimumFloor hbar) ∧
      minimumFloor hbar / (Real.exp S + minimumFloor hbar) ≤
        bracket (longitudinal ε) (fun s _ => clock ε s) s p + 1 := by
  have hk := minimumFloor_positive hbar hh
  have he := minimumFloor_le ε hbar hbound
  rw [bracket_clock_error ε s p (hk.trans_le he).le]
  exact ⟨div_pos hk (by positivity), defect_lower_bound ε _ s S hk he hs⟩

theorem no_bounded_clock_defect_limit {ι : Type*} (l : Filter ι) [l.NeBot]
    (ε s : ι → ℝ) (hbar S : ℝ) (hh : hbar ≠ 0)
    (hbound : ∀ i, |hbar| ≤ 2*Real.pi*ε i/3) (hs : ∀ i, s i ≤ S) :
    ¬Tendsto (fun i => defect (ε i) (s i)) l (𝓝 0) := by
  intro hlim
  have hk := minimumFloor_positive hbar hh
  have hlo : minimumFloor hbar / (Real.exp S + minimumFloor hbar) ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall (fun i =>
      defect_lower_bound (ε i) _ (s i) S hk (minimumFloor_le _ _ (hbound i)) (hs i)))
  exact (not_le_of_gt (div_pos hk (by positivity))) hlo

/-- Recovery at fixed nonzero hbar under the present bound requires escape
to arbitrarily large log-clock, even if the floor varies. It is not supplied
by increasing a matrix capacity while keeping the clock region bounded. -/
theorem defect_limit_forces_large_clock {ι : Type*} (l : Filter ι)
    (ε s : ι → ℝ) (hbar : ℝ) (hh : hbar ≠ 0)
    (hbound : ∀ i, |hbar| ≤ 2*Real.pi*ε i/3)
    (hlim : Tendsto (fun i => defect (ε i) (s i)) l (𝓝 0)) :
    Tendsto s l atTop := by
  apply tendsto_atTop.2
  intro S
  have hk := minimumFloor_positive hbar hh
  have hd : 0 < minimumFloor hbar / (Real.exp S + minimumFloor hbar) :=
    div_pos hk (by positivity)
  filter_upwards [hlim.eventually (gt_mem_nhds hd)] with i hi
  by_contra hs
  have hlo := defect_lower_bound (ε i) _ (s i) S hk
    (minimumFloor_le _ _ (hbound i)) (le_of_not_ge hs)
  exact (not_lt_of_ge hlo) hi

theorem defect_upper_bound (ε s : ℝ) (hε : 0 ≤ ε) :
    defect ε s ≤ ε * Real.exp (-s) := by
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hε (Real.exp_pos s) (by unfold clock; linarith)

theorem defect_large_clock_limit (ε : ℝ) (hε : 0 ≤ ε) :
    Tendsto (defect ε) atTop (𝓝 0) := by
  apply squeeze_zero (fun s => div_nonneg hε (clock_positive ε s hε).le)
    (fun s => defect_upper_bound ε s hε)
  simpa only [mul_zero] using
    Real.tendsto_exp_neg_atTop_nhds_zero.const_mul ε

/-- Pointwise small-floor recovery alone does not preserve the current
averaged-domain bound at fixed nonzero hbar. -/
theorem defect_small_floor_limit (s : ℝ) :
    Tendsto (fun ε => defect ε s) (𝓝 0) (𝓝 0) := by
  have h : ContinuousAt (fun ε : ℝ => ε / (Real.exp s + ε)) 0 :=
    continuousAt_id.div (continuousAt_const.add continuousAt_id)
      (by simp)
  simpa only [defect, clock, zero_div] using h.tendsto

/-- An explicit accuracy estimate, uniform on any region exp(s)>=a. -/
theorem defect_on_clock_region (ε s a δ : ℝ) (hε : 0 ≤ ε)
    (ha : 0 < a) (hs : a ≤ Real.exp s) (hδ : ε ≤ δ*a) :
    defect ε s ≤ δ := by
  have h := div_le_div_of_nonneg_left hε ha
    (show a ≤ clock ε s by unfold clock; linarith)
  exact h.trans ((div_le_iff₀ ha).mpr hδ)

#print axioms minimumFloor_positive
#print axioms minimumFloor_le
#print axioms defect_lower_bound
#print axioms admissible_bracket_error_lower_bound
#print axioms no_bounded_clock_defect_limit
#print axioms defect_limit_forces_large_clock
#print axioms defect_upper_bound
#print axioms defect_large_clock_limit
#print axioms defect_small_floor_limit
#print axioms defect_on_clock_region

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectLimits
