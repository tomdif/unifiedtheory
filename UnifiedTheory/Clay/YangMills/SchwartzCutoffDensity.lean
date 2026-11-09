/- Explicit compact cutoffs converge in every Schwartz seminorm. A fixed
smooth bump is dilated; its uniformly bounded derivatives and one additional
Schwartz weight give an inverse-radius estimate. No density premise is used. -/
import UnifiedTheory.Clay.YangMills.PositiveTimeCutoff
import UnifiedTheory.Clay.YangMills.SchwartzTranslations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SchwartzCutoffDensity
noncomputable section
open Filter
open scoped Topology

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def bump : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩

def profile : SchwartzMap E ℂ :=
  ((bump E).hasCompactSupport.comp_left (show Complex.ofReal 0 = 0 by rfl)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (bump E).contDiff)

@[simp] theorem profile_apply (x : E) : profile E x = (bump E x : ℂ) := rfl

def radius (R : ℕ) : ℝ := (R : ℝ) + 1

theorem radius_pos (R : ℕ) : 0 < radius R := by unfold radius; positivity

def dilation (R : ℕ) : E →L[ℝ] E := (radius R)⁻¹ • ContinuousLinearMap.id ℝ E

@[simp] theorem dilation_apply (R : ℕ) (x : E) : dilation E R x = (radius R)⁻¹ • x := rfl

theorem dilation_norm_le (R : ℕ) : ‖dilation E R‖ ≤ 1 := by
  have hr : 1 ≤ radius R := by unfold radius; linarith [Nat.cast_nonneg (α := ℝ) R]
  calc
    ‖dilation E R‖ = |(radius R)⁻¹| * ‖ContinuousLinearMap.id ℝ E‖ := by
      rw [dilation, norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * 1 := mul_le_mul
      (by rw [abs_of_pos (inv_pos.mpr (radius_pos R))]; exact inv_le_one_of_one_le₀ hr)
      (ContinuousLinearMap.norm_id_le) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

def multiplier (R : ℕ) : E → ℂ := profile E ∘ dilation E R

theorem multiplier_temperate (R : ℕ) : Function.HasTemperateGrowth (multiplier E R) :=
  (profile E).hasTemperateGrowth.comp (dilation E R).hasTemperateGrowth

def cutoff (R : ℕ) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.smulLeftCLM ℂ (multiplier E R) f

@[simp] theorem cutoff_apply (R : ℕ) (f : SchwartzMap E ℂ) (x : E) :
    cutoff E R f x = multiplier E R x * f x := by
  rw [cutoff, SchwartzMap.smulLeftCLM_apply_apply (multiplier_temperate E R), smul_eq_mul]

theorem multiplier_one (R : ℕ) (x : E) (hx : ‖x‖ ≤ radius R) : multiplier E R x = 1 := by
  have hb : dilation E R x ∈ Metric.closedBall (0 : E) (bump E).rIn := by
    simp only [Metric.mem_closedBall, dist_zero_right, dilation_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (radius_pos R))]
    change (radius R)⁻¹ * ‖x‖ ≤ 1
    exact (inv_mul_le_iff₀ (radius_pos R)).mpr (by simpa using hx)
  simp only [multiplier, Function.comp_apply, profile_apply,
    (bump E).one_of_mem_closedBall hb, Complex.ofReal_one]

theorem error_derivative_bound (R i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y => multiplier E R y - 1) x‖ ≤
      SchwartzMap.seminorm ℂ 0 i (profile E) + 1 := by
  have hq : ContDiff ℝ i (multiplier E R) :=
    ((profile E).smooth i).comp (dilation E R).contDiff
  have hlin := SchwartzProductTensor.projection_derivative_bound
    (dilation E R) (dilation_norm_le E R) (profile E) i x
  have hc : ‖iteratedFDeriv ℝ i (fun _ : E => (1 : ℂ)) x‖ ≤ 1 := by
    cases i with
    | zero => simp only [norm_iteratedFDeriv_zero, norm_one, le_refl]
    | succ i => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, zero_le_one]
  have he : (fun y => multiplier E R y - 1) =
      (multiplier E R) + -(fun _ : E => (1 : ℂ)) := by funext y; rfl
  have hn : ContDiffAt ℝ i (-(fun _ : E => (1 : ℂ))) x := contDiffAt_const.neg
  rw [he, iteratedFDeriv_add_apply hq.contDiffAt hn,
    iteratedFDeriv_neg_apply]
  calc
    _ ≤ ‖iteratedFDeriv ℝ i (multiplier E R) x‖ +
        ‖iteratedFDeriv ℝ i (fun _ : E => (1 : ℂ)) x‖ := by
      simpa only [sub_eq_add_neg] using norm_sub_le
        (iteratedFDeriv ℝ i (multiplier E R) x)
        (iteratedFDeriv ℝ i (fun _ : E => (1 : ℂ)) x)
    _ ≤ SchwartzMap.seminorm ℂ 0 i (profile E) + 1 :=
      add_le_add (hlin.trans ((profile E).norm_iteratedFDeriv_le_seminorm ℂ i _)) hc

def bound (f : SchwartzMap E ℂ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    (SchwartzMap.seminorm ℂ 0 i (profile E)+1) * SchwartzMap.seminorm ℂ (k+1) (n-i) f

theorem bound_nonneg (f : SchwartzMap E ℂ) (k n : ℕ) : 0 ≤ bound E f k n := by
  unfold bound
  exact Finset.sum_nonneg (fun i _ => by positivity)

theorem weighted_error_bound (R : ℕ) (f : SchwartzMap E ℂ) (k n : ℕ) (x : E) :
    ‖x‖^k * ‖iteratedFDeriv ℝ n (cutoff E R f - f) x‖ ≤ bound E f k n / radius R := by
  by_cases hx : ‖x‖ < radius R
  · have he : ((cutoff E R f - f : SchwartzMap E ℂ) : E → ℂ) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hx] with y hy
      simp only [SchwartzMap.sub_apply, cutoff_apply, multiplier_one E R y hy.le,
        one_mul, sub_self]
    have hd := (he.iteratedFDeriv ℝ n).self_of_nhds
    rw [hd]
    cases n <;> simp [norm_iteratedFDeriv_zero, iteratedFDeriv_succ_const,
      div_nonneg (bound_nonneg E f k _) (radius_pos R).le]
  · have hrx : radius R ≤ ‖x‖ := le_of_not_gt hx
    have hq : ContDiff ℝ n (fun y => multiplier E R y - 1) :=
      (((profile E).smooth n).comp (dilation E R).contDiff).sub contDiff_const
    have he : ((cutoff E R f - f : SchwartzMap E ℂ) : E → ℂ) =
        fun y => (multiplier E R y - 1) * f y := by
      funext y
      simp only [SchwartzMap.sub_apply, cutoff_apply]
      ring
    rw [he]
    apply (le_div_iff₀ (radius_pos R)).mpr
    have hder := norm_iteratedFDeriv_mul_le hq (f.smooth n) x le_rfl
    calc
      _ ≤ radius R * ‖x‖^k * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y => multiplier E R y - 1) x‖ *
          ‖iteratedFDeriv ℝ (n-i) f x‖ := by
        nlinarith [mul_le_mul_of_nonneg_left hder
          (mul_nonneg (radius_pos R).le (pow_nonneg (norm_nonneg x) k))]
      _ ≤ bound E f k n := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hf : radius R * (‖x‖^k * ‖iteratedFDeriv ℝ (n-i) f x‖) ≤
            SchwartzMap.seminorm ℂ (k+1) (n-i) f := by
          calc
            _ ≤ ‖x‖ * (‖x‖^k * ‖iteratedFDeriv ℝ (n-i) f x‖) := by gcongr
            _ = ‖x‖^(k+1) * ‖iteratedFDeriv ℝ (n-i) f x‖ := by rw [pow_succ]; ring
            _ ≤ _ := f.le_seminorm ℂ (k+1) (n-i) x
        calc
          _ = (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => multiplier E R y - 1) x‖ *
              (radius R * (‖x‖^k * ‖iteratedFDeriv ℝ (n-i) f x‖)) := by ring
          _ ≤ _ := mul_le_mul
            (mul_le_mul_of_nonneg_left (error_derivative_bound E R i x) (Nat.cast_nonneg _))
            hf (mul_nonneg (radius_pos R).le (by positivity)) (by positivity)

theorem seminorm_cutoff_bound (R : ℕ) (f : SchwartzMap E ℂ) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (cutoff E R f - f) ≤ bound E f k n / radius R :=
  SchwartzMap.seminorm_le_bound ℂ k n _
    (div_nonneg (bound_nonneg E f k n) (radius_pos R).le)
    (weighted_error_bound E R f k n)

theorem cutoff_tendsto (f : SchwartzMap E ℂ) :
    Tendsto (fun R => cutoff E R f) atTop (𝓝 f) := by
  apply ((schwartz_withSeminorms ℂ E ℂ).tendsto_nhds _ f).mpr
  rintro ⟨k,n⟩ eps heps
  have hr : Tendsto radius atTop atTop :=
    tendsto_atTop_mono (fun R : ℕ => show (R : ℝ) ≤ radius R by unfold radius; linarith)
      tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun R => bound E f k n / radius R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hr
  filter_upwards [hz.eventually (gt_mem_nhds heps)] with R hR
  exact (seminorm_cutoff_bound E R f k n).trans_lt hR

/-- The constructed cutoff is zero outside an explicit expanding ball. -/
theorem cutoff_support_bound (R : ℕ) (f : SchwartzMap E ℂ) (x : E)
    (hx : cutoff E R f x ≠ 0) : ‖x‖ < 2 * radius R := by
  rw [cutoff_apply] at hx
  have hq : multiplier E R x ≠ 0 := (mul_ne_zero_iff.mp hx).1
  have hb : bump E (dilation E R x) ≠ 0 := by
    simpa only [multiplier, Function.comp_apply, profile_apply, Complex.ofReal_ne_zero] using hq
  have hm : dilation E R x ∈ Function.support (bump E) := hb
  rw [(bump E).support_eq] at hm
  have hn : (radius R)⁻¹ * ‖x‖ < 2 := by
    simpa only [Metric.mem_ball, dist_zero_right, dilation_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (radius_pos R))] using hm
  simpa only [mul_comm] using (inv_mul_lt_iff₀ (radius_pos R)).mp hn

theorem cutoff_hasCompactSupport (R : ℕ) (f : SchwartzMap E ℂ) :
    HasCompactSupport (cutoff E R f) := by
  apply (isCompact_closedBall (0 : E) (2 * radius R)).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using
    (cutoff_support_bound E R f x hx).le)

end
end UnifiedTheory.Clay.YangMills.SchwartzCutoffDensity
