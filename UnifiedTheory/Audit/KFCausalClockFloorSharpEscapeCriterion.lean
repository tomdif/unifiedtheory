/- Sharp clock probability escape is equivalent to decay of the actual
bounded clock defect, for every uniformly norm-bounded L2 family. -/
import UnifiedTheory.Audit.KFCausalBornLocalization
import UnifiedTheory.Audit.KFCausalClockPositionLaw
import UnifiedTheory.Audit.KFCausalClockFloorDefectLocalization
import UnifiedTheory.Audit.KFCausalClockFloorDefectLimits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorSharpEscapeCriterion
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockPositionLaw
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectLocalization
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalBornLocalization (mask mask_coe mask_norm_square)

theorem sharp_mass (S : ℝ) (f : Hilbert) :
    clockPositionLaw f (Set.Iic S) = ENNReal.ofReal (‖lowProjection S f‖^2) := by
  have hA : MeasurableSet {x : Configuration | x.1 ≤ S} := measurableSet_le measurable_fst measurable_const
  have he : mask volume {x : Configuration | x.1 ≤ S} hA f = lowProjection S f := by
    apply Lp.ext
    filter_upwards [mask_coe volume _ hA f,lowProjection_coe S f] with x hm hl
    rw [hm,hl]
    rfl
  rw [clockPositionLaw_apply f _ measurableSet_Iic,← he,mask_norm_square]
  rfl

theorem projection_escape_iff {ι : Type*} (l : Filter ι) (f : ι → Hilbert) :
    (∀ S, Tendsto (fun t => clockPositionLaw (f t) (Set.Iic S)) l (𝓝 0)) ↔
      (∀ S, Tendsto (fun t => ‖lowProjection S (f t)‖) l (𝓝 0)) := by
  constructor
  · intro ht S
    have hsq := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (ht S)
    simp only [Function.comp_def,sharp_mass,ENNReal.toReal_ofReal (sq_nonneg _),ENNReal.toReal_zero] at hsq
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hs
  · intro ht S
    have hs := ENNReal.tendsto_ofReal ((ht S).pow 2)
    simpa only [sharp_mass,zero_pow (by norm_num : (2 : ℕ) ≠ 0),ENNReal.ofReal_zero] using hs

variable (ε : ℝ) (hε : 0 < ε)
local notation "D" => defectOperator ε hε

theorem defect_cutoff_bound (S : ℝ) (f : Hilbert) :
    ‖D f‖ ≤ ‖lowProjection S f‖+defect ε S*‖f‖ := by
  have hh : ‖D (f-lowProjection S f)‖ ≤ defect ε S*‖f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [defectOperator_coe ε hε (f-lowProjection S f),
      Lp.coeFn_sub f (lowProjection S f),lowProjection_coe S f] with x hd hs hp
    rw [hd,hs]
    simp only [Pi.sub_apply]
    rw [hp]
    by_cases hx : x.1 ≤ S
    · rw [if_pos hx,sub_self,mul_zero,norm_zero]
      exact mul_nonneg (defect_positive ε S hε).le (norm_nonneg _)
    · rw [if_neg hx,sub_zero,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (defect_positive ε x.1 hε)]
      have he : defect ε x.1 ≤ defect ε S := by
        unfold defect
        apply div_le_div_of_nonneg_left hε.le (clock_positive ε S hε.le)
        unfold clock
        linarith [Real.exp_le_exp.mpr (le_of_not_ge hx)]
      exact mul_le_mul_of_nonneg_right he (norm_nonneg _)
  calc
    ‖D f‖ = ‖D (lowProjection S f)+D (f-lowProjection S f)‖ := by
      rw [← map_add,add_sub_cancel]
    _ ≤ ‖D (lowProjection S f)‖+‖D (f-lowProjection S f)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (defectOperator_norm_le ε hε _) hh

theorem defect_of_projection_escape {ι : Type*} (l : Filter ι) (f : ι → Hilbert)
    (C : ℝ) (hC : ∀ t, ‖f t‖ ≤ C)
    (ht : ∀ S, Tendsto (fun t => ‖lowProjection S (f t)‖) l (𝓝 0)) :
    Tendsto (fun t => ‖D (f t)‖) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hd : Tendsto (fun S => defect ε S*C) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (KFCausalClockFloorDefectLimits.defect_large_clock_limit ε hε.le).mul_const C
  obtain ⟨S,hS⟩ := (hd.eventually (gt_mem_nhds (by linarith : 0 < η/2))).exists
  filter_upwards [(ht S).eventually (gt_mem_nhds (by linarith : 0 < η/2))] with t htime
  have hb := (defect_cutoff_bound ε hε S (f t)).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hC t) (defect_positive ε S hε).le))
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]
  linarith only [hb,hS,htime]

theorem sharp_escape_iff_defect {ι : Type*} (l : Filter ι) (f : ι → Hilbert)
    (C : ℝ) (hC : ∀ t, ‖f t‖ ≤ C) :
    (∀ S, Tendsto (fun t => clockPositionLaw (f t) (Set.Iic S)) l (𝓝 0)) ↔
      Tendsto (fun t => ‖D (f t)‖) l (𝓝 0) := by
  rw [projection_escape_iff]
  exact ⟨defect_of_projection_escape ε hε l f C hC,
    fun hd S => lowProjection_tendsto_zero l ε hε f hd S⟩

#print axioms sharp_mass
#print axioms projection_escape_iff
#print axioms defect_cutoff_bound
#print axioms defect_of_projection_escape
#print axioms sharp_escape_iff_defect

end
end UnifiedTheory.Audit.KFCausalClockFloorSharpEscapeCriterion
