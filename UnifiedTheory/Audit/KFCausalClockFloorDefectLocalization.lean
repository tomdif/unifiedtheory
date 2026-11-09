/- Small norm of the actual defect multiplier forces small probability
below every fixed log-clock threshold. This holds for arbitrary L2 states,
independently of charge or energy-domain membership. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectLocalization
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalContractiveMultiplier

def lowWeight (S : ℝ) (x : Configuration) : ℂ := if x.1 ≤ S then 1 else 0

theorem lowWeight_measurable (S : ℝ) : Measurable (lowWeight S) := by
  unfold lowWeight
  exact Measurable.ite (measurableSet_le measurable_fst measurable_const) measurable_const measurable_const

theorem lowWeight_bound (S : ℝ) (x : Configuration) : ‖lowWeight S x‖ ≤ 1 := by
  unfold lowWeight
  split_ifs <;> norm_num

def lowProjection (S : ℝ) : Hilbert →L[ℂ] Hilbert :=
  multiplyL (lowWeight S) (lowWeight_measurable S) (lowWeight_bound S)

theorem lowProjection_coe (S : ℝ) (f : Hilbert) :
    lowProjection S f =ᵐ[volume] fun x => if x.1 ≤ S then f x else 0 := by
  filter_upwards [multiplyL_coe (lowWeight S) (lowWeight_measurable S) (lowWeight_bound S) f] with x hx
  change lowProjection S f x = lowWeight S x * f x at hx
  rw [hx, lowWeight]
  split_ifs <;> simp

/-- Squaring the norm on the left gives the probability below S for a unit state. -/
theorem lowProjection_defect_bound (ε : ℝ) (hε : 0 < ε) (S : ℝ) (f : Hilbert) :
    ‖lowProjection S f‖ ≤ ((Real.exp S+ε)/ε) * ‖defectOperator ε hε f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [lowProjection_coe S f, defectOperator_coe ε hε f] with x hP hD
  rw [hP,hD,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (defect_positive ε x.1 hε)]
  by_cases hs : x.1 ≤ S
  · rw [if_pos hs, ← mul_assoc]
    have he : (Real.exp S+ε)/ε * defect ε x.1 = (Real.exp S+ε)/clock ε x.1 := by
      unfold defect
      field_simp
    have hle : 1 ≤ (Real.exp S+ε)/ε * defect ε x.1 := by
      rw [he, le_div_iff₀ (clock_positive ε x.1 hε.le), one_mul]
      unfold clock
      linarith [Real.exp_le_exp.mpr hs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hle (norm_nonneg (f x))
  · rw [if_neg hs, norm_zero]
    exact mul_nonneg (div_pos (by positivity) hε).le
      (mul_nonneg (defect_positive ε x.1 hε).le (norm_nonneg _))

theorem lowProjection_tendsto_zero {ι : Type*} (l : Filter ι) (ε : ℝ) (hε : 0 < ε)
    (f : ι → Hilbert) (hf : Tendsto (fun i => ‖defectOperator ε hε (f i)‖) l (𝓝 0)) (S : ℝ) :
    Tendsto (fun i => ‖lowProjection S (f i)‖) l (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _) (fun i => lowProjection_defect_bound ε hε S (f i))
  simpa only [mul_zero] using hf.const_mul ((Real.exp S+ε)/ε)

#print axioms lowWeight_measurable
#print axioms lowWeight_bound
#print axioms lowProjection_coe
#print axioms lowProjection_defect_bound
#print axioms lowProjection_tendsto_zero

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectLocalization
