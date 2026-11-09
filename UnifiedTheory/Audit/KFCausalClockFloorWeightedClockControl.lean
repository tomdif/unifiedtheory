/- The analytic clock localization is bounded below on every finite
clock band. Together with the two clock tails this controls the defect. -/
import UnifiedTheory.Audit.KFCausalClockFloorLocalizedVacuum
import UnifiedTheory.Audit.KFCausalClockFloorSharpEscapeCriterion
import Mathlib.Topology.Order.Compact

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorWeightedClockControl
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorDefectOperator
open KFCausalClockFloorDefectLocalization (lowProjection lowProjection_coe)
open KFCausalClockFloorCanonicalDefect (defect response response_add_defect response_bounds defect_positive)
open KFCausalClockFloorLocalizedVacuum (clockWeight)
open KFCausalClockFloorBoundedInverse (inverseL)

def weight (ε s : ℝ) : ℝ := (Real.sqrt (Real.exp s+ε))⁻¹*defect ε s*(1-defect ε s)
def weighted (ε : ℝ) (hε : 0 < ε) : Hilbert →L[ℂ] Hilbert :=
  (inverseL ε hε).comp (clockWeight ε hε)

theorem weight_positive (ε : ℝ) (hε : 0 < ε) (s : ℝ) : 0 < weight ε s := by
  have hr : 0 < 1-defect ε s := by
    linarith [response_add_defect ε s hε.le,(response_bounds ε s hε).1]
  exact mul_pos (mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)))
    (defect_positive ε s hε)) hr

theorem weight_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (weight ε) := by
  have hc : Continuous (fun s : ℝ => Real.exp s+ε) := Real.continuous_exp.add continuous_const
  have hn (s : ℝ) : Real.exp s+ε ≠ 0 := (show 0 < Real.exp s+ε by positivity).ne'
  have hd : Continuous (defect ε) := continuous_const.div hc hn
  exact ((hc.sqrt.inv₀ (fun s => (Real.sqrt_pos.mpr (by positivity : 0 < Real.exp s+ε)).ne')).mul hd).mul
    (continuous_const.sub hd)

theorem weighted_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    weighted ε hε f =ᵐ[volume] fun x => (weight ε x.1:ℂ)*f x := by
  filter_upwards [KFCausalClockFloorClockHalf.inverseAction_coe ε hε (clockWeight ε hε f),
    Lp.coeFn_sub (defectOperator ε hε f) (defectOperator ε hε (defectOperator ε hε f)),
    defectOperator_coe ε hε f,defectOperator_coe ε hε (defectOperator ε hε f)] with x hi hs h1 h2
  change weighted ε hε f x=(Real.sqrt (Real.exp x.1+ε):ℂ)⁻¹*(clockWeight ε hε f) x at hi
  rw [hi]
  change _*(defectOperator ε hε f-defectOperator ε hε (defectOperator ε hε f)) x = _
  rw [hs,Pi.sub_apply,h2,h1]
  simp only [weight,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_sub,Complex.ofReal_one]
  ring

theorem band_bound (ε : ℝ) (hε : 0 < ε) (L S c : ℝ) (hLS : L ≤ S) (hc : 0 < c)
    (hw : ∀ s ∈ Set.Icc L S, c ≤ weight ε s) (f : Hilbert) :
    ‖lowProjection S f-lowProjection L f‖ ≤ (1/c)*‖weighted ε hε f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (lowProjection S f) (lowProjection L f),
    lowProjection_coe S f,lowProjection_coe L f,weighted_coe ε hε f] with x hs hS hL hW
  have hxpos := weight_positive ε hε x.1
  rw [hs,Pi.sub_apply,hS,hL,hW,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (weight_positive ε hε x.1)]
  by_cases hl : x.1 ≤ L
  · rw [if_pos hl,if_pos (hl.trans hLS),sub_self,norm_zero]
    positivity
  · rw [if_neg hl,sub_zero]
    by_cases hu : x.1 ≤ S
    · rw [if_pos hu]
      have hb := hw x.1 ⟨(lt_of_not_ge hl).le,hu⟩
      have hm : 1 ≤ (1/c)*weight ε x.1 := by rw [one_div,mul_comm,← div_eq_mul_inv]; exact (one_le_div hc).mpr hb
      simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right hm (norm_nonneg (f x))
    · rw [if_neg hu,norm_zero]
      positivity

theorem exists_defect_control (ε : ℝ) (hε : 0 < ε) (L S : ℝ) (hLS : L ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Hilbert,
      ‖defectOperator ε hε f‖ ≤ ‖lowProjection L f‖+C*‖weighted ε hε f‖+defect ε S*‖f‖ := by
  obtain ⟨s,_,hs⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hLS)
    (weight_continuous ε hε).continuousOn
  refine ⟨1/weight ε s,by positivity [weight_positive ε hε s],fun f => ?_⟩
  have hb := band_bound ε hε L S (weight ε s) hLS (weight_positive ε hε s) hs f
  have ht : ‖lowProjection S f‖ ≤ ‖lowProjection L f‖+‖lowProjection S f-lowProjection L f‖ :=
    (norm_add_le (lowProjection L f) (lowProjection S f-lowProjection L f)).trans_eq' (by rw [add_sub_cancel])
  have hd := KFCausalClockFloorSharpEscapeCriterion.defect_cutoff_bound ε hε S f
  linarith only [hb,ht,hd]

#print axioms weight_positive
#print axioms weight_continuous
#print axioms weighted_coe
#print axioms band_bound
#print axioms exists_defect_control
end
end UnifiedTheory.Audit.KFCausalClockFloorWeightedClockControl
