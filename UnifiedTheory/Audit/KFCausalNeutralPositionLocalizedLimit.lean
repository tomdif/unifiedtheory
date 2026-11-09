/- Removing the charged Gaussian localizer recovers the bare physical
neutral-position phase strongly on every fixed L2 vector. This is strong
L2 convergence only; no uniform graph bound or averaged-domain limit is
claimed as the localizer vanishes. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMatter
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMultiplier
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar scalar_norm)

def damping (δ : ℝ) (x : Configuration) : ℝ := Real.exp (-δ*(x.2 2+x.2 3)^2)

theorem damping_bounds (δ : ℝ) (hδ : 0 ≤ δ) (x : Configuration) : 0 ≤ damping δ x ∧ damping δ x ≤ 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) (sq_nonneg _)

theorem physicalPhase_damping (δ v : ℝ) (x : Configuration) :
    physicalPhase δ v x = (damping δ x:ℂ)*scalar (v*x.2 4) := by
  unfold physicalPhase damping
  rw [Complex.ofReal_exp]
  push_cast
  rfl

theorem norm_difference_square (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (h0 : |(0:ℝ)| ≤ Real.pi*ε/3) (f : Hilbert) :
    ‖action ε δ v hε hδ 0 h0 f-KFCausalNeutralPositionCharge.action v f‖^2 =
      ∫ x : Configuration, (damping δ x-1)^2*‖f x‖^2 := by
  rw [KFCausalAveragedEnergyGraph.l2_norm_square]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (action ε δ v hε hδ 0 h0 f) (KFCausalNeutralPositionCharge.action v f),
    action_zero_coe ε δ v hε hδ h0 f,KFCausalNeutralPositionCharge.action_coe v f] with x hs ha hb
  rw [hs]
  simp only [Pi.sub_apply,ha,hb,physicalPhase_damping]
  have he : (damping δ x:ℂ)*scalar (v*x.2 4)*f x-scalar (v*x.2 4)*f x =
      ((damping δ x-1:ℝ):ℂ)*scalar (v*x.2 4)*f x := by push_cast; ring
  rw [he]
  simp only [norm_mul,scalar_norm,mul_one,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem strong_limit (ε v : ℝ) (hε : 0 < ε) (h0 : |(0:ℝ)| ≤ Real.pi*ε/3)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hd : Tendsto δ atTop (𝓝 0)) (f : Hilbert) :
    Tendsto (fun n => action ε (δ n) v hε (hδ n) 0 h0 f) atTop
      (𝓝 (KFCausalNeutralPositionCharge.action v f)) := by
  have hI : Tendsto (fun n => ∫ x : Configuration, (damping (δ n) x-1)^2*‖f x‖^2)
      atTop (𝓝 (∫ _x : Configuration, (0:ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (fun x : Configuration => ‖f x‖^2)
    · intro n
      have hc : Continuous (fun x : Configuration => (damping (δ n) x-1)^2) := by unfold damping; fun_prop
      exact hc.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable f).norm.pow 2)
    · exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
    · intro n
      filter_upwards [] with x
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      apply mul_le_of_le_one_left (sq_nonneg _)
      have hb := damping_bounds (δ n) (hδ n).le x
      nlinarith [sq_nonneg (damping (δ n) x)]
    · filter_upwards [] with x
      have hc : Tendsto (fun n => damping (δ n) x) atTop (𝓝 1) := by
        have hp : Tendsto (fun n => -δ n*(x.2 2+x.2 3)^2) atTop (𝓝 0) := by
          simpa only [neg_zero,zero_mul] using (hd.neg).mul_const ((x.2 2+x.2 3)^2)
        simpa only [damping,Function.comp_def,Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hp
      simpa only [sub_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul]
        using ((hc.sub_const 1).pow 2).mul_const (‖f x‖^2)
  have hsq : Tendsto (fun n => ‖action ε (δ n) v hε (hδ n) 0 h0 f-KFCausalNeutralPositionCharge.action v f‖^2)
      atTop (𝓝 0) := by
    simpa only [norm_difference_square,integral_zero] using hI
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero]
    using (Real.continuous_sqrt.tendsto 0).comp hsq

#print axioms damping_bounds
#print axioms physicalPhase_damping
#print axioms norm_difference_square
#print axioms strong_limit

end
end UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedLimit
