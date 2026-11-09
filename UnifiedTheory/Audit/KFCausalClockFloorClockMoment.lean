/- The physical positive-clock moment is finite on the half-clock domain.
The bounded resolvents converge to that moment by dominated convergence. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockResolvent
import UnifiedTheory.Audit.KFCausalClockFloorClockHalf
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockMoment
noncomputable section
open MeasureTheory Filter
open scoped Topology ComplexConjugate
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorClockResolvent

def moment (ε : ℝ) (f : Hilbert) : ℝ := ∫ x, clock ε x.1*‖f x‖^2

variable (ε : ℝ) (hε : 0 < ε) (f y : Hilbert)
include hε

theorem density_eq (hy : (f,y) ∈ (clockHalf ε).graph) :
    (fun x => clock ε x.1*‖f x‖^2) =ᵐ[volume] fun x => ‖y x‖^2 := by
  filter_upwards [(clockHalf_graph ε f y).mp hy] with x hx
  rw [hx,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  simp only [halfWeight,Real.sq_sqrt (by positivity : 0 ≤ Real.exp x.1+ε),clock]

theorem moment_integrable (hy : (f,y) ∈ (clockHalf ε).graph) :
    Integrable (fun x => clock ε x.1*‖f x‖^2) volume :=
  ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable y)).mp (Lp.memLp y)).congr
    (density_eq ε hε f y hy).symm

theorem moment_eq_norm (hy : (f,y) ∈ (clockHalf ε).graph) : moment ε f = ‖y‖^2 := by
  unfold moment
  rw [integral_congr_ae (density_eq ε hε f y hy)]
  exact (KFCausalAveragedEnergyGraph.l2_norm_square volume y).symm

theorem expectation_tendsto (hy : (f,y) ∈ (clockHalf ε).graph)
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hz : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun n => (inner ℂ f (clockApprox ε hε (b n) (hb n) f)).re) atTop (𝓝 (moment ε f)) := by
  simp only [expectation_integral,moment]
  apply tendsto_integral_of_dominated_convergence (fun x => clock ε x.1*‖f x‖^2)
  · intro n
    have hm : Measurable (weight ε (b n)) := by
      unfold weight KFCausalClockFloorCanonicalDefect.defect clock
      fun_prop
    exact hm.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable f).norm.pow 2)
  · exact moment_integrable ε hε f y hy
  · intro n
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (weight_positive ε hε (b n) (hb n) x).le (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (weight_bound ε hε (b n) (hb n) x) (sq_nonneg _))
  · exact Filter.Eventually.of_forall (fun x => (weight_tendsto ε hε b atTop hz x).mul_const _)

theorem expectation_real (b : ℝ) (hb : 0 < b) :
    inner ℂ f (clockApprox ε hε b hb f) = ((inner ℂ f (clockApprox ε hε b hb f)).re:ℂ) := by
  have hc := clockApprox_dual ε hε b hb f f
  have hs := inner_conj_symm (𝕜 := ℂ) f (clockApprox ε hε b hb f)
  rw [hc] at hs
  apply Complex.ext
  · rfl
  · have hi := congrArg Complex.im hs
    simp only [Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

theorem complex_expectation_tendsto (hy : (f,y) ∈ (clockHalf ε).graph)
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hz : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun n => inner ℂ f (clockApprox ε hε (b n) (hb n) f)) atTop (𝓝 (moment ε f:ℂ)) := by
  have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp (expectation_tendsto ε hε f y hy b hb hz)
  change Tendsto (fun n => ((inner ℂ f (clockApprox ε hε (b n) (hb n) f)).re:ℂ))
    atTop (𝓝 (moment ε f:ℂ)) at ht
  simpa only [← expectation_real ε hε f] using ht

#print axioms density_eq
#print axioms moment_integrable
#print axioms moment_eq_norm
#print axioms expectation_tendsto
#print axioms expectation_real
#print axioms complex_expectation_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorClockMoment
