/- An unbounded left-clock moment is propagated by the actual dynamics.
The initial integrability condition is explicit; none is imposed on the
evolved state. Bounded inverse-order barriers and Fatou give the result. -/
import UnifiedTheory.Audit.KFCausalClockFloorLeftBarrierEvolution
import UnifiedTheory.Audit.KFCausalPureMomentumCutoffDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorInverseGapMoment
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorLeftBarrier
open UnifiedTheory.Audit.KFCausalClockFloorLeftBarrierEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution)

def density (ε : ℝ) (f : Hilbert) (x : Configuration) : ℝ :=
  (1-(defect ε x.1)^2)⁻¹*‖f x‖^2

def moment (ε : ℝ) (f : Hilbert) : ℝ := ∫ x, density ε f x

def cutoffDensity (ε b : ℝ) (f : Hilbert) (x : Configuration) : ℝ :=
  (1-(defect ε x.1)^2+b)⁻¹*‖f x‖^2

theorem cutoff_integrable (ε : ℝ) (hε : 0 < ε) (b : ℝ) (hb : 0 < b) (f : Hilbert) :
    Integrable (cutoffDensity ε b f) := by
  have hi := (L2.integrable_inner (𝕜 := ℂ) f (barrier ε hε b hb f)).re.const_mul b⁻¹
  apply hi.congr
  filter_upwards [barrier_coe ε hε b hb f] with x hx
  rw [hx]
  change b⁻¹*(inner ℂ (f x) ((weight ε b x:ℂ) • f x)).re = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change b⁻¹*((weight ε b x:ℂ)*(‖f x‖:ℂ)^2).re = _
  rw [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]
  unfold cutoffDensity weight
  field_simp

theorem cutoff_expectation (ε : ℝ) (hε : 0 < ε) (b : ℝ) (hb : 0 < b) (f : Hilbert) :
    (∫ x, cutoffDensity ε b f x) = b⁻¹*(inner ℂ f (barrier ε hε b hb f)).re := by
  rw [expectation_integral,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold cutoffDensity weight
  field_simp

theorem cutoff_le (ε : ℝ) (hε : 0 < ε) (b : ℝ) (hb : 0 < b) (f : Hilbert)
    (x : Configuration) : 0 ≤ cutoffDensity ε b f x ∧ cutoffDensity ε b f x ≤ density ε f x := by
  have hp := gap_positive ε hε x.1
  constructor
  · exact mul_nonneg (inv_nonneg.mpr (by linarith)) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right (inv_anti₀ hp (by linarith)) (sq_nonneg _)

theorem cutoff_limit (ε : ℝ) (hε : 0 < ε) (b : ℕ → ℝ)
    (hz : Tendsto b atTop (𝓝 0)) (f : Hilbert) (x : Configuration) :
    Tendsto (fun n => cutoffDensity ε (b n) f x) atTop (𝓝 (density ε f x)) := by
  have he := ((tendsto_const_nhds.add hz).inv₀
    (show 1-(defect ε x.1)^2+0 ≠ 0 by simpa only [add_zero] using (gap_positive ε hε x.1).ne')).mul_const (‖f x‖^2)
  simpa only [add_zero,cutoffDensity,density] using he

theorem moment_integrable_after (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
    (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s t : ℝ) (hst : s ≤ t)
    (f : Hilbert) (hf : Integrable (density ε f)) :
    Integrable (density ε (evolution ε hε h hne hh m g k s t f)) ∧
      moment ε (evolution ε hε h hne hh m g k s t f) ≤ moment ε f := by
  let u := evolution ε hε h hne hh m g k s t f
  let b : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hb (n : ℕ) : 0 < b n := by dsimp only [b]; positivity
  have hz : Tendsto b atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hm (n : ℕ) : (∫ x, cutoffDensity ε (b n) u x) ≤ moment ε f := by
    rw [cutoff_expectation ε hε _ (hb n),moment]
    have he := mul_le_mul_of_nonneg_left
      (expectation_le_initial ε hε h hne hh m g k (b n) (hb n) s t hst f)
      (inv_nonneg.mpr (hb n).le)
    exact he.trans (((cutoff_expectation ε hε _ (hb n) f).symm).trans_le
      (integral_mono (cutoff_integrable ε hε _ (hb n) f) hf
      (fun x => (cutoff_le ε hε _ (hb n) f x).2)))
  have hmeas : AEStronglyMeasurable (density ε u) volume := by
    have hc : Measurable (fun x : Configuration => (1-(defect ε x.1)^2)⁻¹) := by
      unfold defect KFCausalClockFloorFlow.clock
      fun_prop
    exact hc.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable u).norm.pow 2)
  have hi : Integrable (density ε u) :=
    KFCausalPureMomentumCutoffDomain.integrable_of_uniform_nonnegative_integrals
      (fun n => cutoffDensity ε (b n) u) (density ε u)
      (fun n => cutoff_integrable ε hε _ (hb n) u)
      (fun n x => (cutoff_le ε hε _ (hb n) u x).1) hmeas
      (fun x => mul_nonneg (inv_nonneg.mpr (gap_positive ε hε x.1).le) (sq_nonneg _))
      (cutoff_limit ε hε b hz u) (moment ε f) hm
  refine ⟨hi,?_⟩
  apply le_of_tendsto (tendsto_integral_of_dominated_convergence (density ε u)
    (fun n => (cutoff_integrable ε hε _ (hb n) u).aestronglyMeasurable) hi
    (fun n => Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (cutoff_le ε hε _ (hb n) u x).1]
      exact (cutoff_le ε hε _ (hb n) u x).2))
    (Eventually.of_forall (cutoff_limit ε hε b hz u)))
  exact Eventually.of_forall hm

#print axioms cutoff_integrable
#print axioms cutoff_expectation
#print axioms cutoff_le
#print axioms cutoff_limit
#print axioms moment_integrable_after
end
end UnifiedTheory.Audit.KFCausalClockFloorInverseGapMoment
