/- Each physical initial state has uniformly small sufficiently negative
clock tails for all forward times. This does not assert positive-clock
escape or vanishing clock defect. -/
import UnifiedTheory.Audit.KFCausalClockFloorLeftBarrierEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorLeftTightness
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorLeftBarrier
open UnifiedTheory.Audit.KFCausalClockFloorLeftBarrierEvolution
open UnifiedTheory.Audit.KFCausalClockFloorDefectLocalization (lowProjection)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution

variable (ε : ℝ) (hε : 0 < ε)

theorem expectation_tendsto_zero (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hz : Tendsto b atTop (𝓝 0)) (f : Hilbert) :
    Tendsto (fun n => (inner ℂ f (barrier ε hε (b n) (hb n) f)).re)
      atTop (𝓝 0) := by
  have hi := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖^2)
    (fun n => ((Complex.measurable_re.comp (weight_measurable ε (b n))).aestronglyMeasurable).mul
      ((Lp.aestronglyMeasurable f).norm.pow 2))
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f))
    (fun n => by
      filter_upwards [] with x
      change ‖weight ε (b n) x*‖f x‖^2‖ ≤ ‖f x‖^2
      rw [Real.norm_eq_abs,abs_of_nonneg
        (mul_nonneg (weight_bounds ε hε (b n) (hb n) x).1.le (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) (weight_bounds ε hε (b n) (hb n) x).2)
    (show ∀ᵐ x ∂volume, Tendsto (fun n => weight ε (b n) x*‖f x‖^2)
        atTop (𝓝 (0:ℝ)) from by
      filter_upwards [] with x
      have hd := (tendsto_const_nhds.add hz : Tendsto
        (fun n => 1-(KFCausalClockFloorCanonicalDefect.defect ε x.1)^2+b n)
        atTop (𝓝 (1-(KFCausalClockFloorCanonicalDefect.defect ε x.1)^2+0)))
      have hw := hz.div hd (by simpa only [add_zero] using (gap_positive ε hε x.1).ne')
      simpa only [weight,zero_div,zero_mul] using hw.mul_const (‖f x‖^2))
  simpa only [expectation_integral,Complex.ofReal_re,integral_zero] using hi

theorem exists_small_barrier (f : Hilbert) (η : ℝ) (hη : 0 < η) :
    ∃ b : ℝ, ∃ hb : 0 < b, (inner ℂ f (barrier ε hε b hb f)).re < η := by
  let b : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hb : ∀ n, 0 < b n := fun n => by dsimp [b]; positivity
  have hz := expectation_tendsto_zero ε hε b hb tendsto_one_div_add_atTop_nhds_zero_nat f
  obtain ⟨n,hn⟩ := (hz.eventually (gt_mem_nhds hη)).exists
  exact ⟨b n,hb n,hn⟩

theorem uniform_left_tail (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
    (m g k s : ℝ) (f : Hilbert) (η : ℝ) (hη : 0 < η) :
    ∃ S : ℝ, ∀ t, s ≤ t →
      ‖lowProjection S (evolution ε hε h hne hh m g k s t f)‖^2 < η := by
  obtain ⟨b,hb,hsmall⟩ := exists_small_barrier ε hε f (η/2) (by positivity)
  let S := Real.log (b*ε/2)
  have hS : 2*Real.exp S ≤ b*ε := by
    dsimp [S]
    rw [Real.exp_log (by positivity : 0 < b*ε/2)]
    linarith
  refine ⟨S,fun t ht => ?_⟩
  have he := low_probability_le_initial_barrier ε hε h hne hh m g k b hb S hS s t ht f
  linarith

#print axioms expectation_tendsto_zero
#print axioms exists_small_barrier
#print axioms uniform_left_tail
end
end UnifiedTheory.Audit.KFCausalClockFloorLeftTightness
