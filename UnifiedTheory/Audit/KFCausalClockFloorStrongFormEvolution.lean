/- Sharp time-local energy bounds and strong continuity in the actual
completed energy-form space. The energy bound is passed through the
constructed weak cutoff limit; no form-norm convergence is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
import UnifiedTheory.Audit.KFCausalWeakEnergyContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSmoothedTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedCountableLimit
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalWeakLimitTransport
open UnifiedTheory.Audit.KFCausalWeakEnergyContinuity

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "V₀" => FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0
local notation "J" => embedding ε hε hbar hh hbound mass2 quartic vacuum 0
local notation "E" => timeEnergy ε hε hbar hh hbound mass2 quartic vacuum
local notation "F" => formFlow ε hε hbar hh hbound mass2 quartic vacuum
local notation "T" => formTransfer ε hε hbar hh hbound mass2 quartic vacuum

theorem weak_trajectory_energy_bound (s t : ℝ) (w : V₀)
    (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w) :
    E t (V.formState t) ≤ Real.exp (2*|t-s|)*E s w := by
  let u : ℕ → V₀ := fun n => smoothedLift ε hε hbar hh hbound mass2 quartic vacuum
    (cutoff (V.subsequence n)) (cutoff_pos (V.subsequence n)) s t (J w)
  have hC : 0 ≤ ‖J w‖^2 + Real.exp (2*|t-s|)*E s w :=
    add_nonneg (sq_nonneg _) (mul_nonneg (Real.exp_pos _).le
      (timeEnergy_nonneg ε hε hbar hh hbound mass2 quartic vacuum s w))
  have hb (n : ℕ) : ‖J (u n)‖^2+E t (u n) ≤ ‖J w‖^2+Real.exp (2*|t-s|)*E s w := by
    have hp := KFCausalClockFloorAveragedFormWindowBound.smoothedState_norm_le
      ε hε hbar hh hbound mass2 quartic vacuum (cutoff (V.subsequence n))
      (cutoff_pos (V.subsequence n)) s t (J w)
    have hn : ‖J (u n)‖^2 ≤ ‖J w‖^2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
    exact add_le_add hn (smoothed_uniform_form_bound ε hε hbar hh hbound mass2 quartic vacuum
      (cutoff (V.subsequence n)) (cutoff_pos (V.subsequence n)) s t w)
  have hn := weak_output_energy_le (T 0 t) (fun v : V₀ => ‖J v‖^2+E t v)
    (transported_form_norm ε hε hbar hh hbound mass2 quartic vacuum t)
    (u := u) (x := V.formState t) hC hb (V.formConvergence t)
  have hp := KFCausalClockFloorAveragedWeakNormConservation.physical_norm_initial
    ε hε hbar hh hbound mass2 quartic vacuum s w V t
  have he : ‖J w‖^2+E t (V.formState t) ≤ ‖J w‖^2+Real.exp (2*|t-s|)*E s w :=
    (congrArg (fun a : ℝ => a^2+E t (V.formState t)) hp.symm).le.trans hn
  linarith only [he]

theorem formFlow_energy_bound (s t : ℝ) (w : V₀) :
    E t (F s t w) ≤ Real.exp (2*|t-s|)*E s w :=
  weak_trajectory_energy_bound ε hε hbar hh hbound mass2 quartic vacuum s t w
    (weakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)

theorem timeEnergy_distance_comparison (s t : ℝ) (u : V₀) :
    E s u ≤ Real.exp (2*|t-s|)*E t u := by
  rcases le_total s t with hst | hts
  · have he := (timeEnergy_comparison ε hε hbar hh hbound mass2 quartic vacuum s t hst u).1
    exact he.trans (le_mul_of_one_le_left (timeEnergy_nonneg ε hε hbar hh hbound mass2 quartic vacuum t u)
      (Real.one_le_exp (by positivity)))
  · have he := (timeEnergy_comparison ε hε hbar hh hbound mass2 quartic vacuum t s hts u).2
    simpa only [abs_of_nonpos (sub_nonpos.mpr hts),neg_sub] using he

theorem formFlow_local_norm_bound (r t : ℝ) (w : V₀) :
    ‖T 0 r (F r t w)‖^2 ≤ ‖J w‖^2 + Real.exp (4*|t-r|)*E r w := by
  have hn : ‖T 0 r (F r t w)‖^2 = ‖J w‖^2+E r (F r t w) :=
    (transported_form_norm ε hε hbar hh hbound mass2 quartic vacuum r (F r t w)).trans
      (congrArg (fun a : ℝ => a^2+E r (F r t w))
        (formFlow_physical_norm ε hε hbar hh hbound mass2 quartic vacuum r t w))
  have he := (timeEnergy_distance_comparison ε hε hbar hh hbound mass2 quartic vacuum r t (F r t w)).trans
    (mul_le_mul_of_nonneg_left (formFlow_energy_bound ε hε hbar hh hbound mass2 quartic vacuum r t w)
      (Real.exp_pos _).le)
  have hexp : Real.exp (2*|t-r|)*(Real.exp (2*|t-r|)*E r w) = Real.exp (4*|t-r|)*E r w := by
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  exact hn.le.trans (add_le_add le_rfl (he.trans hexp.le))

theorem formFlow_continuous (s : ℝ) (w : V₀) : Continuous (fun t => F s t w) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  let x := F s r w
  have hw (y : FormSpace ε hε hbar hh hbound mass2 quartic vacuum r) :
      Tendsto (fun t => inner ℂ (T 0 r (F s t w)) y) (𝓝 r)
        (𝓝 (inner ℂ (T 0 r x) y)) := by
    simpa only [ContinuousLinearMap.adjoint_inner_right] using
      (formState_weakly_continuous ε hε hbar hh hbound mass2 quartic vacuum s w
        (weakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)
        ((T 0 r).adjoint y)).tendsto r
  have hb (t : ℝ) : ‖T 0 r (F s t w)‖^2 ≤ ‖J x‖^2 + Real.exp (4*|t-r|)*E r x := by
    have hn := formFlow_local_norm_bound ε hε hbar hh hbound mass2 quartic vacuum r t x
    simpa only [x,formFlow_compose] using hn
  have hB : Tendsto (fun t : ℝ => ‖J x‖^2+Real.exp (4*|t-r|)*E r x)
      (𝓝 r) (𝓝 (‖T 0 r x‖^2)) := by
    have hc : Continuous (fun t : ℝ => ‖J x‖^2+Real.exp (4*|t-r|)*E r x) := by fun_prop
    simpa only [sub_self,abs_zero,mul_zero,Real.exp_zero,one_mul,transported_form_norm]
      using hc.tendsto r
  have ht := (T r 0).continuous.tendsto (T 0 r x) |>.comp (strong_of_weak_sq_bound hw hb hB)
  simpa only [Function.comp_def,transfer_inverse] using ht

#print axioms weak_trajectory_energy_bound
#print axioms formFlow_energy_bound
#print axioms timeEnergy_distance_comparison
#print axioms formFlow_local_norm_bound
#print axioms formFlow_continuous

end
end UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
