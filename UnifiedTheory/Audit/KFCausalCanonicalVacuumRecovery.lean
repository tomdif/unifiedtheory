/- The full canonical vector field supplies the clock equations used in the
classical recovery theorem. No independent clock-force assumption is needed.
The global-trajectory hypothesis is still explicit. -/
import UnifiedTheory.Audit.KFCausalClassicalVacuumClockComponents

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalCanonicalVacuumRecovery
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE
open UnifiedTheory.Audit.KFCausalClassicalVacuumClockComponents
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)

theorem trajectory_time (ε κ : ℝ) (γ : ℝ → TimePhase)
    (hγ : ∀ t, HasDerivAt γ (field ε κ (γ t)) t) (t : ℝ) :
    (γ t).1 = t+(γ 0).1 := by
  have hd (u : ℝ) : HasDerivAt (fun v => (γ v).1-v) 0 u := by
    have hf : HasDerivAt (fun v => (γ v).1) 1 u := (hγ u).fst
    simpa only [sub_self] using hf.sub (hasDerivAt_id u)
  have h := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0
  change (γ t).1-t = (γ 0).1-0 at h
  linarith

theorem clock_derivative (ε κ : ℝ) (hε : 0 ≤ ε) (γ : ℝ → TimePhase) (t : ℝ)
    (hγ : HasDerivAt γ (field ε κ (γ t)) t) :
    HasDerivAt (fun u => q (.inr 0) (γ u).2)
      (clockRate ε κ (γ t).1 (γ t).2 (q (.inr 0) (γ t).2) (p (.inr 0) (γ t).2)) t := by
  have h : HasDerivAt (fun u => q (.inr 0) (γ u).2) (q (.inr 0) (field ε κ (γ t)).2) t :=
    (q (.inr 0)).hasFDerivAt.comp_hasDerivAt t hγ.snd
  simpa only [field_clock ε κ hε] using h

theorem clockMomentum_derivative (ε κ : ℝ) (hε : 0 ≤ ε) (γ : ℝ → TimePhase) (t : ℝ)
    (hγ : HasDerivAt γ (field ε κ (γ t)) t) :
    HasDerivAt (fun u => p (.inr 0) (γ u).2)
      (momentumRate ε κ (γ t).1 (γ t).2 (q (.inr 0) (γ t).2) (p (.inr 0) (γ t).2)) t := by
  have h : HasDerivAt (fun u => p (.inr 0) (γ u).2) (p (.inr 0) (field ε κ (γ t)).2) t :=
    (p (.inr 0)).hasFDerivAt.comp_hasDerivAt t hγ.snd
  simpa only [field_clockMomentum ε κ hε] using h

theorem global_defect_tendsto_zero (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ)
    (γ : ℝ → TimePhase) (h0 : (γ 0).1 = 0)
    (hγ : ∀ t, HasDerivAt γ (field ε κ (γ t)) t) :
    Tendsto (fun t => defect ε (q (.inr 0) (γ t).2)) atTop (𝓝 0) := by
  have ht (t : ℝ) : (γ t).1 = t := by rw [trajectory_time ε κ γ hγ t,h0,add_zero]
  apply KFCausalClassicalAveragedVacuumDecay.defect_tendsto_zero ε κ hε
    (fun t => (γ t).2) (fun t => q (.inr 0) (γ t).2) (fun t => p (.inr 0) (γ t).2)
  · intro t
    simpa only [ht] using clock_derivative ε κ hε.le γ t (hγ t)
  · intro t
    simpa only [ht] using clockMomentum_derivative ε κ hε.le γ t (hγ t)
  · exact hκ

#print axioms trajectory_time
#print axioms clock_derivative
#print axioms clockMomentum_derivative
#print axioms global_defect_tendsto_zero

end
end UnifiedTheory.Audit.KFCausalCanonicalVacuumRecovery
