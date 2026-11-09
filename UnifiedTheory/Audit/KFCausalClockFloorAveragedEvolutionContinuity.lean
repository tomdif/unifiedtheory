/- Joint strong continuity in both time endpoints of the actual
unbounded weak-form propagator. This is strong, not operator-norm,
continuity on the physical Hilbert space. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
import UnifiedTheory.Audit.KFCausalStrongIsometryContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionContinuity
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalStrongIsometryContinuity

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3)
  (mass2 quartic vacuum : ℝ)

theorem evolution_initial_time_continuous (t : ℝ) (f : Hilbert) :
    Continuous (fun s => evolution ε hε hbar hh hbound mass2 quartic vacuum s t f) := by
  have hc := inverse_strong_continuous
    (fun s => evolution ε hε hbar hh hbound mass2 quartic vacuum t s)
    (evolution_strong_continuous ε hε hbar hh hbound mass2 quartic vacuum t) f
  have hr (s : ℝ) : (evolution ε hε hbar hh hbound mass2 quartic vacuum t s).symm f =
      evolution ε hε hbar hh hbound mass2 quartic vacuum s t f := by
    have h := congrArg (fun P : Hilbert →L[ℂ] Hilbert => P f)
      (evolution_adjoint ε hε hbar hh hbound mass2 quartic vacuum t s)
    rw [LinearIsometryEquiv.adjoint_eq_symm] at h
    exact h
  simpa only [hr] using hc

theorem evolution_joint_strong_continuous (f : Hilbert) :
    Continuous (fun p : ℝ × ℝ => evolution ε hε hbar hh hbound mass2 quartic vacuum p.1 p.2 f) := by
  have hb := strong_joint_apply (fun t => evolution ε hε hbar hh hbound mass2 quartic vacuum 0 t)
    (evolution_strong_continuous ε hε hbar hh hbound mass2 quartic vacuum 0)
  have hp : Continuous (fun p : ℝ × ℝ => (p.2,evolution ε hε hbar hh hbound mass2 quartic vacuum p.1 0 f)) :=
    continuous_snd.prodMk ((evolution_initial_time_continuous ε hε hbar hh hbound mass2 quartic vacuum 0 f).comp continuous_fst)
  have hr (s t : ℝ) : evolution ε hε hbar hh hbound mass2 quartic vacuum 0 t
      (evolution ε hε hbar hh hbound mass2 quartic vacuum s 0 f) =
      evolution ε hε hbar hh hbound mass2 quartic vacuum s t f :=
    congrArg (fun P : Hilbert →L[ℂ] Hilbert => P f)
      (evolution_compose ε hε hbar hh hbound mass2 quartic vacuum s 0 t)
  simpa only [Function.comp_def,hr] using hb.comp hp

#print axioms evolution_initial_time_continuous
#print axioms evolution_joint_strong_continuous

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionContinuity
