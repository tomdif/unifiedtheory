/- Joint strong continuity of the constructed unbounded homogeneous
evolution in both times and the initial state. Operator-norm continuity
and classical differentiability for arbitrary L2 data are not claimed. -/
import UnifiedTheory.Audit.KFCausalRegularizedHomogeneousEvolution
import UnifiedTheory.Audit.KFCausalStrongUnitaryContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedHomogeneousContinuity
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedHomogeneousEvolution
open UnifiedTheory.Audit.KFCausalStrongUnitaryContinuity

theorem evolution_symm (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) :
    (evolution ε hε hbar coupling s t).symm = evolution ε hε hbar coupling t s := by
  apply LinearIsometryEquiv.ext
  intro f
  have hh := evolution_adjoint ε hε hbar coupling s t
  rw [LinearIsometryEquiv.adjoint_eq_symm] at hh
  exact congrArg (fun P : Hilbert →L[ℂ] Hilbert => P f) hh

theorem evolution_initial_time_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) (f : Hilbert) :
    Continuous (fun s => evolution ε hε hbar coupling s t f) := by
  have hh := inverse_strong_continuous (H := Hilbert) (fun s => evolution ε hε hbar coupling t s)
    (evolution_strong_continuous ε hε hbar coupling t) f
  simpa only [evolution_symm] using hh

theorem evolution_joint_strong_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ) (f : Hilbert) :
    Continuous (fun p : ℝ×ℝ => evolution ε hε hbar coupling p.1 p.2 f) := by
  have he := joint_evaluation_continuous (H := Hilbert) (fun t => evolution ε hε hbar coupling 0 t)
    (evolution_strong_continuous ε hε hbar coupling 0)
  have hi : Continuous (fun p : ℝ×ℝ => evolution ε hε hbar coupling p.1 0 f) :=
    (evolution_initial_time_continuous ε hε hbar coupling 0 f).comp continuous_fst
  have hh := he.comp (continuous_snd.prodMk hi)
  have hid (p : ℝ×ℝ) : evolution ε hε hbar coupling 0 p.2
      (evolution ε hε hbar coupling p.1 0 f) = evolution ε hε hbar coupling p.1 p.2 f := by
    exact congrArg (fun P : Hilbert →L[ℂ] Hilbert => P f)
      (evolution_compose ε hε hbar coupling p.1 0 p.2)
  simpa only [Function.comp_def,hid] using hh

theorem evolution_joint_state_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ) :
    Continuous (fun p : (ℝ×ℝ)×Hilbert => evolution ε hε hbar coupling p.1.1 p.1.2 p.2) := by
  have hh := joint_evaluation_continuous (H := Hilbert)
    (fun p : ℝ×ℝ => evolution ε hε hbar coupling p.1 p.2)
    (evolution_joint_strong_continuous ε hε hbar coupling)
  exact hh

#print axioms evolution_symm
#print axioms evolution_initial_time_continuous
#print axioms evolution_joint_strong_continuous
#print axioms evolution_joint_state_continuous

end
end UnifiedTheory.Audit.KFCausalRegularizedHomogeneousContinuity
