/- The unique constructed full matter trajectories, with their evolution
law. Continuity in initial data is established separately. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterCompleteRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterEvolution
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalMatterODE
open UnifiedTheory.Audit.KFCausalClassicalMatterGlobal
open UnifiedTheory.Audit.KFCausalClassicalMatterCompleteRecovery
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (TimePhase q)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)

variable (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)

def evolve (t : ℝ) (x : TimePhase) : TimePhase :=
  (exists_global ε m g κ hε hm hg hκ x).choose t

theorem evolve_zero (x : TimePhase) : evolve ε m g κ hε hm hg hκ 0 x = x :=
  (exists_global ε m g κ hε hm hg hκ x).choose_spec.1

theorem evolve_derivative (x : TimePhase) (t : ℝ) :
    HasDerivAt (fun u => evolve ε m g κ hε hm hg hκ u x)
      (field ε m g κ (evolve ε m g κ hε hm hg hκ t x)) t :=
  (exists_global ε m g κ hε hm hg hκ x).choose_spec.2 t

theorem evolve_continuous_time (x : TimePhase) :
    Continuous (fun t => evolve ε m g κ hε hm hg hκ t x) :=
  continuous_iff_continuousAt.mpr (fun t => (evolve_derivative ε m g κ hε hm hg hκ x t).continuousAt)

theorem evolve_add (s t : ℝ) (x : TimePhase) :
    evolve ε m g κ hε hm hg hκ (s+t) x =
      evolve ε m g κ hε hm hg hκ s (evolve ε m g κ hε hm hg hκ t x) := by
  let η : ℝ → TimePhase := fun u => evolve ε m g κ hε hm hg hκ (u+t) x
  have hd (u : ℝ) : HasDerivAt η (field ε m g κ (η u)) u := by
    simpa only [η,Function.comp_def,one_smul] using
      (evolve_derivative ε m g κ hε hm hg hκ x (u+t)).scomp u ((hasDerivAt_id u).add_const t)
  have he := global_unique ε m g κ hε.le η
    (fun u => evolve ε m g κ hε hm hg hκ u (evolve ε m g κ hε hm hg hκ t x))
    hd (evolve_derivative ε m g κ hε hm hg hκ _) (by simp only [η,zero_add,evolve_zero])
  exact congrFun he s

theorem evolve_time (x : TimePhase) (t : ℝ) :
    (evolve ε m g κ hε hm hg hκ t x).1 = t+x.1 := by
  have h := trajectory_time ε m g κ
    (fun u => evolve ε m g κ hε hm hg hκ u x)
    (evolve_derivative ε m g κ hε hm hg hκ x) t
  simpa only [evolve_zero] using h

theorem evolve_recovery (x : TimePhase) :
    Tendsto (fun t => q (.inr 0) (evolve ε m g κ hε hm hg hκ t x).2) atTop atTop ∧
      Tendsto (fun t => defect ε (q (.inr 0) (evolve ε m g κ hε hm hg hκ t x).2)) atTop (𝓝 0) :=
  global_recovery ε m g κ hε hm hg hκ
    (fun t => evolve ε m g κ hε hm hg hκ t x) (evolve_derivative ε m g κ hε hm hg hκ x)

#print axioms evolve_zero
#print axioms evolve_derivative
#print axioms evolve_continuous_time
#print axioms evolve_add
#print axioms evolve_time
#print axioms evolve_recovery

end
end UnifiedTheory.Audit.KFCausalClassicalMatterEvolution

