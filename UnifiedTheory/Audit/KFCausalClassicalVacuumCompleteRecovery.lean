/- Every initial state of the full classical vacuum candidate has a unique
all-real-time canonical trajectory, and its positive-floor clock defect tends
to zero in the future. Global existence is constructed, not assumed. -/
import UnifiedTheory.Audit.KFCausalClassicalVacuumGlobal
import UnifiedTheory.Audit.KFCausalCanonicalVacuumRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumCompleteRecovery
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE
open UnifiedTheory.Audit.KFCausalCanonicalVacuumRecovery
open UnifiedTheory.Audit.KFCausalClassicalVacuumGlobal
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)

theorem defect_tendsto_zero_anytime (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ)
    (γ : ℝ → TimePhase) (hγ : ∀ t, HasDerivAt γ (field ε κ (γ t)) t) :
    Tendsto (fun t => defect ε (q (.inr 0) (γ t).2)) atTop (𝓝 0) := by
  let a := (γ 0).1
  let η : ℝ → TimePhase := fun t => γ (t-a)
  have hη (t : ℝ) : HasDerivAt η (field ε κ (η t)) t := by
    simpa only [η,Function.comp_def,one_smul] using
      (hγ (t-a)).scomp t ((hasDerivAt_id t).sub_const a)
  have hη0 : (η 0).1 = 0 := by
    rw [show η 0 = γ (-a) by simp [η],trajectory_time ε κ γ hγ]
    dsimp [a]
    ring
  have hl := global_defect_tendsto_zero ε κ hε hκ η hη0 hη
  have ht : Tendsto (fun t : ℝ => t+a) atTop atTop := tendsto_atTop_add_const_right _ a tendsto_id
  simpa only [Function.comp_def,η,add_sub_cancel_right] using hl.comp ht

theorem exists_unique_global (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (x₀ : TimePhase) :
    ∃! γ : ℝ → TimePhase, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (field ε κ (γ t)) t := by
  obtain ⟨γ,h₀,hγ⟩ := exists_global ε κ hε hκ x₀
  refine ⟨γ,⟨h₀,hγ⟩,?_⟩
  intro η hη
  exact global_unique ε κ hε.le η γ hη.2 hγ (hη.1.trans h₀.symm)

theorem exists_unique_global_recovery (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (x₀ : TimePhase) :
    ∃! γ : ℝ → TimePhase, γ 0 = x₀ ∧
      (∀ t, HasDerivAt γ (field ε κ (γ t)) t) ∧
      Tendsto (fun t => defect ε (q (.inr 0) (γ t).2)) atTop (𝓝 0) := by
  obtain ⟨γ,h₀,hγ⟩ := exists_global ε κ hε hκ x₀
  refine ⟨γ,⟨h₀,hγ,defect_tendsto_zero_anytime ε κ hε hκ γ hγ⟩,?_⟩
  intro η hη
  exact global_unique ε κ hε.le η γ hη.2.1 hγ (hη.1.trans h₀.symm)

#print axioms defect_tendsto_zero_anytime
#print axioms exists_unique_global
#print axioms exists_unique_global_recovery

end
end UnifiedTheory.Audit.KFCausalClassicalVacuumCompleteRecovery
