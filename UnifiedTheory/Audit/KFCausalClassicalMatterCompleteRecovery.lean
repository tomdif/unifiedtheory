/- Complete classical matter recovery: a unique global trajectory is
constructed for every initial point, and its clock defect tends to zero.
This is a classical candidate theorem, not a quantum or physical TOE claim. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterRecovery
import UnifiedTheory.Audit.KFCausalClassicalMatterGlobalDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterCompleteRecovery
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalMatterODE
open UnifiedTheory.Audit.KFCausalClassicalMatterGlobal
open UnifiedTheory.Audit.KFCausalClassicalMatterGlobalDecay (defect_strictAnti)
open UnifiedTheory.Audit.KFCausalClassicalMatterDefect (clock_derivative clockMomentum_derivative)
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian (clockRate momentumRate)
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q p TimePhase)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)

theorem trajectory_time (ε m g κ : ℝ) (γ : ℝ → TimePhase)
    (hγ : ∀ t, HasDerivAt γ (field ε m g κ (γ t)) t) (t : ℝ) :
    (γ t).1 = t+(γ 0).1 := by
  have hd (u : ℝ) : HasDerivAt (fun v => (γ v).1-v) 0 u := by
    have hf : HasDerivAt (fun v => (γ v).1) 1 u := (hγ u).fst
    simpa only [sub_self] using hf.sub (hasDerivAt_id u)
  have h := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0
  change (γ t).1-t = (γ 0).1-0 at h
  linarith

theorem global_recovery (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g)
    (hκ : 0 < κ) (γ : ℝ → TimePhase)
    (hγ : ∀ t, HasDerivAt γ (field ε m g κ (γ t)) t) :
    Tendsto (fun t => q (.inr 0) (γ t).2) atTop atTop ∧
      Tendsto (fun t => defect ε (q (.inr 0) (γ t).2)) atTop (𝓝 0) := by
  have hs (t : ℝ) : HasDerivAt (fun u => q (.inr 0) (γ u).2)
      (clockRate ε m g κ (t+(γ 0).1) (γ t).2 (q (.inr 0) (γ t).2) (p (.inr 0) (γ t).2)) t := by
    have h := clock_derivative ε m g κ hε.le γ t (hγ t)
    rw [trajectory_time ε m g κ γ hγ t] at h
    exact h
  have hp (t : ℝ) : HasDerivAt (fun u => p (.inr 0) (γ u).2)
      (momentumRate ε m g κ (t+(γ 0).1) (γ t).2 (q (.inr 0) (γ t).2) (p (.inr 0) (γ t).2)) t := by
    have h := clockMomentum_derivative ε m g κ hε.le γ t (hγ t)
    rw [trajectory_time ε m g κ γ hγ t] at h
    exact h
  exact ⟨KFCausalClassicalMatterRecovery.logClock_tendsto_atTop ε m g κ (γ 0).1 hε hm hg hκ
      (fun t => (γ t).2) (fun t => q (.inr 0) (γ t).2) (fun t => p (.inr 0) (γ t).2) hs hp,
    KFCausalClassicalMatterRecovery.defect_tendsto_zero ε m g κ (γ 0).1 hε hm hg hκ
      (fun t => (γ t).2) (fun t => q (.inr 0) (γ t).2) (fun t => p (.inr 0) (γ t).2) hs hp⟩

theorem exists_unique_global_recovery (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m)
    (hg : 0 ≤ g) (hκ : 0 < κ) (x₀ : TimePhase) :
    ∃! γ : ℝ → TimePhase, γ 0 = x₀ ∧
      (∀ t, HasDerivAt γ (field ε m g κ (γ t)) t) ∧
      StrictAnti (fun t => defect ε (q (.inr 0) (γ t).2)) ∧
      Tendsto (fun t => q (.inr 0) (γ t).2) atTop atTop ∧
      Tendsto (fun t => defect ε (q (.inr 0) (γ t).2)) atTop (𝓝 0) := by
  obtain ⟨γ,h₀,hγ⟩ := exists_global ε m g κ hε hm hg hκ x₀
  refine ⟨γ,⟨h₀,hγ,defect_strictAnti ε m g κ hε hm hg hκ γ hγ,
    global_recovery ε m g κ hε hm hg hκ γ hγ⟩,?_⟩
  intro η hη
  exact global_unique ε m g κ hε.le η γ hη.2.1 hγ (hη.1.trans h₀.symm)

#print axioms trajectory_time
#print axioms global_recovery
#print axioms exists_unique_global_recovery

end
end UnifiedTheory.Audit.KFCausalClassicalMatterCompleteRecovery

