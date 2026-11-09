/- Strict clock-defect decrease and a nonnegative future limit on constructed
global matter trajectories. This does not identify that limit with zero. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterGlobal
import UnifiedTheory.Audit.KFCausalClassicalMatterDefect
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterGlobalDecay
noncomputable section
open Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalMatterODE
open UnifiedTheory.Audit.KFCausalClassicalMatterGlobal
open UnifiedTheory.Audit.KFCausalClassicalMatterDefect
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q TimePhase)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect defect_positive)

theorem defect_strictAnti (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g)
    (hκ : 0 < κ) (γ : ℝ → TimePhase)
    (hγ : ∀ t, HasDerivAt γ (field ε m g κ (γ t)) t) :
    StrictAnti (fun t => defect ε (q (.inr 0) (γ t).2)) := by
  intro a b hab
  exact defect_strictAntiOn ε m g κ hε hm hg hκ γ a b (fun t _ => hγ t)
    ⟨le_rfl,hab.le⟩ ⟨hab.le,le_rfl⟩ hab

theorem defect_limit (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g)
    (hκ : 0 < κ) (γ : ℝ → TimePhase)
    (hγ : ∀ t, HasDerivAt γ (field ε m g κ (γ t)) t) :
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧ (∀ t, ℓ < defect ε (q (.inr 0) (γ t).2)) ∧
      Tendsto (fun t => defect ε (q (.inr 0) (γ t).2)) atTop (𝓝 ℓ) := by
  let F : ℝ → ℝ := fun t => defect ε (q (.inr 0) (γ t).2)
  have hs : StrictAnti F := defect_strictAnti ε m g κ hε hm hg hκ γ hγ
  have h0 (t : ℝ) : 0 ≤ F t := (defect_positive ε _ hε).le
  have hbd : BddBelow (range F) := ⟨0,by rintro _ ⟨t,rfl⟩; exact h0 t⟩
  refine ⟨⨅ t, F t,le_ciInf h0,?_,tendsto_atTop_ciInf hs.antitone hbd⟩
  intro t
  exact (ciInf_le hbd (t+1)).trans_lt (hs (by linarith : t < t+1))

theorem exists_unique_global_decay (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m)
    (hg : 0 ≤ g) (hκ : 0 < κ) (x₀ : TimePhase) :
    ∃! γ : ℝ → TimePhase, γ 0 = x₀ ∧
      (∀ t, HasDerivAt γ (field ε m g κ (γ t)) t) ∧
      StrictAnti (fun t => defect ε (q (.inr 0) (γ t).2)) ∧
      ∃ ℓ : ℝ, 0 ≤ ℓ ∧ (∀ t, ℓ < defect ε (q (.inr 0) (γ t).2)) ∧
        Tendsto (fun t => defect ε (q (.inr 0) (γ t).2)) atTop (𝓝 ℓ) := by
  obtain ⟨γ,h₀,hγ⟩ := exists_global ε m g κ hε hm hg hκ x₀
  refine ⟨γ,⟨h₀,hγ,defect_strictAnti ε m g κ hε hm hg hκ γ hγ,
    defect_limit ε m g κ hε hm hg hκ γ hγ⟩,?_⟩
  intro η hη
  exact global_unique ε m g κ hε.le η γ hη.2.1 hγ (hη.1.trans h₀.symm)

#print axioms defect_strictAnti
#print axioms defect_limit
#print axioms exists_unique_global_decay

end
end UnifiedTheory.Audit.KFCausalClassicalMatterGlobalDecay
