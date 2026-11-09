/- Continuous dependence of the constructed full matter trajectories,
uniformly on bounded initial sets and finite time windows. This defines an
actual continuous flow to use in probability-law transport. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterInitialBounds
import UnifiedTheory.Audit.KFCausalClassicalMatterEvolution
import UnifiedTheory.Audit.KFCausalODEWindowStability
import Mathlib.Dynamics.Flow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterFlow
noncomputable section
open Set Metric
open scoped Topology NNReal
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (TimePhase)
open UnifiedTheory.Audit.KFCausalClassicalMatterODE
open UnifiedTheory.Audit.KFCausalClassicalMatterEvolution

variable (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)
local notation "Φ" => evolve ε m g κ hε hm hg hκ

theorem evolve_window_bound (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : TimePhase, ‖x‖ ≤ R →
      ∀ t ∈ Icc (-T) T, ‖Φ t x‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := KFCausalClassicalMatterInitialBounds.bounded_initial_window
    ε m g κ hε hm hg hκ R T hR hT
  refine ⟨B,hB,?_⟩
  intro x hx
  exact hbound (fun t => Φ t x) (by simpa only [evolve_zero] using hx)
    (fun t _ => evolve_derivative ε m g κ hε hm hg hκ x t)

theorem evolve_window_lipschitz (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T) :
    ∃ L : ℝ≥0, ∀ t ∈ Icc (-T) T,
      LipschitzOnWith L (Φ t) (closedBall (0 : TimePhase) R) := by
  obtain ⟨B,_,hbound⟩ := evolve_window_bound ε m g κ hε hm hg hκ R T hR hT
  obtain ⟨K,hK⟩ := (field_contDiff ε m g κ hε.le).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall (0 : TimePhase) B) (isCompact_closedBall _ _)
  refine ⟨⟨Real.exp ((K:ℝ)*T),(Real.exp_pos _).le⟩,?_⟩
  intro t ht
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hx' : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hy' : ‖y‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hy
  have h := KFCausalODEWindowStability.distance_window (field ε m g κ) K (closedBall 0 B)
    hK T hT (fun u => Φ u x) (fun u => Φ u y)
    (fun u _ => evolve_derivative ε m g κ hε hm hg hκ x u)
    (fun u _ => evolve_derivative ε m g κ hε hm hg hκ y u)
    (fun u hu => by simpa only [mem_closedBall,dist_zero_right] using hbound x hx' u hu)
    (fun u hu => by simpa only [mem_closedBall,dist_zero_right] using hbound y hy' u hu) t ht
  simpa only [evolve_zero,mul_comm,NNReal.coe_mk] using h

theorem evolve_continuous : Continuous (fun tx : ℝ × TimePhase => Φ tx.1 tx.2) := by
  have hs : Continuous (fun xt : TimePhase × ℝ => Φ xt.2 xt.1) := by
    apply continuous_iff_continuousAt.mpr
    rintro ⟨x,t⟩
    let R := ‖x‖+1
    let T := |t|+1
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have hT : 0 ≤ T := by dsimp [T]; positivity
    obtain ⟨L,hL⟩ := evolve_window_lipschitz ε m g κ hε hm hg hκ R T hR hT
    have hc := continuousOn_prod_of_continuousOn_lipschitzOnWith
      (fun xt : TimePhase × ℝ => Φ xt.2 xt.1) (s := closedBall 0 R) (t := Icc (-T) T) L
      (fun y _ => (evolve_continuous_time ε m g κ hε hm hg hκ y).continuousOn) hL
    apply hc.continuousAt
    apply prod_mem_nhds
    · apply closedBall_mem_nhds_of_mem
      change dist x 0 < ‖x‖+1
      rw [dist_zero_right]
      linarith
    · apply Icc_mem_nhds
      · dsimp [T]
        linarith [neg_abs_le t]
      · dsimp [T]
        linarith [le_abs_self t]
  exact hs.comp continuous_swap

def flow : Flow ℝ TimePhase where
  toFun := Φ
  cont' := evolve_continuous ε m g κ hε hm hg hκ
  map_add' := evolve_add ε m g κ hε hm hg hκ
  map_zero' := evolve_zero ε m g κ hε hm hg hκ

#print axioms evolve_window_bound
#print axioms evolve_window_lipschitz
#print axioms evolve_continuous
#print axioms flow

end
end UnifiedTheory.Audit.KFCausalClassicalMatterFlow

