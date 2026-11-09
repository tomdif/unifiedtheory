/- The original finite sourced state admits all six actual outer-matter
after-vacuum-or-matter graphs. Finite sums retain all packet interference. -/
import UnifiedTheory.Audit.KFCausalOuterMatterSquare
import UnifiedTheory.Audit.KFCausalFiniteSourcedMixedVacuum
import UnifiedTheory.Audit.KFCausalTwoAngleOperatorGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalFiniteOuterMatterSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (action)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalReciprocalNeutralSuperposition (state)
open KFCausalFiniteSourcedMixedVacuum (widthCap width_le_cap action_state)
open KFCausalSourcedWidthMatterSquare (matterSecond)
open KFCausalVacuumMatterInput (innerSecond innerOutput)
open KFCausalChargeConjugatedInsertion (operatorAt)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ t, 0 < a t)
  (hh : h ≠ 0) (hw : ∀ t, 1 ≤ w t) (hb : |h| ≤ ε/10)
local notation "ψ" => state n ε h a w p C b P hε ha hh hw
local notation "W" => widthCap n w
local notation "hW" => width_le_cap n w hw

def firstOutput (i : Option (Fin 2)) : Hilbert := ∑ t,
  innerOutput ε h (a t) (w t) (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) hb i

def secondOutput (i : Option (Fin 2)) (j : Fin 2) (θ : ℝ) : Hilbert := ∑ t,
  KFCausalOuterMatterSquare.secondOutput ε h (a t) W (w t) (C t) (p t) (b t) (P t)
    hε hh (ha t) (hw t) (hW t) hb i j θ

variable (i : Option (Fin 2)) (j : Fin 2)
local notation "u" => firstOutput n ε h a w p C b P hε ha hh hw hb i
local notation "v" => secondOutput n ε h a w p C b P hε ha hh hw hb i j
local notation "T" => innerSecond ε h hε i
local notation "S" => matterSecond ε h j hε

theorem first_graph : (ψ,u) ∈ (T).graph := by
  have hs := (T).graph.sum_mem
    (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalVacuumMatterInput.inner_graph ε h (a t) (w t) (C t) (p t) (b t) (P t)
        hε hh (ha t) (hw t) hb i)
  simpa only [← prod_mk_sum,state,firstOutput,KFCausalSourcedWidthSecondInput.state] using hs

theorem mixed_graph (θ : ℝ) : (action h hh θ u,v θ) ∈ (S).graph := by
  have hs := (S).graph.sum_mem
    (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalOuterMatterSquare.mixed_graph ε h (a t) W (w t) (C t) (p t) (b t) (P t)
        hε hh (ha t) (hw t) (hW t) hb i j θ)
  simpa only [← prod_mk_sum,firstOutput,secondOutput,map_sum] using hs

theorem mixed_domain (θ : ℝ) : action h hh θ u ∈ (S).domain :=
  LinearPMap.mem_domain_of_mem_graph (mixed_graph n ε h a w p C b P hε ha hh hw hb i j θ)

theorem ordered_graph : (ψ,v 0) ∈ (composition S T).graph := by
  apply (composition_graph _ _ _ _).mpr
  refine ⟨u,first_graph n ε h a w p C b P hε ha hh hw hb i,?_⟩
  simpa only [KFCausalPhysicalCircleAction.action_zero] using
    mixed_graph n ε h a w p C b P hε ha hh hw hb i j 0

include hb in
theorem ordered_domain : ψ ∈ (composition S T).domain :=
  LinearPMap.mem_domain_of_mem_graph (ordered_graph n ε h a w p C b P hε ha hh hw hb i j)

theorem secondOutput_continuous : Continuous v := by
  apply continuous_finset_sum
  intro t _
  exact KFCausalOuterMatterSquare.secondOutput_continuous
    ε h (a t) W (w t) (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) (hW t) hb i j

theorem two_angle_graph (θ φ : ℝ) :
    (ψ,action h hh (-φ) (v (φ-θ))) ∈
      (composition (operatorAt h hh S φ) (operatorAt h hh T θ)).graph :=
  KFCausalTwoAngleOperatorGraph.two_angle_graph h hh S T ψ u v
    (action_state n ε h a w p C b P hε ha hh hw)
    (first_graph n ε h a w p C b P hε ha hh hw hb i)
    (mixed_graph n ε h a w p C b P hε ha hh hw hb i j) θ φ

include hb in
theorem two_angle_domain (θ φ : ℝ) :
    ψ ∈ (composition (operatorAt h hh S φ) (operatorAt h hh T θ)).domain :=
  LinearPMap.mem_domain_of_mem_graph (two_angle_graph n ε h a w p C b P hε ha hh hw hb i j θ φ)

#print axioms first_graph
#print axioms mixed_graph
#print axioms mixed_domain
#print axioms ordered_graph
#print axioms ordered_domain
#print axioms secondOutput_continuous
#print axioms two_angle_graph
#print axioms two_angle_domain
end
end UnifiedTheory.Audit.KFCausalFiniteOuterMatterSquare
