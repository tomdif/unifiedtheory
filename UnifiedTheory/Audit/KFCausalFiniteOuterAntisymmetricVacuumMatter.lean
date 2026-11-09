/- The original finite sourced family admits the six antisymmetric
kinetic-after-vacuum-or-matter graphs, including primitive projected graphs. -/
import UnifiedTheory.Audit.KFCausalOuterAntisymmetricVacuumMatter
import UnifiedTheory.Audit.KFCausalFiniteSourcedMixedVacuum
import UnifiedTheory.Audit.KFCausalTwoAngleOperatorGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalFiniteOuterAntisymmetricVacuumMatter
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (action)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalReciprocalNeutralSuperposition (state)
open KFCausalFiniteSourcedMixedVacuum (widthCap width_le_cap action_state)
open KFCausalAntisymmetricKineticGraphAssembly (kineticSecond)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorAntisymmetricGraph (antiIndex)
open KFCausalStandingChargeOperator (zeroProjection)
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
  KFCausalOuterAntisymmetricVacuumMatter.secondOutput ε h (a t) W (w t) (C t) (p t) (b t) (P t)
    hε hh (ha t) (hw t) (hW t) hb i j θ

def forwardOutput (i : Option (Fin 2)) (j : Fin 2) (θ : ℝ) : Hilbert := ∑ t,
  KFCausalOuterAntisymmetricVacuumMatter.forwardOutput ε h (a t) W (w t) (C t) (p t) (b t) (P t)
    hε hh (ha t) (hw t) (hW t) hb i j θ

def projectedForward (i : Option (Fin 2)) (j : Fin 2) : Hilbert := ∑ t,
  KFCausalOuterAntisymmetricVacuumMatter.projectedForward ε h (a t) W (w t) (C t) (p t) (b t) (P t)
    hε hh (ha t) (hw t) (hW t) hb i j

def projectedOutput (i : Option (Fin 2)) (j : Fin 2) : Hilbert := ∑ t,
  KFCausalOuterAntisymmetricVacuumMatter.projectedOutput ε h (a t) W (w t) (C t) (p t) (b t) (P t)
    hε hh (ha t) (hw t) (hW t) hb i j

variable (i : Option (Fin 2)) (j : Fin 2)
local notation "u" => firstOutput n ε h a w p C b P hε ha hh hw hb i
local notation "v" => secondOutput n ε h a w p C b P hε ha hh hw hb i j
local notation "T" => innerSecond ε h hε i
local notation "S" => kineticSecond ε hε h j

theorem first_graph : (ψ,u) ∈ (T).graph := by
  have hs := (T).graph.sum_mem
    (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalVacuumMatterInput.inner_graph ε h (a t) (w t) (C t) (p t) (b t) (P t)
        hε hh (ha t) (hw t) hb i)
  simpa only [← prod_mk_sum,state,firstOutput,KFCausalSourcedWidthSecondInput.state] using hs

theorem forward_graph (θ : ℝ) :
    (action h hh θ u,forwardOutput n ε h a w p C b P hε ha hh hw hb i j θ) ∈
      (energyFactor ε hε h modelDirections pointField (antiIndex j)).graph := by
  have hs := (energyFactor ε hε h modelDirections pointField (antiIndex j)).graph.sum_mem
    (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalOuterAntisymmetricVacuumMatter.forward_graph ε h (a t) W (w t)
        (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) (hW t) hb i j θ)
  simpa only [← prod_mk_sum,firstOutput,forwardOutput,map_sum] using hs

theorem reverse_graph (θ : ℝ) :
    (forwardOutput n ε h a w p C b P hε ha hh hw hb i j θ,v θ) ∈
      (reverseFactor ε hε h modelDirections pointField (antiIndex j)).graph := by
  have hs := (reverseFactor ε hε h modelDirections pointField (antiIndex j)).graph.sum_mem
    (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalOuterAntisymmetricVacuumMatter.reverse_graph ε h (a t) W (w t)
        (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) (hW t) hb i j θ)
  simpa only [← prod_mk_sum,forwardOutput,secondOutput] using hs

theorem mixed_graph (θ : ℝ) : (action h hh θ u,v θ) ∈ (S).graph := by
  have hs := (S).graph.sum_mem
    (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalOuterAntisymmetricVacuumMatter.mixed_graph ε h (a t) W (w t) (C t) (p t) (b t) (P t)
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
  exact KFCausalOuterAntisymmetricVacuumMatter.secondOutput_continuous
    ε h (a t) W (w t) (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) (hW t) hb i j

theorem projected_forward_graph :
    (zeroProjection h hh u,projectedForward n ε h a w p C b P hε ha hh hw hb i j) ∈
      (energyFactor ε hε h modelDirections pointField (antiIndex j)).graph := by
  have hs := (energyFactor ε hε h modelDirections pointField (antiIndex j)).graph.sum_mem
    (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalOuterAntisymmetricVacuumMatter.projected_forward_graph ε h (a t) W (w t)
        (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) (hW t) hb i j)
  simpa only [← prod_mk_sum,firstOutput,projectedForward,map_sum] using hs

theorem projected_reverse_graph :
    (projectedForward n ε h a w p C b P hε ha hh hw hb i j,
      projectedOutput n ε h a w p C b P hε ha hh hw hb i j) ∈
      (reverseFactor ε hε h modelDirections pointField (antiIndex j)).graph := by
  have hs := (reverseFactor ε hε h modelDirections pointField (antiIndex j)).graph.sum_mem
    (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalOuterAntisymmetricVacuumMatter.projected_reverse_graph ε h (a t) W (w t)
        (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) (hW t) hb i j)
  simpa only [← prod_mk_sum,projectedForward,projectedOutput] using hs

theorem projected_graph :
    (zeroProjection h hh u,projectedOutput n ε h a w p C b P hε ha hh hw hb i j) ∈ (S).graph := by
  have hs := (S).graph.sum_mem
    (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalOuterAntisymmetricVacuumMatter.projected_graph ε h (a t) W (w t)
        (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) (hW t) hb i j)
  simpa only [← prod_mk_sum,firstOutput,projectedOutput,map_sum] using hs

theorem projected_domain : zeroProjection h hh u ∈ (S).domain :=
  LinearPMap.mem_domain_of_mem_graph (projected_graph n ε h a w p C b P hε ha hh hw hb i j)

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
#print axioms forward_graph
#print axioms reverse_graph
#print axioms mixed_graph
#print axioms mixed_domain
#print axioms ordered_graph
#print axioms ordered_domain
#print axioms secondOutput_continuous
#print axioms projected_forward_graph
#print axioms projected_reverse_graph
#print axioms projected_graph
#print axioms projected_domain
#print axioms two_angle_graph
#print axioms two_angle_domain
end
end UnifiedTheory.Audit.KFCausalFiniteOuterAntisymmetricVacuumMatter
