/- Finite original sourced families admit Q U(theta) L Q and Q P0 L Q
for each symmetric charged position. Graph sums retain cancellation. -/
import UnifiedTheory.Audit.KFCausalSourcedWidthSymmetricProjected
import UnifiedTheory.Audit.KFCausalFiniteSourcedFirstField

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalFiniteSourcedSymmetricSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (action)
open KFCausalClockFloorVacuumSquare (square)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalPhysicalField (physicalField)
open KFCausalPhysicalSpectatorGraph (symmetricPosition)
open KFCausalSingleGaussianMixedSquare (original_strip)
open KFCausalReciprocalNeutralSuperposition (state)
open KFCausalFiniteSourcedMixedVacuum (widthCap width_le_cap firstOutput first_graph)
open KFCausalFiniteSourcedFirstField (fieldOutput first_field_graph field_after_square_graph)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (j : Fin 2) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
local notation "ψ" => state n ε h a w p C b P hε ha hh hw
local notation "u" => fieldOutput n ε h a w p C b P hε ha hh hw hb (symmetricPosition j)
local notation "W" => widthCap n w
local notation "hW" => width_le_cap n w hw

def secondOutput (θ : ℝ) : Hilbert := ∑ i,
  KFCausalSourcedWidthSymmetricSquare.secondOutput ε h (a i) W (w i) (C i) (p i) (b i) (P i) j
    hε hh (ha i) (hw i) (hW i) hb θ

def projectedOutput : Hilbert := ∑ i,
  KFCausalSourcedWidthSymmetricProjected.projectedOutput ε h (a i) W (w i) (C i) (p i) (b i) (P i) j
    hε hh (ha i) (hw i) (hW i) hb

local notation "v" => secondOutput n ε h a w p C b P j hε ha hh hw hb
local notation "z" => projectedOutput n ε h a w p C b P j hε ha hh hw hb

theorem mixed_graph (θ : ℝ) : (action h hh θ u,v θ) ∈ (square ε hε h).graph := by
  have hs := (square ε hε h).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalSourcedWidthSymmetricSquare.mixed_square_graph ε h (a i) W (w i) (C i) (p i) (b i) (P i) j
        hε hh (ha i) (hw i) (hW i) hb θ)
  simpa only [← prod_mk_sum,fieldOutput,secondOutput,map_sum] using hs

theorem mixed_domain (θ : ℝ) : action h hh θ u ∈ (square ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (mixed_graph n ε h a w p C b P j hε ha hh hw hb θ)

theorem projected_graph : (zeroProjection h hh u,z) ∈ (square ε hε h).graph := by
  have hs := (square ε hε h).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalSourcedWidthSymmetricProjected.projected_square_graph ε h (a i) W (w i) (C i) (p i) (b i) (P i) j
        hε hh (ha i) (hw i) (hW i) hb)
  simpa only [← prod_mk_sum,fieldOutput,projectedOutput,map_sum] using hs

theorem projected_domain : zeroProjection h hh u ∈ (square ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (projected_graph n ε h a w p C b P j hε ha hh hw hb)

theorem square_field_square_graph :
    (ψ,v 0) ∈ (composition (square ε hε h)
      (composition (physicalField (symmetricPosition j)) (square ε hε h))).graph := by
  apply (composition_graph _ _ _ _).mpr
  refine ⟨u,field_after_square_graph n ε h a w p C b P hε ha hh hw hb (symmetricPosition j),?_⟩
  simpa only [KFCausalPhysicalCircleAction.action_zero] using
    mixed_graph n ε h a w p C b P j hε ha hh hw hb 0

include hb in
theorem square_field_square_domain :
    ψ ∈ (composition (square ε hε h)
      (composition (physicalField (symmetricPosition j)) (square ε hε h))).domain :=
  LinearPMap.mem_domain_of_mem_graph (square_field_square_graph n ε h a w p C b P j hε ha hh hw hb)

theorem secondOutput_continuous : Continuous v := by
  apply continuous_finset_sum
  intro i _
  exact KFCausalSourcedWidthSymmetricContinuity.secondOutput_continuous
    ε h (a i) W (w i) (C i) (p i) (b i) (P i) j hε hh (ha i) (hw i) (hW i) hb

theorem three_actual_graphs (θ : ℝ) :
    (ψ,firstOutput n ε h a w p C b P hε ha hh hw hb) ∈ (square ε hε h).graph ∧
      (firstOutput n ε h a w p C b P hε ha hh hw hb,u) ∈ (physicalField (symmetricPosition j)).graph ∧
      (action h hh θ u,v θ) ∈ (square ε hε h).graph :=
  ⟨first_graph n ε h a w p C b P hε ha hh hw hb,
    first_field_graph n ε h a w p C b P hε ha hh hw hb (symmetricPosition j),
    mixed_graph n ε h a w p C b P j hε ha hh hw hb θ⟩

#print axioms mixed_graph
#print axioms mixed_domain
#print axioms projected_graph
#print axioms projected_domain
#print axioms square_field_square_graph
#print axioms square_field_square_domain
#print axioms secondOutput_continuous
#print axioms three_actual_graphs
end
end UnifiedTheory.Audit.KFCausalFiniteSourcedSymmetricSquare
