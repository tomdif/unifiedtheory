/- Projected actual outer matter graphs for the original finite sourced
families, preserving each primitive forward and reverse factor graph. -/
import UnifiedTheory.Audit.KFCausalOuterMatterProjected
import UnifiedTheory.Audit.KFCausalFiniteOuterMatterSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalFiniteOuterMatterProjected
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalFiniteSourcedMixedVacuum (widthCap width_le_cap)
open KFCausalFiniteOuterMatterSquare (firstOutput)
open KFCausalSourcedWidthMatterSquare (matterSecond)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalReciprocalNeutralMatterSpectral (matterIndex)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ t, 0 < a t)
  (hh : h ≠ 0) (hw : ∀ t, 1 ≤ w t) (hb : |h| ≤ ε/10)
  (i : Option (Fin 2)) (j : Fin 2)
local notation "W" => widthCap n w
local notation "hW" => width_le_cap n w hw
local notation "u" => firstOutput n ε h a w p C b P hε ha hh hw hb i

def projectedForward : Hilbert := ∑ t,
  KFCausalOuterMatterProjected.projectedForward ε h (a t) W (w t) (C t) (p t) (b t) (P t)
    hε hh (ha t) (hw t) (hW t) hb i j

def projectedOutput : Hilbert := ∑ t,
  KFCausalOuterMatterProjected.projectedOutput ε h (a t) W (w t) (C t) (p t) (b t) (P t)
    hε hh (ha t) (hw t) (hW t) hb i j

theorem projected_forward_graph :
    (zeroProjection h hh u,projectedForward n ε h a w p C b P hε ha hh hw hb i j) ∈
      (energyFactor ε hε h modelDirections pointField (matterIndex j)).graph := by
  have hs := (energyFactor ε hε h modelDirections pointField (matterIndex j)).graph.sum_mem
    (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalOuterMatterProjected.projected_forward_graph ε h (a t) W (w t)
        (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) (hW t) hb i j)
  simpa only [← prod_mk_sum,firstOutput,projectedForward,map_sum] using hs

theorem projected_reverse_graph :
    (projectedForward n ε h a w p C b P hε ha hh hw hb i j,
      projectedOutput n ε h a w p C b P hε ha hh hw hb i j) ∈
      (reverseFactor ε hε h modelDirections pointField (matterIndex j)).graph := by
  have hs := (reverseFactor ε hε h modelDirections pointField (matterIndex j)).graph.sum_mem
    (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalOuterMatterProjected.projected_reverse_graph ε h (a t) W (w t)
        (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) (hW t) hb i j)
  simpa only [← prod_mk_sum,projectedForward,projectedOutput] using hs

theorem projected_matter_graph :
    (zeroProjection h hh u,projectedOutput n ε h a w p C b P hε ha hh hw hb i j) ∈
      (matterSecond ε h j hε).graph := by
  have hs := (matterSecond ε h j hε).graph.sum_mem
    (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalOuterMatterProjected.projected_matter_graph ε h (a t) W (w t)
        (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) (hW t) hb i j)
  simpa only [← prod_mk_sum,firstOutput,projectedOutput,map_sum] using hs

theorem projected_matter_domain : zeroProjection h hh u ∈ (matterSecond ε h j hε).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (projected_matter_graph n ε h a w p C b P hε ha hh hw hb i j)

#print axioms projected_forward_graph
#print axioms projected_reverse_graph
#print axioms projected_matter_graph
#print axioms projected_matter_domain
end
end UnifiedTheory.Audit.KFCausalFiniteOuterMatterProjected
