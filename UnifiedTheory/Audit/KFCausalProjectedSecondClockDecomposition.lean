/- Exact clock/kinetic and potential decomposition of the original
weighted second-output projection. Pure-clock graphs are preserved by
finite sums and the actual zero-charge projection. -/
import UnifiedTheory.Audit.KFCausalPureClockZeroProjection
import UnifiedTheory.Audit.KFCausalJointSecondPairing
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockKineticSecondCommutator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalProjectedSecondClockDecomposition
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalJointSecondPairing (secondWeighted)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalPureClockZeroProjection (projected_graph)
open KFCausalCorrelatedClusteredClockKineticSecondCommutator (lowIndex)

def highIndex (j : Fin 3) : Fin 8 := Fin.natAdd 5 j

variable (h : ℝ) (hh : h ≠ 0) (c : Fin 8 → ℂ)

def total (z : Fin 8 → Hilbert) : Hilbert := zeroProjection h hh (secondWeighted c z)
def low (z : Fin 8 → Hilbert) : Hilbert :=
  zeroProjection h hh (∑ j : Fin 5, (star (c (lowIndex j))*c (lowIndex j)) • z (lowIndex j))
def high (z : Fin 8 → Hilbert) : Hilbert :=
  zeroProjection h hh (∑ j : Fin 3, (star (c (highIndex j))*c (highIndex j)) • z (highIndex j))
def lowDerivative (d : Fin 5 → Hilbert) : Hilbert :=
  zeroProjection h hh (∑ j, (star (c (lowIndex j))*c (lowIndex j)) • d j)

theorem total_split (z : Fin 8 → Hilbert) : total h hh c z=low h hh c z+high h hh c z := by
  unfold total secondWeighted low high lowIndex highIndex
  rw [Fin.sum_univ_add (a := 5) (b := 3),map_add]

variable (ε : ℝ) (hε : 0 < ε)
local notation "B" => pureMomentum ε hε h

theorem total_graph (z d : Fin 8 → Hilbert) (hd : ∀ j, (z j,d j) ∈ (B).graph) :
    (total h hh c z,total h hh c d) ∈ (B).graph := by
  apply projected_graph ε hε h hh
  have hg := (B).graph.sum_mem (fun j (_ : j ∈ (Finset.univ : Finset (Fin 8))) =>
    (B).graph.smul_mem (star (c j)*c j) (hd j))
  simpa only [secondWeighted,Prod.smul_mk,← prod_mk_sum] using hg

theorem low_graph (z : Fin 8 → Hilbert) (d : Fin 5 → Hilbert)
    (hd : ∀ j, (z (lowIndex j),d j) ∈ (B).graph) :
    (low h hh c z,lowDerivative h hh c d) ∈ (B).graph := by
  apply projected_graph ε hε h hh
  have hg := (B).graph.sum_mem (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) =>
    (B).graph.smul_mem (star (c (lowIndex j))*c (lowIndex j)) (hd j))
  simpa only [Prod.smul_mk,← prod_mk_sum] using hg

theorem high_graph (z d : Fin 8 → Hilbert)
    (hd : ∀ j : Fin 3, (z (highIndex j),d (highIndex j)) ∈ (B).graph) :
    (high h hh c z,high h hh c d) ∈ (B).graph := by
  apply projected_graph ε hε h hh
  have hg := (B).graph.sum_mem (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    (B).graph.smul_mem (star (c (highIndex j))*c (highIndex j)) (hd j))
  simpa only [Prod.smul_mk,← prod_mk_sum] using hg

theorem total_domain_iff (z : Fin 8 → Hilbert) (hl : low h hh c z ∈ (B).domain) :
    total h hh c z ∈ (B).domain ↔ high h hh c z ∈ (B).domain := by
  rw [total_split]
  constructor
  · intro ht
    simpa only [add_sub_cancel_left] using (B).domain.sub_mem ht hl
  · intro ht
    exact (B).domain.add_mem hl ht

#print axioms total_split
#print axioms total_graph
#print axioms low_graph
#print axioms high_graph
#print axioms total_domain_iff
end
end UnifiedTheory.Audit.KFCausalProjectedSecondClockDecomposition
