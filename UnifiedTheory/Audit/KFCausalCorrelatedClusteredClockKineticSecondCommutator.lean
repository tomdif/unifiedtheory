/- The five clock/kinetic second-output derivatives have exact bounded
commutator corrections, uniformly over the full correlated family. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockKineticSecondPureLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockKineticSecondCommutator
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredAllSecondLimit (inputSeconds momentumSeconds)
open KFCausalCorrelatedClusteredClockKineticSecondPureLimit
open KFCausalCorrelatedClusteredFiniteSecondPureClock (finiteDerivative)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorPureClockKinetic (correction)

def lowIndex (j : Fin 5) : Fin 8 := Fin.castAdd 3 j

theorem double_correction_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (g : Hilbert) :
    ‖correction ε hε h g+correction ε hε h g‖ ≤ (|h|/(4*ε))*‖g‖ := by
  calc
    _ ≤ ‖correction ε hε h g‖+‖correction ε hε h g‖ := norm_add_le _ _
    _ ≤ (|h|/(8*ε))*‖g‖+(|h|/(8*ε))*‖g‖ := add_le_add
      (KFCausalClockFloorPureClockKineticResponse.correction_bound ε hε h g)
      (KFCausalClockFloorPureClockKineticResponse.correction_bound ε hε h g)
    _ = _ := by ring

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "B" => pureMomentum ε hε h
local notation "K" => correction ε hε h
local notation "L" => inputSeconds f ε h a p hε hh ha hb
local notation "M" => momentumSeconds f ε h a p hε hh ha hb

def derivative : Fin 5 → Hilbert :=
  ![clockDerivative f ε h a p hε hh ha hb,
    kineticDerivative f ε h a p hε hh ha hb 0,kineticDerivative f ε h a p hε hh ha hb 1,
    kineticDerivative f ε h a p hε hh ha hb 2,kineticDerivative f ε h a p hε hh ha hb 3]

theorem derivative_graph (j : Fin 5) : (L (lowIndex j),derivative f ε h a p hε hh ha hb j) ∈ (B).graph := by
  fin_cases j
  · exact clock_derivative_graph f ε h a p hε hh ha hb
  · exact kinetic_derivative_graph f ε h a p hε hh ha hb 0
  · exact kinetic_derivative_graph f ε h a p hε hh ha hb 1
  · exact kinetic_derivative_graph f ε h a p hε hh ha hb 2
  · exact kinetic_derivative_graph f ε h a p hε hh ha hb 3

theorem derivative_domain (j : Fin 5) : L (lowIndex j) ∈ (B).domain :=
  LinearPMap.mem_domain_of_mem_graph (derivative_graph f ε h a p hε hh ha hb j)

theorem derivative_tendsto (j : Fin 5) :
    Tendsto (fun δ => finiteDerivative f ε h a p hε hh ha hb δ (lowIndex j)) (𝓝[>] 0)
      (𝓝 (derivative f ε h a p hε hh ha hb j)) := by
  fin_cases j
  · exact clock_derivative_tendsto f ε h a p hε hh ha hb
  · exact kinetic_derivative_tendsto f ε h a p hε hh ha hb 0
  · exact kinetic_derivative_tendsto f ε h a p hε hh ha hb 1
  · exact kinetic_derivative_tendsto f ε h a p hε hh ha hb 2
  · exact kinetic_derivative_tendsto f ε h a p hε hh ha hb 3

theorem derivative_difference (j : Fin 5) :
    derivative f ε h a p hε hh ha hb j-M (lowIndex j) =
      (if j=0 then (-1:ℂ) else 1) • (K (L (lowIndex j))+K (L (lowIndex j))) := by
  fin_cases j
  · change (M 0-K (L 0)-K (L 0))-M 0=(-1:ℂ) • (K (L 0)+K (L 0))
    rw [neg_one_smul]
    abel
  · change (M 1+K (L 1)+K (L 1))-M 1=(1:ℂ) • (K (L 1)+K (L 1))
    rw [one_smul]
    abel
  · change (M 2+K (L 2)+K (L 2))-M 2=(1:ℂ) • (K (L 2)+K (L 2))
    rw [one_smul]
    abel
  · change (M 3+K (L 3)+K (L 3))-M 3=(1:ℂ) • (K (L 3)+K (L 3))
    rw [one_smul]
    abel
  · change (M 4+K (L 4)+K (L 4))-M 4=(1:ℂ) • (K (L 4)+K (L 4))
    rw [one_smul]
    abel

theorem derivative_correction_bound (j : Fin 5) :
    ‖derivative f ε h a p hε hh ha hb j-M (lowIndex j)‖ ≤ (|h|/(4*ε))*‖L (lowIndex j)‖ := by
  rw [derivative_difference,norm_smul]
  have hc : ‖(if j=0 then (-1:ℂ) else 1)‖=1 := by split_ifs <;> norm_num
  rw [hc,one_mul]
  exact double_correction_bound ε hε h (L (lowIndex j))

#print axioms double_correction_bound
#print axioms derivative_graph
#print axioms derivative_domain
#print axioms derivative_tendsto
#print axioms derivative_difference
#print axioms derivative_correction_bound
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockKineticSecondCommutator
