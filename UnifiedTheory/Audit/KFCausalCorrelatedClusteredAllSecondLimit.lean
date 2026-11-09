/- All eight natural second actions on the physical clustered state
and its actual clock momentum, with convergence of the original finite
outputs. No matter coupling or polynomial degree is discarded. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMatterSecondLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumMatterSecondLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockSecondLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredVacuumSecondLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredAllSecondLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalGaussianVacuumSquare (original_strip)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb

def inputSeconds : Fin 8 → Hilbert :=
  ![KFCausalCorrelatedClusteredClockSecondLimit.inputSecond f ε h a p hε hh ha,
    KFCausalCorrelatedClusteredPhysicalKineticSeconds.inputSecond f ε h a p hε hh ha 0,
    KFCausalCorrelatedClusteredPhysicalKineticSeconds.inputSecond f ε h a p hε hh ha 1,
    KFCausalCorrelatedClusteredPhysicalKineticSeconds.inputSecond f ε h a p hε hh ha 2,
    KFCausalCorrelatedClusteredPhysicalKineticSeconds.inputSecond f ε h a p hε hh ha 3,
    KFCausalCorrelatedClusteredMatterSecondLimit.second f ε h a p hε hh ha hb 0,
    KFCausalCorrelatedClusteredMatterSecondLimit.second f ε h a p hε hh ha hb 1,
    KFCausalCorrelatedClusteredVacuumSecondLimit.inputSecond f ε h a p hε hh ha hb]

theorem input_reverse_graph (j : Fin 8) :
    (KFCausalCorrelatedClusteredAllFactorLimit.output f ε h a p hε hh hb₀ ha j,
      inputSeconds f ε h a p hε hh ha hb j) ∈
        (reverseFactor ε hε h modelDirections pointField j).graph := by
  fin_cases j
  · exact KFCausalCorrelatedClusteredClockSecondLimit.input_reverse_graph f ε h a p hε hh ha hb
  · exact KFCausalCorrelatedClusteredPhysicalKineticSeconds.input_reverse_graph f ε h a p hε hh ha 0
  · exact KFCausalCorrelatedClusteredPhysicalKineticSeconds.input_reverse_graph f ε h a p hε hh ha 1
  · exact KFCausalCorrelatedClusteredPhysicalKineticSeconds.input_reverse_graph f ε h a p hε hh ha 2
  · exact KFCausalCorrelatedClusteredPhysicalKineticSeconds.input_reverse_graph f ε h a p hε hh ha 3
  · exact KFCausalCorrelatedClusteredMatterSecondLimit.reverse_graph f ε h a p hε hh ha hb 0
  · exact KFCausalCorrelatedClusteredMatterSecondLimit.reverse_graph f ε h a p hε hh ha hb 1
  · exact KFCausalCorrelatedClusteredVacuumSecondLimit.input_reverse_graph f ε h a p hε hh ha hb

theorem inputSeconds_tendsto (j : Fin 8) :
    Tendsto (fun δ => KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteSeconds f ε h a p hε hh ha hb δ j)
      (𝓝[>] 0) (𝓝 (inputSeconds f ε h a p hε hh ha hb j)) := by
  fin_cases j
  · exact KFCausalCorrelatedClusteredClockSecondLimit.inputSecond_tendsto f ε h a p hε hh ha hb
  · exact KFCausalCorrelatedClusteredOriginalKineticSeconds.inputSecond_tendsto f ε h a p hε hh ha hb 0
  · exact KFCausalCorrelatedClusteredOriginalKineticSeconds.inputSecond_tendsto f ε h a p hε hh ha hb 1
  · exact KFCausalCorrelatedClusteredOriginalKineticSeconds.inputSecond_tendsto f ε h a p hε hh ha hb 2
  · exact KFCausalCorrelatedClusteredOriginalKineticSeconds.inputSecond_tendsto f ε h a p hε hh ha hb 3
  · exact KFCausalCorrelatedClusteredMatterSecondLimit.original_second_tendsto f ε h a p hε hh ha hb 0
  · exact KFCausalCorrelatedClusteredMatterSecondLimit.original_second_tendsto f ε h a p hε hh ha hb 1
  · exact KFCausalCorrelatedClusteredVacuumSecondLimit.inputSecond_tendsto f ε h a p hε hh ha hb

def momentumSeconds : Fin 8 → Hilbert :=
  ![KFCausalCorrelatedClusteredClockSecondLimit.momentumSecond f ε h a p hε hh ha,
    KFCausalCorrelatedClusteredPhysicalKineticSeconds.momentumSecond f ε h a p hε hh ha 0,
    KFCausalCorrelatedClusteredPhysicalKineticSeconds.momentumSecond f ε h a p hε hh ha 1,
    KFCausalCorrelatedClusteredPhysicalKineticSeconds.momentumSecond f ε h a p hε hh ha 2,
    KFCausalCorrelatedClusteredPhysicalKineticSeconds.momentumSecond f ε h a p hε hh ha 3,
    KFCausalCorrelatedClusteredMomentumMatterSecondLimit.second f ε h a p hε hh ha hb 0,
    KFCausalCorrelatedClusteredMomentumMatterSecondLimit.second f ε h a p hε hh ha hb 1,
    KFCausalCorrelatedClusteredVacuumSecondLimit.momentumSecond f ε h a p hε hh ha hb]

theorem momentum_reverse_graph (j : Fin 8) :
    (KFCausalCorrelatedClusteredAllFactorLimit.momentumOutput f ε h a p hε hh hb₀ ha j,
      momentumSeconds f ε h a p hε hh ha hb j) ∈
        (reverseFactor ε hε h modelDirections pointField j).graph := by
  fin_cases j
  · exact KFCausalCorrelatedClusteredClockSecondLimit.momentum_reverse_graph f ε h a p hε hh ha hb
  · exact KFCausalCorrelatedClusteredPhysicalKineticSeconds.momentum_reverse_graph f ε h a p hε hh ha 0
  · exact KFCausalCorrelatedClusteredPhysicalKineticSeconds.momentum_reverse_graph f ε h a p hε hh ha 1
  · exact KFCausalCorrelatedClusteredPhysicalKineticSeconds.momentum_reverse_graph f ε h a p hε hh ha 2
  · exact KFCausalCorrelatedClusteredPhysicalKineticSeconds.momentum_reverse_graph f ε h a p hε hh ha 3
  · exact KFCausalCorrelatedClusteredMomentumMatterSecondLimit.reverse_graph f ε h a p hε hh ha hb 0
  · exact KFCausalCorrelatedClusteredMomentumMatterSecondLimit.reverse_graph f ε h a p hε hh ha hb 1
  · exact KFCausalCorrelatedClusteredVacuumSecondLimit.momentum_reverse_graph f ε h a p hε hh ha hb

theorem momentumSeconds_tendsto (j : Fin 8) :
    Tendsto (fun δ => KFCausalCorrelatedClusteredOriginalKineticSeconds.finiteMomentumSeconds f ε h a p hε hh ha hb δ j)
      (𝓝[>] 0) (𝓝 (momentumSeconds f ε h a p hε hh ha hb j)) := by
  fin_cases j
  · exact KFCausalCorrelatedClusteredClockSecondLimit.momentumSecond_tendsto f ε h a p hε hh ha hb
  · exact KFCausalCorrelatedClusteredOriginalKineticSeconds.momentumSecond_tendsto f ε h a p hε hh ha hb 0
  · exact KFCausalCorrelatedClusteredOriginalKineticSeconds.momentumSecond_tendsto f ε h a p hε hh ha hb 1
  · exact KFCausalCorrelatedClusteredOriginalKineticSeconds.momentumSecond_tendsto f ε h a p hε hh ha hb 2
  · exact KFCausalCorrelatedClusteredOriginalKineticSeconds.momentumSecond_tendsto f ε h a p hε hh ha hb 3
  · exact KFCausalCorrelatedClusteredMomentumMatterSecondLimit.original_second_tendsto f ε h a p hε hh ha hb 0
  · exact KFCausalCorrelatedClusteredMomentumMatterSecondLimit.original_second_tendsto f ε h a p hε hh ha hb 1
  · exact KFCausalCorrelatedClusteredVacuumSecondLimit.momentumSecond_tendsto f ε h a p hε hh ha hb

#print axioms input_reverse_graph
#print axioms momentum_reverse_graph
#print axioms inputSeconds_tendsto
#print axioms momentumSeconds_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredAllSecondLimit
