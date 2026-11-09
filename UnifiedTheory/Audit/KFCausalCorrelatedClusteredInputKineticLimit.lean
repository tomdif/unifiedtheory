/- Identify the already constructed physical state with the generic
clock vector and close its four actual kinetic energy-factor graphs. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredKineticGraphs
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputGraphLimit
import UnifiedTheory.Audit.KFCausalCoherentFactorResponseBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputKineticLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredInputProfiles (finiteState finiteState_coe amplitudes inputAmplitude_continuous inputAmplitude_memLp)
open KFCausalCorrelatedClusteredInputGraphLimit (limitingState state_tendsto)
open KFCausalCorrelatedClusteredClockVectors (vector vector_coe limitingVector vector_tendsto)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorTrialMomentum (clockMomentum)
open KFCausalCoherentFactorResponseBounds (kineticIndex)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
local notation "c" => amplitudes ε a p
local notation "hc" => fun i => inputAmplitude_continuous ε (a i) (p i)
local notation "hc2" => fun i => inputAmplitude_memLp ε (a i) (p i) hε (ha i)

theorem finiteState_eq (δ : ℝ) (hδ : 0 < δ) :
    finiteState f ε h a p hε hh ha δ = vector f c α β hα hβ hw hc2 δ :=
  Lp.ext ((finiteState_coe f ε h a p hε hh ha δ hδ).trans
    (vector_coe f c α β hα hβ hw hc2 δ hδ).symm)

theorem limitingState_eq : limitingState f ε h a p hε hh ha = limitingVector f c α β hα hβ hw hc2 hc := by
  apply tendsto_nhds_unique (state_tendsto f ε h a p hε hh ha)
  apply Tendsto.congr' _ (vector_tendsto f c α β hα hβ hw hc2 hc)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finiteState_eq f ε h a p hε hh ha δ hδ).symm

theorem energyFactor_kinetic (j : Fin 4) :
    energyFactor ε hε h modelDirections pointField (kineticIndex j) = clockMomentum ε h (modelDirections j) := by
  fin_cases j <;> rfl

def limitingOutput (j : Fin 4) : Hilbert :=
  KFCausalCorrelatedClusteredKineticGraphs.limitingOutput f c α β ε h hα hβ hε hc hc2 j

theorem limiting_graph (j : Fin 4) :
    (limitingState f ε h a p hε hh ha,limitingOutput f ε h a p hε hh ha j) ∈
      (energyFactor ε hε h modelDirections pointField (kineticIndex j)).graph := by
  rw [energyFactor_kinetic ε h hε j,limitingState_eq f ε h a p hε hh ha]
  exact KFCausalCorrelatedClusteredKineticGraphs.limiting_graph f c α β ε h hα hβ hw hε hc hc2 j

theorem limiting_domain (j : Fin 4) : limitingState f ε h a p hε hh ha ∈
    (energyFactor ε hε h modelDirections pointField (kineticIndex j)).domain :=
  LinearPMap.mem_domain_of_mem_graph (limiting_graph f ε h a p hε hh ha j)

variable (hb : |h| ≤ 2*Real.pi*ε/3)

theorem finiteOutput_eq (δ : ℝ) (hδ : 0 < δ) (j : Fin 4) :
    KFCausalCorrelatedClusteredPhysicalCauchy.finiteOutput f ε h a p hε hh hb ha δ (kineticIndex j) =
      KFCausalCorrelatedClusteredKineticGraphs.finiteOutput f c α β ε h hα hβ hε hc hc2 δ j := by
  have hg := KFCausalCorrelatedClusteredInputGraphLimit.finite_output_graph f ε h a p hε hh ha hb δ hδ (kineticIndex j)
  rw [energyFactor_kinetic ε h hε j,finiteState_eq f ε h a p hε hh ha δ hδ] at hg
  exact (clockMomentum ε h (modelDirections j)).mem_graph_snd_inj' hg
    (KFCausalCorrelatedClusteredKineticGraphs.finite_graph f c α β ε h hα hβ hw hε hc hc2 δ hδ j) rfl

theorem output_tendsto (j : Fin 4) :
    Tendsto (fun δ => KFCausalCorrelatedClusteredPhysicalCauchy.finiteOutput f ε h a p hε hh hb ha δ (kineticIndex j))
      (𝓝[>] 0) (𝓝 (limitingOutput f ε h a p hε hh ha j)) := by
  apply Tendsto.congr' _ (KFCausalCorrelatedClusteredKineticGraphs.output_tendsto f c α β ε h hα hβ hε hc hc2 j)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finiteOutput_eq f ε h a p hε hh ha hb δ hδ j).symm

theorem graph_tendsto (j : Fin 4) :
    Tendsto (fun δ => (finiteState f ε h a p hε hh ha δ,
      KFCausalCorrelatedClusteredPhysicalCauchy.finiteOutput f ε h a p hε hh hb ha δ (kineticIndex j)))
      (𝓝[>] 0) (𝓝 (limitingState f ε h a p hε hh ha,limitingOutput f ε h a p hε hh ha j)) :=
  (state_tendsto f ε h a p hε hh ha).prodMk_nhds (output_tendsto f ε h a p hε hh ha hb j)

#print axioms finiteState_eq
#print axioms limitingState_eq
#print axioms energyFactor_kinetic
#print axioms limiting_graph
#print axioms limiting_domain
#print axioms finiteOutput_eq
#print axioms output_tendsto
#print axioms graph_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputKineticLimit
