/- The actual clock momentum of the physical limiting state lies in
all four kinetic-factor domains, with the original finite outputs
converging strongly to the identified operator actions. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputKineticLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumPotentialProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumKineticLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredPureMomentumLimit (finiteMomentum finiteMomentum_eq limitingMomentum momentum_tendsto)
open KFCausalCorrelatedClusteredMomentumAmplitudes (amplitudes amplitude_continuous amplitude_memLp)
open KFCausalCorrelatedClusteredInputKineticLimit (energyFactor_kinetic)
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
local notation "hc" => fun i => amplitude_continuous ε (a i) (p i) hε
local notation "hc2" => fun i => amplitude_memLp ε (a i) (p i) hε (ha i)
local notation "s" => -Complex.I*(h:ℂ)

def limitingOutput (j : Fin 4) : Hilbert := s •
  KFCausalCorrelatedClusteredKineticGraphs.limitingOutput f c α β ε h hα hβ hε hc hc2 j

theorem limiting_graph (j : Fin 4) :
    (limitingMomentum f ε h a p hε hh ha,limitingOutput f ε h a p hε hh ha j) ∈
      (energyFactor ε hε h modelDirections pointField (kineticIndex j)).graph := by
  rw [energyFactor_kinetic ε h hε j]
  exact (clockMomentum ε h (modelDirections j)).graph.smul_mem s
    (KFCausalCorrelatedClusteredKineticGraphs.limiting_graph f c α β ε h hα hβ hw hε hc hc2 j)

theorem limiting_domain (j : Fin 4) : limitingMomentum f ε h a p hε hh ha ∈
    (energyFactor ε hε h modelDirections pointField (kineticIndex j)).domain :=
  LinearPMap.mem_domain_of_mem_graph (limiting_graph f ε h a p hε hh ha j)

variable (hb : |h| ≤ 2*Real.pi*ε/3)

theorem finiteOutput_eq (δ : ℝ) (hδ : 0 < δ) (j : Fin 4) :
    KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput f ε h a p hε hh hb ha δ (kineticIndex j) =
      s • KFCausalCorrelatedClusteredKineticGraphs.finiteOutput f c α β ε h hα hβ hε hc hc2 δ j := by
  have hg := KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput_graph f ε h a p hε hh hb ha δ hδ (kineticIndex j)
  rw [energyFactor_kinetic ε h hε j,finiteMomentum_eq f ε h a p hε hh ha δ hδ] at hg
  exact (clockMomentum ε h (modelDirections j)).mem_graph_snd_inj' hg
    ((clockMomentum ε h (modelDirections j)).graph.smul_mem s
      (KFCausalCorrelatedClusteredKineticGraphs.finite_graph f c α β ε h hα hβ hw hε hc hc2 δ hδ j)) rfl

theorem output_tendsto (j : Fin 4) :
    Tendsto (fun δ => KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput f ε h a p hε hh hb ha δ (kineticIndex j))
      (𝓝[>] 0) (𝓝 (limitingOutput f ε h a p hε hh ha j)) := by
  apply Tendsto.congr' _ ((KFCausalCorrelatedClusteredKineticGraphs.output_tendsto f c α β ε h hα hβ hε hc hc2 j).const_smul s)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finiteOutput_eq f ε h a p hε hh ha hb δ hδ j).symm

theorem graph_tendsto (j : Fin 4) :
    Tendsto (fun δ => (finiteMomentum f ε h a p hε hh ha δ,
      KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput f ε h a p hε hh hb ha δ (kineticIndex j)))
      (𝓝[>] 0) (𝓝 (limitingMomentum f ε h a p hε hh ha,limitingOutput f ε h a p hε hh ha j)) :=
  (momentum_tendsto f ε h a p hε hh ha).prodMk_nhds (output_tendsto f ε h a p hε hh ha hb j)

#print axioms limiting_graph
#print axioms limiting_domain
#print axioms finiteOutput_eq
#print axioms output_tendsto
#print axioms graph_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumKineticLimit
