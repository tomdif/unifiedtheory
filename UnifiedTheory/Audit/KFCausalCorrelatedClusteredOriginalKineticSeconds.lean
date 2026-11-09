/- The existing finite strong-Hamiltonian kinetic second outputs agree
with the constructed second vectors and converge to the actual limiting
second actions. The original finite theorem's narrower strip is retained. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalKineticSeconds
import UnifiedTheory.Audit.KFCausalReciprocalNeutralStrongHamiltonian
import UnifiedTheory.Audit.KFCausalReciprocalNeutralMomentumStrongHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredOriginalKineticSeconds
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredPhysicalClockLimit (lift)
open KFCausalCorrelatedClusteredPhysicalKineticSeconds (inputSecond momentumSecond reverseFactor_kinetic)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalCoherentFactorResponseBounds (kineticIndex)
open KFCausalCorrelatedClusteredInputProfiles (amplitudes inputAmplitude_continuous inputAmplitude_memLp)
open KFCausalCorrelatedClusteredMomentumAmplitudes (amplitude_continuous amplitude_memLp)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "c" => amplitudes ε a p
local notation "hc" => fun i => inputAmplitude_continuous ε (a i) (p i)
local notation "hc2" => fun i => inputAmplitude_memLp ε (a i) (p i) hε (ha i)
local notation "d" => KFCausalCorrelatedClusteredMomentumAmplitudes.amplitudes ε a p
local notation "hd" => fun i => amplitude_continuous ε (a i) (p i) hε
local notation "hd2" => fun i => amplitude_memLp ε (a i) (p i) hε (ha i)
local notation "F" => KFCausalCorrelatedClusteredPhysicalCauchy.finiteOutput f ε h a p hε hh hb₀ ha
local notation "G" => KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput f ε h a p hε hh hb₀ ha

def finiteSeconds (δ : ℝ) (j : Fin 8) : Hilbert := if hδ : 0 < δ then
  KFCausalReciprocalNeutralStrongHamiltonian.seconds (count f) ε h (lift f a) (widths f δ) (lift f p)
    (coefficients f δ) (sources f) (polynomials f) hε (fun k => ha (index f k).1) hh
    (widths_admissible f δ hδ.le) hb j else 0

def finiteMomentumSeconds (δ : ℝ) (j : Fin 8) : Hilbert := if hδ : 0 < δ then
  KFCausalReciprocalNeutralMomentumStrongHamiltonian.seconds (count f) ε h (lift f a) (widths f δ) (lift f p)
    (coefficients f δ) (sources f) (polynomials f) hε (fun k => ha (index f k).1) hh
    (widths_admissible f δ hδ.le) hb j else 0

theorem finite_reverse_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 8) :
    (F δ j,finiteSeconds f ε h a p hε hh ha hb δ j) ∈ (reverseFactor ε hε h modelDirections pointField j).graph := by
  rw [KFCausalCorrelatedClusteredPhysicalCauchy.finiteOutput,finiteSeconds,dif_pos hδ,dif_pos hδ]
  exact KFCausalReciprocalNeutralStrongHamiltonian.reverse_graph (count f) ε h (lift f a) (widths f δ) (lift f p)
    (coefficients f δ) (sources f) (polynomials f) hε (fun k => ha (index f k).1) hh
    (widths_admissible f δ hδ.le) hb j

theorem finiteMomentum_reverse_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 8) :
    (G δ j,finiteMomentumSeconds f ε h a p hε hh ha hb δ j) ∈ (reverseFactor ε hε h modelDirections pointField j).graph := by
  rw [KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput,finiteMomentumSeconds,dif_pos hδ,dif_pos hδ]
  exact KFCausalReciprocalNeutralMomentumStrongHamiltonian.reverse_graph (count f) ε h (lift f a) (widths f δ) (lift f p)
    (coefficients f δ) (sources f) (polynomials f) hε (fun k => ha (index f k).1) hh
    (widths_admissible f δ hδ.le) hb j

theorem finiteSeconds_eq (δ : ℝ) (hδ : 0 < δ) (j : Fin 4) :
    finiteSeconds f ε h a p hε hh ha hb δ (kineticIndex j) =
      KFCausalCorrelatedClusteredKineticSecondLimit.finiteOutput f c α β ε h hα hβ hε hc hc2 δ j := by
  have hg := finite_reverse_graph f ε h a p hε hh ha hb δ hδ (kineticIndex j)
  rw [KFCausalCorrelatedClusteredInputKineticLimit.finiteOutput_eq f ε h a p hε hh ha hb₀ δ hδ j,
    reverseFactor_kinetic ε h hε j] at hg
  exact (KFCausalClockFloorKineticSquare.reverse ε h (modelDirections j)).mem_graph_snd_inj' hg
    (KFCausalCorrelatedClusteredKineticSecondLimit.finite_reverse_graph f c α β ε h hα hβ hε hc hc2 δ hδ j) rfl

theorem finiteMomentumSeconds_eq (δ : ℝ) (hδ : 0 < δ) (j : Fin 4) :
    finiteMomentumSeconds f ε h a p hε hh ha hb δ (kineticIndex j) = (-Complex.I*(h:ℂ)) •
      KFCausalCorrelatedClusteredKineticSecondLimit.finiteOutput f d α β ε h hα hβ hε hd hd2 δ j := by
  have hg := finiteMomentum_reverse_graph f ε h a p hε hh ha hb δ hδ (kineticIndex j)
  rw [KFCausalCorrelatedClusteredMomentumKineticLimit.finiteOutput_eq f ε h a p hε hh ha hb₀ δ hδ j,
    reverseFactor_kinetic ε h hε j] at hg
  exact (KFCausalClockFloorKineticSquare.reverse ε h (modelDirections j)).mem_graph_snd_inj' hg
    ((KFCausalClockFloorKineticSquare.reverse ε h (modelDirections j)).graph.smul_mem (-Complex.I*(h:ℂ))
      (KFCausalCorrelatedClusteredKineticSecondLimit.finite_reverse_graph f d α β ε h hα hβ hε hd hd2 δ hδ j)) rfl

theorem inputSecond_tendsto (j : Fin 4) :
    Tendsto (fun δ => finiteSeconds f ε h a p hε hh ha hb δ (kineticIndex j)) (𝓝[>] 0)
      (𝓝 (inputSecond f ε h a p hε hh ha j)) := by
  apply Tendsto.congr' _ (KFCausalCorrelatedClusteredKineticSecondLimit.output_tendsto f c α β ε h hα hβ hε hc hc2 j)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finiteSeconds_eq f ε h a p hε hh ha hb δ hδ j).symm

theorem momentumSecond_tendsto (j : Fin 4) :
    Tendsto (fun δ => finiteMomentumSeconds f ε h a p hε hh ha hb δ (kineticIndex j)) (𝓝[>] 0)
      (𝓝 (momentumSecond f ε h a p hε hh ha j)) := by
  apply Tendsto.congr' _ ((KFCausalCorrelatedClusteredKineticSecondLimit.output_tendsto f d α β ε h hα hβ hε hd hd2 j).const_smul (-Complex.I*(h:ℂ)))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finiteMomentumSeconds_eq f ε h a p hε hh ha hb δ hδ j).symm

theorem input_second_graph_tendsto (j : Fin 4) :
    Tendsto (fun δ => (KFCausalCorrelatedClusteredInputProfiles.finiteState f ε h a p hε hh ha δ,
      finiteSeconds f ε h a p hε hh ha hb δ (kineticIndex j))) (𝓝[>] 0)
      (𝓝 (KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha,inputSecond f ε h a p hε hh ha j)) :=
  (KFCausalCorrelatedClusteredInputGraphLimit.state_tendsto f ε h a p hε hh ha).prodMk_nhds
    (inputSecond_tendsto f ε h a p hε hh ha hb j)

theorem momentum_second_graph_tendsto (j : Fin 4) :
    Tendsto (fun δ => (KFCausalCorrelatedClusteredPureMomentumLimit.finiteMomentum f ε h a p hε hh ha δ,
      finiteMomentumSeconds f ε h a p hε hh ha hb δ (kineticIndex j))) (𝓝[>] 0)
      (𝓝 (KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a p hε hh ha,momentumSecond f ε h a p hε hh ha j)) :=
  (KFCausalCorrelatedClusteredPureMomentumLimit.momentum_tendsto f ε h a p hε hh ha).prodMk_nhds
    (momentumSecond_tendsto f ε h a p hε hh ha hb j)

#print axioms finite_reverse_graph
#print axioms finiteMomentum_reverse_graph
#print axioms finiteSeconds_eq
#print axioms finiteMomentumSeconds_eq
#print axioms inputSecond_tendsto
#print axioms momentumSecond_tendsto
#print axioms input_second_graph_tendsto
#print axioms momentum_second_graph_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredOriginalKineticSeconds
