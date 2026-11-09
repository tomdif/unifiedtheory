/- Actual ambient displaced Gaussians have all eight second-factor
orbits and belong to every instantaneous Hamiltonian and the growing
operator. The stronger strip is explicit; no zero-charge restriction is
imposed on the displaced vector. -/
import UnifiedTheory.Audit.KFCausalAveragedSecondOrbitGraph
import UnifiedTheory.Audit.KFCausalCoherentSecondCurves
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedFormOrbit
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeGrowingGraph

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedSecondDomain
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (action)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorBoundedInverse (inverseL inverseL_graph)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalOrderedOperatorComposition (composition_graph)
open KFCausalClockFloorTrialClockEnergy (dampedClockFunction dampedClockFunction_memLp)
open KFCausalClockFloorCoherentBounds (sourceSize)
open KFCausalClockFloorDisplacedSources
open KFCausalClockFloorDisplacedParameterBounds
open KFCausalClockFloorDisplacedCommonDomain (rawState_eq_sourced)
open KFCausalClockFloorDisplacedStates (rawState action_rawState)
open KFCausalChargeModulationFlow (parameter)
open KFCausalClockFloorDisplacedBoostOrbit (parameter_clock)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)

section Sourced
variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => KFCausalGaussianVacuumSquare.original_strip ε h hε hb
local notation "g" => dampedClockFunction ε a
local notation "hg" => dampedClockFunction_memLp ε a hε ha

def sourceSecond (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) : Fin 8 → Hilbert :=
  ![KFCausalGaussianClockSquare.output ε a α β hε ha hα hβ hw C p b,
    inverseL ε hε (KFCausalSourcedSecondMomentum.secondOutput α β hα hβ hw C p b g hg h (modelDirections 0)),
    inverseL ε hε (KFCausalSourcedSecondMomentum.secondOutput α β hα hβ hw C p b g hg h (modelDirections 1)),
    inverseL ε hε (KFCausalSourcedSecondMomentum.secondOutput α β hα hβ hw C p b g hg h (modelDirections 2)),
    inverseL ε hε (KFCausalSourcedSecondMomentum.secondOutput α β hα hβ hw C p b g hg h (modelDirections 3)),
    KFCausalCoherentMatterSquare.output ε a α β hε ha hα hβ hw h hb C p b 0,
    KFCausalCoherentMatterSquare.output ε a α β hε ha hα hβ hw h hb C p b 1,
    KFCausalGaussianVacuumSquare.squareOutput ε a α β hε ha hα hβ hw C p b h hb]

theorem sourceSecond_graph (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 8) :
    (KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw
        C p b h hb₀ modelDirections pointField i,
      sourceSecond ε a α β hε ha hα hβ hw h hb C p b i) ∈
        (reverseFactor ε hε h modelDirections pointField i).graph := by
  have hk (j : Fin 4) :
      (KFCausalSourcedSecondMomentum.firstOutput α β hα hβ hw C p b g hg h (modelDirections j),
        inverseL ε hε (KFCausalSourcedSecondMomentum.secondOutput α β hα hβ hw C p b g hg h (modelDirections j))) ∈
          (KFCausalClockFloorKineticSquare.reverse ε h (modelDirections j)).graph :=
    (composition_graph _ _ _ _).mpr ⟨_,
      KFCausalSourcedSecondMomentum.second_graph α β hα hβ hw C p b g hg h _,
      (inverseL_graph ε hε _ _).mpr rfl⟩
  fin_cases i
  · exact KFCausalGaussianClockSquare.second_graph ε a α β hε ha hα hβ hw C p b
  · exact hk 0
  · exact hk 1
  · exact hk 2
  · exact hk 3
  · exact KFCausalCoherentMatterSquare.linear_reverse_graph ε a α β hε ha hα hβ hw h hb C p b
  · exact KFCausalCoherentMatterSquare.quadratic_reverse_graph ε a α β hε ha hα hβ hw h hb C p b
  · obtain ⟨u,hu,hz⟩ := (composition_graph _ _ _ _).mp
      (KFCausalGaussianVacuumSquare.squareOutput_graph ε a α β hε ha hα hβ hw C p b h hb)
    have he := (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).mem_graph_snd_inj'
      hu (KFCausalClockFloorSourcedCommonDomain.factorOutput_graph ε a α β hε ha hα hβ hw
        C p b h hb₀ modelDirections pointField 7) rfl
    dsimp only at he
    rwa [he] at hz

theorem sourceSecond_curve_continuous (P B : ℝ)
    (C : ℝ → ℂ) (p : ℝ → ℝ) (b : ℝ → Fin 5 → ℂ)
    (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
    (hC : ∀ θ, ‖C θ‖ ≤ 1) (hp : ∀ θ, |p θ| ≤ P) (hB : ∀ θ, sourceSize (b θ) ≤ B)
    (i : Fin 8) :
    Continuous (fun θ => sourceSecond ε a α β hε ha hα hβ hw h hb (C θ) (p θ) (b θ) i) := by
  have hk (j : Fin 4) := (inverseL ε hε).continuous.comp
    (KFCausalCoherentSecondCurves.kinetic_continuous ε a α β hε ha hα hβ hw h B
      C p b hCc hpc hbc hC hB j)
  have hm (j : Fin 2) := (inverseL ε hε).continuous.comp
    (KFCausalCoherentMatterCurve.spectral_continuous ε a α β hε ha hα hβ hw h hb P B
      C p b hCc hpc hbc hp hB j)
  fin_cases i
  · exact KFCausalCoherentSecondCurves.clock_continuous ε a α β hε ha hα hβ hw B
      C p b hCc hpc hbc hC hB
  · exact hk 0
  · exact hk 1
  · exact hk 2
  · exact hk 3
  · exact hm 0
  · exact hm 1
  · exact (inverseL ε hε).continuous.comp
      (KFCausalCoherentSecondCurves.vacuum_continuous ε a α β hε ha hα hβ hw h hb P B
        C p b hCc hpc hbc hC hp hB)
end Sourced

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (q k : Joint 2 4)
local notation "hb₀" => KFCausalGaussianVacuumSquare.original_strip ε h hε hb
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
local notation "C" => fun θ => amplitude h (parameter θ q) (parameter θ k)
local notation "p" => fun θ => clockFrequency h (parameter θ k)
local notation "b" => fun θ => source h (parameter θ q) (parameter θ k)

def firstCurve (i : Fin 8) (θ : ℝ) : Hilbert :=
  KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw
    (C θ) (p θ) (b θ) h hb₀ modelDirections pointField i

def secondCurve (i : Fin 8) (θ : ℝ) : Hilbert :=
  sourceSecond ε a α β hε ha hα hβ hw h hb (C θ) (p θ) (b θ) i

theorem firstCurve_continuous (i : Fin 8) :
    Continuous (firstCurve ε a h hε ha hh hb q k i) := by
  obtain ⟨B,hB⟩ := source_orbit_bound h q k
  exact KFCausalVariableWidthSourceCurves.factor_continuous ε a α β hε ha hα hβ hw h hb₀
    |clockFrequency h k| B C p b
    (amplitude_curve_continuous h q k)
    ((clockFrequency_continuous h).comp (parameter_curve_continuous k))
    (source_curve_continuous h q k) (fun θ => amplitude_norm_le_one h hh _ _)
    (fun θ => by
      change |clockFrequency h (parameter θ k)| ≤ |clockFrequency h k|
      rw [clockFrequency_parameter]) hB modelDirections pointField i

theorem secondCurve_continuous (i : Fin 8) :
    Continuous (secondCurve ε a h hε ha hh hb q k i) := by
  obtain ⟨B,hB⟩ := source_orbit_bound h q k
  exact sourceSecond_curve_continuous ε a α β hε ha hα hβ hw h hb
    |clockFrequency h k| B C p b
    (amplitude_curve_continuous h q k)
    ((clockFrequency_continuous h).comp (parameter_curve_continuous k))
    (source_curve_continuous h q k) (fun θ => amplitude_norm_le_one h hh _ _)
    (fun θ => by
      change |clockFrequency h (parameter θ k)| ≤ |clockFrequency h k|
      rw [clockFrequency_parameter]) hB i

variable (hq : q (.inr 0) = 0)
include hq in
theorem firstCurve_graph (θ : ℝ) (i : Fin 8) :
    (action h hh θ (rawState ε a h hε ha hh q k),firstCurve ε a h hε ha hh hb q k i θ) ∈
      (energyFactor ε hε h modelDirections pointField i).graph := by
  rw [action_rawState,rawState_eq_sourced ε a h hε ha hh _ _ ((parameter_clock θ q).trans hq)]
  exact KFCausalClockFloorSourcedCommonDomain.factorOutput_graph ε a α β hε ha hα hβ hw
    (C θ) (p θ) (b θ) h hb₀ modelDirections pointField i

theorem secondCurve_graph (θ : ℝ) (i : Fin 8) :
    (firstCurve ε a h hε ha hh hb q k i θ,secondCurve ε a h hε ha hh hb q k i θ) ∈
      (reverseFactor ε hε h modelDirections pointField i).graph :=
  sourceSecond_graph ε a α β hε ha hα hβ hw h hb (C θ) (p θ) (b θ) i

def hamiltonianOutput (mass2 quartic vacuum t : ℝ) : Hilbert :=
  KFCausalAveragedSecondOrbitGraph.secondOutput h hh mass2 quartic vacuum t
    (fun i θ => secondCurve ε a h hε ha hh hb q k i (2*Real.pi*θ))

include hq in
theorem hamiltonian_graph (mass2 quartic vacuum t : ℝ) :
    (rawState ε a h hε ha hh q k,hamiltonianOutput ε a h hε ha hh hb q k mass2 quartic vacuum t) ∈
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).graph :=
  KFCausalAveragedSecondOrbitGraph.hamiltonian_graph ε h hε hh hb₀ mass2 quartic vacuum t
    (rawState ε a h hε ha hh q k)
    (fun i θ => firstCurve ε a h hε ha hh hb q k i (2*Real.pi*θ))
    (fun i θ => secondCurve ε a h hε ha hh hb q k i (2*Real.pi*θ))
    (fun i => (firstCurve_continuous ε a h hε ha hh hb q k i).comp (continuous_const.mul continuous_id))
    (fun i => (secondCurve_continuous ε a h hε ha hh hb q k i).comp (continuous_const.mul continuous_id))
    (fun θ i => firstCurve_graph ε a h hε ha hh hb q k hq (2*Real.pi*θ) i)
    (fun θ i => secondCurve_graph ε a h hε ha hh hb q k (2*Real.pi*θ) i)

include hq in
theorem hamiltonian_domain (mass2 quartic vacuum t : ℝ) :
    rawState ε a h hε ha hh q k ∈
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph (hamiltonian_graph ε a h hε ha hh hb q k hq mass2 quartic vacuum t)

def growingOutput (mass2 quartic vacuum : ℝ) : Hilbert :=
  (Real.exp 2-1)⁻¹ • (hamiltonianOutput ε a h hε ha hh hb q k mass2 quartic vacuum 1-
    hamiltonianOutput ε a h hε ha hh hb q k mass2 quartic vacuum 0)

include hq in
theorem growing_graph (mass2 quartic vacuum : ℝ) :
    (rawState ε a h hε ha hh q k,growingOutput ε a h hε ha hh hb q k mass2 quartic vacuum) ∈
      (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb₀ mass2 quartic vacuum).graph := by
  simpa only [mul_one,mul_zero,Real.exp_zero] using
    KFCausalClockFloorTwoTimeGrowingGraph.difference_graph ε hε h hh hb₀ mass2 quartic vacuum
      0 1 (by norm_num) _ _ _
      (hamiltonian_graph ε a h hε ha hh hb q k hq mass2 quartic vacuum 0)
      (hamiltonian_graph ε a h hε ha hh hb q k hq mass2 quartic vacuum 1)

include hq in
theorem growing_domain (mass2 quartic vacuum : ℝ) :
    rawState ε a h hε ha hh q k ∈
      (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb₀ mass2 quartic vacuum).domain :=
  LinearPMap.mem_domain_of_mem_graph (growing_graph ε a h hε ha hh hb q k hq mass2 quartic vacuum)

#print axioms sourceSecond_graph
#print axioms sourceSecond_curve_continuous
#print axioms firstCurve_continuous
#print axioms secondCurve_continuous
#print axioms firstCurve_graph
#print axioms secondCurve_graph
#print axioms hamiltonian_graph
#print axioms hamiltonian_domain
#print axioms growing_graph
#print axioms growing_domain
end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedSecondDomain
