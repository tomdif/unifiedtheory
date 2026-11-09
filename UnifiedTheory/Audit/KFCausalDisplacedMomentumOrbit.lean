/- The actual clock momentum of every normalized displaced packet has
continuous outputs for all eight energy factors around its charge orbit.
Clock displacement is zero; transverse centres and all frequencies are arbitrary. -/
import UnifiedTheory.Audit.KFCausalSourcedMomentumFactors
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedFormOrbit
import UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalDisplacedMomentumOrbit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates (state state_normalization action_state)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedCommonDomain (rawState_eq_sourced)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (amplitude clockFrequency source amplitude_norm_le_one)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedBoostOrbit (parameter_clock)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound trialState)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (physicalProfile_curve_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentGradientContinuity (derivative_curve_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
  (halfClockFunction halfClockFunction_memLp dampedClockFunction dampedClockFunction_memLp)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4)
local notation "N" => (‖trialState ε a h hε ha hh‖⁻¹ : ℝ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h

def pureOutput : Hilbert := N • KFCausalSourcedMomentumFactors.pureOutput
  ε a α β hε ha hα hβ hw (amplitude h q k) (clockFrequency h k) (source h q k) h

def factorOutput (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) : Hilbert :=
  N • KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hw
    (amplitude h q k) (clockFrequency h k) (source h q k) h hb v l i

theorem pureOutput_graph (hq : q (.inr 0) = 0) :
    (state ε a h hε ha hh q k,pureOutput ε a h hε ha hh q k) ∈ (pureMomentum ε hε h).graph := by
  rw [state_normalization,rawState_eq_sourced ε a h hε ha hh q k hq]
  exact ((pureMomentum ε hε h).graph.restrictScalars ℝ).smul_mem N
    (KFCausalSourcedMomentumFactors.pureOutput_graph ε a α β hε ha hα hβ hw
      (amplitude h q k) (clockFrequency h k) (source h q k) h hh)

theorem factorOutput_graph (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    (pureOutput ε a h hε ha hh q k,factorOutput ε a h hε ha hh hb q k v l i) ∈
      (energyFactor ε hε h v l i).graph :=
  ((energyFactor ε hε h v l i).graph.restrictScalars ℝ).smul_mem N
    (KFCausalSourcedMomentumFactors.factorOutput_graph ε a α β hε ha hα hβ hw
      (amplitude h q k) (clockFrequency h k) (source h q k) h hh hb v l i)

theorem sourceFactor_orbit_continuous (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    Continuous (fun θ => KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw
      (amplitude h (parameter θ q) (parameter θ k)) (clockFrequency h (parameter θ k))
      (source h (parameter θ q) (parameter θ k)) h hb v l i) := by
  obtain ⟨B,hB⟩ := source_orbit_bound h q k
  let C := fun θ => amplitude h (parameter θ q) (parameter θ k)
  let p := fun θ => clockFrequency h (parameter θ k)
  let b := fun θ => source h (parameter θ q) (parameter θ k)
  have hCc : Continuous C := amplitude_curve_continuous h q k
  have hpc : Continuous p := (clockFrequency_continuous h).comp (parameter_curve_continuous k)
  have hbc : Continuous b := source_curve_continuous h q k
  have hC : ∀ θ, ‖C θ‖ ≤ 1 := fun θ => amplitude_norm_le_one h hh _ _
  have hp : ∀ θ, |p θ| ≤ |clockFrequency h k| := by
    intro θ
    dsimp only [p]
    rw [clockFrequency_parameter]
  have hc := physicalProfile_curve_continuous α β B hα hβ hw C p b
    (halfClockFunction ε a) (halfClockFunction_memLp ε a hε ha) hCc hpc hbc hC hB
  have hm (u : Transverse) := (continuous_const (y := -Complex.I*(h:ℂ))).smul
    (derivative_curve_continuous α β B hα hβ hw C p b
      (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha) hCc hpc hbc hC hB u)
  have hs := KFCausalClockFloorSourcedFieldContinuity.outputs_curve_continuous ε a h hε ha hh hb
    |clockFrequency h k| B C p b hCc hpc hbc hC hp hB
  fin_cases i
  · exact hc
  · exact hm (v 0)
  · exact hm (v 1)
  · exact hm (v 2)
  · exact hm (v 3)
  · exact hs.2.1 l
  · exact hs.2.2 l
  · exact hs.1

theorem factorOutput_orbit_continuous (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    Continuous (fun θ => factorOutput ε a h hε ha hh hb (parameter θ q) (parameter θ k) v l i) := by
  have hc := sourceFactor_orbit_continuous ε a h hε ha hh hb q k v l i
  have hd := sourceFactor_orbit_continuous ε (a/2) h hε (by positivity) hh hb q k v l i
  simp_rw [clockFrequency_parameter] at hc hd
  unfold factorOutput KFCausalSourcedMomentumFactors.factorOutput
  simp only [clockFrequency_parameter]
  by_cases hi : i.val < 5
  · simp only [hi,ite_true]
    exact (KFCausalPureClockOutputMultipliers.outputMap_continuous ε a h hε ha _ _ _ hc hd).const_smul N
  · simp only [hi,ite_false]
    exact (KFCausalCoherentMomentumOutputReduction.reducedOutput_continuous ε a h hε ha hb _ _ _ hc hd).const_smul N

theorem pureOutput_action (hq : q (.inr 0) = 0) (θ : ℝ) :
    pureOutput ε a h hε ha hh (parameter θ q) (parameter θ k) =
      action h hh θ (pureOutput ε a h hε ha hh q k) := by
  have hg := KFCausalClockFloorPureClockChargeGraph.graph_charge ε hε h hh θ _ _
    (pureOutput_graph ε a h hε ha hh q k hq)
  rw [action_state] at hg
  exact (pureMomentum ε hε h).mem_graph_snd_inj'
    (pureOutput_graph ε a h hε ha hh _ _ ((parameter_clock θ q).trans hq)) hg rfl

theorem factorOutput_action_graph (hq : q (.inr 0) = 0) (θ : ℝ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    (action h hh θ (pureOutput ε a h hε ha hh q k),
      factorOutput ε a h hε ha hh hb (parameter θ q) (parameter θ k) v l i) ∈
        (energyFactor ε hε h v l i).graph := by
  rw [← pureOutput_action ε a h hε ha hh q k hq θ]
  exact factorOutput_graph ε a h hε ha hh hb _ _ v l i

#print axioms pureOutput_graph
#print axioms factorOutput_graph
#print axioms sourceFactor_orbit_continuous
#print axioms factorOutput_orbit_continuous
#print axioms pureOutput_action
#print axioms factorOutput_action_graph
end
end UnifiedTheory.Audit.KFCausalDisplacedMomentumOrbit
