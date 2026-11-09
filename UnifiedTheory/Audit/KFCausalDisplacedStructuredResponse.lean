/- Finite complex superpositions of displaced packets, with independently
chosen positive clock widths. Both f and its actual B f have constructed
full averaged energy-form lifts. The fixed-time response retains all
interference. No bound uniform in the packets or evolution derivative is asserted. -/
import UnifiedTheory.Audit.KFCausalDisplacedMomentumOrbit
import UnifiedTheory.Audit.KFCausalCoherentFullResponseReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates (state action_state)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedBoostOrbit (parameter_clock)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalCoherentFullMomentumPairing
  (pairingDensity pairingDensity_integrable)
open UnifiedTheory.Audit.KFCausalCoherentMomentumEnergyLift (lift lift_pairing)

structure Packet where
  width : ℝ
  width_pos : 0 < width
  centre : Joint 2 4
  frequency : Joint 2 4
  clock_zero : centre (.inr 0) = 0

/-- A finite quantum superposition; coefficients are amplitudes, not probabilities. -/
structure StructuredState where
  size : ℕ
  packet : Fin size → Packet
  coefficient : Fin size → ℂ

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (P : StructuredState)

def input : Hilbert := ∑ j, P.coefficient j •
  state ε (P.packet j).width h hε (P.packet j).width_pos hh (P.packet j).centre (P.packet j).frequency

def momentumOutput : Hilbert := ∑ j, P.coefficient j •
  KFCausalDisplacedMomentumOrbit.pureOutput ε (P.packet j).width h hε (P.packet j).width_pos hh
    (P.packet j).centre (P.packet j).frequency

def inputOrbit (i : Fin 8) (θ : ℝ) : Hilbert := ∑ j, P.coefficient j •
  KFCausalClockFloorDisplacedCommonDomain.factorOutput ε (P.packet j).width h hε (P.packet j).width_pos hh hb
    (parameter (2*Real.pi*θ) (P.packet j).centre) (parameter (2*Real.pi*θ) (P.packet j).frequency)
    modelDirections pointField i

def momentumOrbit (i : Fin 8) (θ : ℝ) : Hilbert := ∑ j, P.coefficient j •
  KFCausalDisplacedMomentumOrbit.factorOutput ε (P.packet j).width h hε (P.packet j).width_pos hh hb
    (parameter (2*Real.pi*θ) (P.packet j).centre) (parameter (2*Real.pi*θ) (P.packet j).frequency)
    modelDirections pointField i

theorem momentum_graph : (input ε h hε hh P,momentumOutput ε h hε hh P) ∈
    (pureMomentum ε hε h).graph := by
  have hs := (pureMomentum ε hε h).graph.sum_mem
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin P.size))) =>
      (pureMomentum ε hε h).graph.smul_mem (P.coefficient j)
        (KFCausalDisplacedMomentumOrbit.pureOutput_graph ε (P.packet j).width h hε
          (P.packet j).width_pos hh (P.packet j).centre (P.packet j).frequency (P.packet j).clock_zero))
  simpa only [input,momentumOutput,Prod.smul_mk,← prod_mk_sum] using hs

theorem inputOrbit_graph (θ : ℝ) (i : Fin 8) :
    (action h hh (2*Real.pi*θ) (input ε h hε hh P),inputOrbit ε h hε hh hb P i θ) ∈
      (energyFactor ε hε h modelDirections pointField i).graph := by
  simp only [input,map_sum,map_smul,action_state]
  have hs := (energyFactor ε hε h modelDirections pointField i).graph.sum_mem
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin P.size))) =>
      (energyFactor ε hε h modelDirections pointField i).graph.smul_mem (P.coefficient j)
        (KFCausalClockFloorDisplacedCommonDomain.factorOutput_graph ε (P.packet j).width h hε
          (P.packet j).width_pos hh hb
          (parameter (2*Real.pi*θ) (P.packet j).centre) (parameter (2*Real.pi*θ) (P.packet j).frequency)
          ((parameter_clock (2*Real.pi*θ) (P.packet j).centre).trans (P.packet j).clock_zero)
          modelDirections pointField i))
  simpa only [inputOrbit,Prod.smul_mk,← prod_mk_sum] using hs

theorem momentumOrbit_graph (θ : ℝ) (i : Fin 8) :
    (action h hh (2*Real.pi*θ) (momentumOutput ε h hε hh P),momentumOrbit ε h hε hh hb P i θ) ∈
      (energyFactor ε hε h modelDirections pointField i).graph := by
  simp only [momentumOutput,map_sum,map_smul]
  have hs := (energyFactor ε hε h modelDirections pointField i).graph.sum_mem
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin P.size))) =>
      (energyFactor ε hε h modelDirections pointField i).graph.smul_mem (P.coefficient j)
        (KFCausalDisplacedMomentumOrbit.factorOutput_action_graph ε (P.packet j).width h hε
          (P.packet j).width_pos hh hb (P.packet j).centre (P.packet j).frequency
          (P.packet j).clock_zero (2*Real.pi*θ) modelDirections pointField i))
  simpa only [momentumOrbit,Prod.smul_mk,← prod_mk_sum] using hs

theorem inputOrbit_continuous (i : Fin 8) : Continuous (inputOrbit ε h hε hh hb P i) :=
  continuous_finset_sum Finset.univ (fun j _ =>
    ((KFCausalClockFloorDisplacedFormOrbit.factorOutput_orbit_continuous ε (P.packet j).width h hε
      (P.packet j).width_pos hh hb (P.packet j).centre (P.packet j).frequency modelDirections pointField i).comp
        (continuous_const.mul continuous_id)).const_smul (P.coefficient j))

theorem momentumOrbit_continuous (i : Fin 8) : Continuous (momentumOrbit ε h hε hh hb P i) :=
  continuous_finset_sum Finset.univ (fun j _ =>
    ((KFCausalDisplacedMomentumOrbit.factorOutput_orbit_continuous ε (P.packet j).width h hε
      (P.packet j).width_pos hh hb (P.packet j).centre (P.packet j).frequency modelDirections pointField i).comp
        (continuous_const.mul continuous_id)).const_smul (P.coefficient j))

theorem orbit_memLp (i : Fin 8) :
    MemLp (inputOrbit ε h hε hh hb P i) 2 angleMeasure ∧
      MemLp (momentumOrbit ε h hε hh hb P i) 2 angleMeasure :=
  ⟨continuous_angle_memLp _ (inputOrbit_continuous ε h hε hh hb P i),
    continuous_angle_memLp _ (momentumOrbit_continuous ε h hε hh hb P i)⟩

variable (mass2 quartic vacuum t : ℝ)
local notation "hp" => hamiltonian_bound ε h hb
local notation "Full" => AveragedSpace ε hε h hp hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hp hh mass2 quartic vacuum t
local notation "out" => energyOutput ε hε h hp hh mass2 quartic vacuum t
local notation "g" => inputOrbit ε h hε hh hb P
local notation "k" => momentumOrbit ε h hε hh hb P

def inputLift : Full := lift ε h hε hh hb mass2 quartic vacuum t (input ε h hε hh P) g
  (inputOrbit_continuous ε h hε hh hb P) (inputOrbit_graph ε h hε hh hb P)

def momentumLift : Full := lift ε h hε hh hb mass2 quartic vacuum t (momentumOutput ε h hε hh P) k
  (momentumOrbit_continuous ε h hε hh hb P) (momentumOrbit_graph ε h hε hh hb P)

theorem lifts_embedding :
    embed (inputLift ε h hε hh hb P mass2 quartic vacuum t) = input ε h hε hh P ∧
      embed (momentumLift ε h hε hh hb P mass2 quartic vacuum t) = momentumOutput ε h hε hh P := ⟨rfl,rfl⟩

theorem both_energy_domains :
    input ε h hε hh P ∈ (energyOperator ε hε h hp hh mass2 quartic vacuum t).domain ∧
      momentumOutput ε h hε hh P ∈ (energyOperator ε hε h hp hh mass2 quartic vacuum t).domain :=
  ⟨(energy_domain ε hε h hp hh mass2 quartic vacuum t _).mpr
      ⟨inputLift ε h hε hh hb P mass2 quartic vacuum t,rfl⟩,
    (energy_domain ε hε h hp hh mass2 quartic vacuum t _).mpr
      ⟨momentumLift ε h hε hh hb P mass2 quartic vacuum t,rfl⟩⟩

theorem actual_momentum_energy_domain (b : Hilbert)
    (hB : (input ε h hε hh P,b) ∈ (pureMomentum ε hε h).graph) :
    b ∈ (energyOperator ε hε h hp hh mass2 quartic vacuum t).domain := by
  have he := (pureMomentum ε hε h).mem_graph_snd_inj' hB (momentum_graph ε h hε hh P) rfl
  dsimp only at he
  rw [he]
  exact (both_energy_domains ε h hε hh hb P mass2 quartic vacuum t).2

theorem actual_pairing (u v : Full) (hu : embed u = input ε h hε hh P)
    (hv : embed v = momentumOutput ε h hε hh P) :
    Integrable (pairingDensity mass2 quartic vacuum t g k) angleMeasure ∧
      inner ℂ (out u) (out v) = ∫ θ, pairingDensity mass2 quartic vacuum t g k θ ∂angleMeasure ∧
      (-2/h)*(inner ℂ (out u) (out v)).im =
        ∫ θ, (-2/h)*(pairingDensity mass2 quartic vacuum t g k θ).im ∂angleMeasure := by
  have eu : inputLift ε h hε hh hb P mass2 quartic vacuum t = u :=
    embedding_injective ε hε h hp hh mass2 quartic vacuum t hu.symm
  have ev : momentumLift ε h hε hh hb P mass2 quartic vacuum t = v :=
    embedding_injective ε hε h hp hh mass2 quartic vacuum t hv.symm
  have he : inner ℂ (out u) (out v) = ∫ θ, pairingDensity mass2 quartic vacuum t g k θ ∂angleMeasure := by
    rw [← eu,← ev]
    exact lift_pairing ε h hε hh hb mass2 quartic vacuum t _ _ g k
      (inputOrbit_continuous ε h hε hh hb P) (momentumOrbit_continuous ε h hε hh hb P)
      (inputOrbit_graph ε h hε hh hb P) (momentumOrbit_graph ε h hε hh hb P)
  have hi := pairingDensity_integrable mass2 quartic vacuum t g k
    (inputOrbit_continuous ε h hε hh hb P) (momentumOrbit_continuous ε h hε hh hb P)
  refine ⟨hi,he,?_⟩
  exact (congrArg (fun z : ℂ => (-2/h)*z.im) he).trans
    ((congrArg (fun r : ℝ => (-2/h)*r) (integral_im hi).symm).trans
      (integral_const_mul (-2/h) _).symm)

theorem actual_full_response (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) :
    (-2/h)*(inner ℂ (out (inputLift ε h hε hh hb P mass2 quartic vacuum t))
      (out (momentumLift ε h hε hh hb P mass2 quartic vacuum t))).im =
        KFCausalCoherentFullResponseReduction.fullRate mass2 quartic vacuum t h g k :=
  (actual_pairing ε h hε hh hb P mass2 quartic vacuum t _ _ rfl rfl).2.2.trans
    (KFCausalFullMomentumRateDecomposition.physical_decomposition mass2 quartic vacuum t h hm hq hvac g k
      (inputOrbit_continuous ε h hε hh hb P) (momentumOrbit_continuous ε h hε hh hb P))

#print axioms momentum_graph
#print axioms inputOrbit_graph
#print axioms momentumOrbit_graph
#print axioms inputOrbit_continuous
#print axioms momentumOrbit_continuous
#print axioms orbit_memLp
#print axioms lifts_embedding
#print axioms both_energy_domains
#print axioms actual_momentum_energy_domain
#print axioms actual_pairing
#print axioms actual_full_response
end
end UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse
