/- Actual states, pure-clock momenta and all eight energy-factor outputs
for complex superpositions of the centered and paired quadratic packets.
Every graph is constructed by linearity of previously verified operators. -/
import UnifiedTheory.Audit.KFCausalChargedPairHamiltonianResponse
import UnifiedTheory.Audit.KFCausalChargedPairOrderedMomentumDensity
import UnifiedTheory.Audit.KFCausalPairedSpanMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedSpanDomain
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorPureClockKinetic (correction)
open KFCausalStandingChargeOperator (zeroSector)
open KFCausalPairedSpanMoments (Coefficients)

def combine (c : Coefficients) (f g : Hilbert) : Hilbert := c.1 • f+c.2 • g

theorem combine_coe (c : Coefficients) (f g : Hilbert) (F G : Configuration → ℂ)
    (hf : f =ᵐ[volume] F) (hg : g =ᵐ[volume] G) :
    combine c f g =ᵐ[volume] fun x => c.1*F x+c.2*G x := by
  filter_upwards [Lp.coeFn_add (c.1 • f) (c.2 • g), Lp.coeFn_smul c.1 f,
    Lp.coeFn_smul c.2 g, hf, hg] with x ha h0 h1 hf hg
  change (c.1 • f+c.2 • g) x = _
  rw [ha]
  simp only [Pi.add_apply, h0, h1, Pi.smul_apply, smul_eq_mul, hf, hg]

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)

def baseState : Hilbert := KFCausalDirectionalGaussianDomain.input ε a h hε ha hh 1 0 0 0
def baseMomentum : Hilbert := KFCausalDirectionalClockMomentum.momentum ε a h hε ha hh 0 0 1 0
def state (c : Coefficients) : Hilbert :=
  combine c (baseState ε a h hε ha hh) (KFCausalChargedPairDomain.state ε a h hε ha hh)
def momentum (c : Coefficients) : Hilbert :=
  combine c (baseMomentum ε a h hε ha hh) (KFCausalChargedPairClockMomentum.momentum ε a h hε ha hh)

theorem baseState_eq_trial :
    baseState ε a h hε ha hh = KFCausalClockFloorInvariantTrial.trialState ε a h hε ha hh := by
  apply Lp.ext
  filter_upwards [KFCausalDirectionalGaussianDomain.input_coe ε a h hε ha hh 1 0 0 0,
    KFCausalClockFloorInvariantTrial.trialState_coe ε a h hε ha hh] with x hx hy
  change baseState ε a h hε ha hh x = _ at hx
  rw [hx,hy]
  simp [KFCausalDirectionalGaussianStates.profile,
    KFCausalClockFloorCoherentDerivative.physicalProfile,
    KFCausalClockFloorCoherentDerivative.clockMultiplier,
    KFCausalClockFloorCoherentMoments.sourcedPacket,
    KFCausalClockFloorCoherentSources.linearSource,
    KFCausalClockFloorCoherentStrip.clockPhase,
    KFCausalChargeGaussianIdentities.configurationProfile]

theorem state_zeroSector (c : Coefficients) : state ε a h hε ha hh c ∈ zeroSector h hh := by
  have hb : baseState ε a h hε ha hh ∈ zeroSector h hh := by
    rw [baseState_eq_trial]
    exact KFCausalClockFloorInvariantTrial.trialState_mem_zeroSector ε a h hε ha hh
  exact (zeroSector h hh).add_mem ((zeroSector h hh).smul_mem c.1 hb)
    ((zeroSector h hh).smul_mem c.2 (KFCausalChargedPairCharge.state_zeroSector ε a h hε ha hh))

theorem momentum_graph (c : Coefficients) :
    (state ε a h hε ha hh c,momentum ε a h hε ha hh c) ∈ (pureMomentum ε hε h).graph :=
  (pureMomentum ε hε h).graph.add_mem
    ((pureMomentum ε hε h).graph.smul_mem c.1
      (KFCausalDirectionalClockMomentum.momentum_graph ε a h hε ha hh 0 0 1 0))
    ((pureMomentum ε hε h).graph.smul_mem c.2
      (KFCausalChargedPairClockMomentum.momentum_graph ε a h hε ha hh))

theorem momentum_zeroSector (c : Coefficients) :
    momentum ε a h hε ha hh c ∈ zeroSector h hh :=
  KFCausalPureClockZeroProjection.output_zeroSector ε hε h hh _ _
    (momentum_graph ε a h hε ha hh c) (state_zeroSector ε a h hε ha hh c)

variable (hb : |h| ≤ 2*Real.pi*ε/3)

def output (c : Coefficients) (j : Fin 8) : Hilbert :=
  combine c
    (KFCausalDirectionalGaussianDomain.output ε a h hε ha hh 1 0 0 0 hb modelDirections pointField j)
    (KFCausalChargedPairDomain.output ε a h hε ha hh hb modelDirections pointField j)

def momentumOutput (c : Coefficients) (j : Fin 8) : Hilbert :=
  combine c
    (KFCausalDirectionalClockMomentum.factor ε a h hε ha hh 0 0 1 hb 0 modelDirections pointField j)
    (KFCausalChargedPairClockMomentum.factor ε a h hε ha hh hb modelDirections pointField j)

theorem output_graph (c : Coefficients) (j : Fin 8) :
    (state ε a h hε ha hh c,output ε a h hε ha hh hb c j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph :=
  (energyFactor ε hε h modelDirections pointField j).graph.add_mem
    ((energyFactor ε hε h modelDirections pointField j).graph.smul_mem c.1
      (KFCausalDirectionalGaussianDomain.output_graph ε a h hε ha hh 1 0 0 0 hb modelDirections pointField j))
    ((energyFactor ε hε h modelDirections pointField j).graph.smul_mem c.2
      (KFCausalChargedPairDomain.output_graph ε a h hε ha hh hb modelDirections pointField j))

theorem momentumOutput_graph (c : Coefficients) (j : Fin 8) :
    (momentum ε a h hε ha hh c,momentumOutput ε a h hε ha hh hb c j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph :=
  (energyFactor ε hε h modelDirections pointField j).graph.add_mem
    ((energyFactor ε hε h modelDirections pointField j).graph.smul_mem c.1
      (KFCausalDirectionalClockMomentum.factor_graph ε a h hε ha hh 0 0 1 hb 0 modelDirections pointField j))
    ((energyFactor ε hε h modelDirections pointField j).graph.smul_mem c.2
      (KFCausalChargedPairClockMomentum.factor_graph ε a h hε ha hh hb modelDirections pointField j))

theorem clock_composition_graph (c : Coefficients) :
    (output ε a h hε ha hh hb c 0,
      momentumOutput ε a h hε ha hh hb c 0-correction ε hε h (output ε a h hε ha hh hb c 0)) ∈
        (pureMomentum ε hε h).graph := by
  have he := (pureMomentum ε hε h).graph.add_mem
    ((pureMomentum ε hε h).graph.smul_mem c.1
      (KFCausalDirectionalClockComposition.composition_graph ε a h hε ha hh hb 1 0 0 0))
    ((pureMomentum ε hε h).graph.smul_mem c.2
      (KFCausalChargedPairFactorResponse.clock_composition_graph ε a h hε ha hh hb))
  convert he using 1
  congr 1
  simp only [output, momentumOutput, combine, Prod.smul_mk, smul_sub, map_add, map_smul]
  abel

def factorEnergy (c : Coefficients) (j : Fin 8) : ℝ := ‖output ε a h hε ha hh hb c j‖^2
def factorRate (c : Coefficients) (j : Fin 8) : ℝ :=
  (-2/h)*(inner ℂ (output ε a h hε ha hh hb c j) (momentumOutput ε a h hε ha hh hb c j)).im

theorem clock_response (c : Coefficients) :
    factorRate ε a h hε ha hh hb c 0 =
      -KFCausalClockFloorPureClockKineticResponse.response ε hε (output ε a h hε ha hh hb c 0) :=
  KFCausalClockFloorPureClockClockResponse.weak_response ε hε h hh
    (state ε a h hε ha hh c) _ (momentum ε a h hε ha hh c) _ _
    (output_graph ε a h hε ha hh hb c 0) (momentum_graph ε a h hε ha hh c)
    (momentumOutput_graph ε a h hε ha hh hb c 0) (clock_composition_graph ε a h hε ha hh hb c)

theorem clock_energy_bounds (c : Coefficients) :
    -(1/(4*ε))*factorEnergy ε a h hε ha hh hb c 0 ≤ factorRate ε a h hε ha hh hb c 0 ∧
      factorRate ε a h hε ha hh hb c 0 ≤ 0 := by
  rw [clock_response]
  exact KFCausalClockFloorPureClockClockResponse.response_bounds ε hε
    (state ε a h hε ha hh c) (output ε a h hε ha hh hb c 0)

theorem kinetic_response (c : Coefficients) (i : Fin 4) :
    factorRate ε a h hε ha hh hb c (KFCausalCoherentFactorResponseBounds.kineticIndex i) =
      KFCausalClockFloorPureClockKineticResponse.response ε hε
        (output ε a h hε ha hh hb c (KFCausalCoherentFactorResponseBounds.kineticIndex i)) := by
  apply KFCausalClockFloorPureClockKineticResponse.weak_response ε hε h hh (modelDirections i)
    (state ε a h hε ha hh c) _ (momentum ε a h hε ha hh c) _
  · have hg := output_graph ε a h hε ha hh hb c (KFCausalCoherentFactorResponseBounds.kineticIndex i)
    fin_cases i <;> exact hg
  · exact momentum_graph ε a h hε ha hh c
  · have hg := momentumOutput_graph ε a h hε ha hh hb c (KFCausalCoherentFactorResponseBounds.kineticIndex i)
    fin_cases i <;> exact hg

theorem kinetic_bounds (c : Coefficients) (i : Fin 4) :
    0 ≤ factorRate ε a h hε ha hh hb c (KFCausalCoherentFactorResponseBounds.kineticIndex i) ∧
      factorRate ε a h hε ha hh hb c (KFCausalCoherentFactorResponseBounds.kineticIndex i) ≤
        (1/(4*ε))*factorEnergy ε a h hε ha hh hb c (KFCausalCoherentFactorResponseBounds.kineticIndex i) := by
  rw [kinetic_response]
  exact KFCausalClockFloorPureClockKineticResponse.response_bounds ε hε _

#print axioms combine_coe
#print axioms baseState_eq_trial
#print axioms state_zeroSector
#print axioms momentum_graph
#print axioms momentum_zeroSector
#print axioms output_graph
#print axioms momentumOutput_graph
#print axioms clock_composition_graph
#print axioms clock_response
#print axioms clock_energy_bounds
#print axioms kinetic_response
#print axioms kinetic_bounds
end
end UnifiedTheory.Audit.KFCausalPairedSpanDomain
