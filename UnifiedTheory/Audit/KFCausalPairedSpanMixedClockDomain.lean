/- Independently clocked centered/paired states and their actual momenta.
All eight graphs and the clock composition graph retain the full sum. -/
import UnifiedTheory.Audit.KFCausalChargedPairFrequencyDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedSpanMixedClockDomain
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPairedSpanMoments (Coefficients)
open KFCausalPairedSpanDomain (combine)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorPureClockKinetic (correction)
open KFCausalStandingChargeOperator (zeroSector)

variable (ε a b h p q : ℝ) (hε : 0 < ε) (ha : 0 < a) (hbw : 0 < b) (hh : h ≠ 0)

def state (c : Coefficients) : Hilbert :=
  combine c (KFCausalDirectionalGaussianDomain.input ε a h hε ha hh 1 p 0 0)
    (KFCausalChargedPairFrequencyDomain.state ε b h hε hbw hh q)
def momentum (c : Coefficients) : Hilbert :=
  combine c (KFCausalDirectionalClockMomentum.momentum ε a h hε ha hh p 0 1 0)
    (KFCausalChargedPairFrequencyDomain.momentum ε b h hε hbw hh q)

theorem state_zeroSector (c : Coefficients) :
    state ε a b h p q hε ha hbw hh c ∈ zeroSector h hh :=
  (zeroSector h hh).add_mem
    ((zeroSector h hh).smul_mem c.1 (KFCausalChargedPairFrequencyDomain.centered_zeroSector ε a h hε ha hh p))
    ((zeroSector h hh).smul_mem c.2 (KFCausalChargedPairFrequencyDomain.state_zeroSector ε b h hε hbw hh q))

theorem momentum_graph (c : Coefficients) :
    (state ε a b h p q hε ha hbw hh c,momentum ε a b h p q hε ha hbw hh c) ∈
      (pureMomentum ε hε h).graph :=
  (pureMomentum ε hε h).graph.add_mem
    ((pureMomentum ε hε h).graph.smul_mem c.1
      (KFCausalDirectionalClockMomentum.momentum_graph ε a h hε ha hh p 0 1 0))
    ((pureMomentum ε hε h).graph.smul_mem c.2
      (KFCausalChargedPairFrequencyDomain.momentum_graph ε b h hε hbw hh q))

theorem momentum_zeroSector (c : Coefficients) :
    momentum ε a b h p q hε ha hbw hh c ∈ zeroSector h hh :=
  KFCausalPureClockZeroProjection.output_zeroSector ε hε h hh _ _
    (momentum_graph ε a b h p q hε ha hbw hh c) (state_zeroSector ε a b h p q hε ha hbw hh c)

variable (hb : |h| ≤ 2*Real.pi*ε/3)

def output (c : Coefficients) (j : Fin 8) : Hilbert :=
  combine c
    (KFCausalDirectionalGaussianDomain.output ε a h hε ha hh 1 p 0 0 hb modelDirections pointField j)
    (KFCausalChargedPairFrequencyDomain.output ε b h hε hbw hh q hb modelDirections pointField j)
def momentumOutput (c : Coefficients) (j : Fin 8) : Hilbert :=
  combine c
    (KFCausalDirectionalClockMomentum.factor ε a h hε ha hh p 0 1 hb 0 modelDirections pointField j)
    (KFCausalChargedPairFrequencyDomain.momentumOutput ε b h hε hbw hh q hb modelDirections pointField j)

theorem output_graph (c : Coefficients) (j : Fin 8) :
    (state ε a b h p q hε ha hbw hh c,output ε a b h p q hε ha hbw hh hb c j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph :=
  (energyFactor ε hε h modelDirections pointField j).graph.add_mem
    ((energyFactor ε hε h modelDirections pointField j).graph.smul_mem c.1
      (KFCausalDirectionalGaussianDomain.output_graph ε a h hε ha hh 1 p 0 0 hb modelDirections pointField j))
    ((energyFactor ε hε h modelDirections pointField j).graph.smul_mem c.2
      (KFCausalChargedPairFrequencyDomain.output_graph ε b h hε hbw hh q hb modelDirections pointField j))

theorem momentumOutput_graph (c : Coefficients) (j : Fin 8) :
    (momentum ε a b h p q hε ha hbw hh c,momentumOutput ε a b h p q hε ha hbw hh hb c j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph :=
  (energyFactor ε hε h modelDirections pointField j).graph.add_mem
    ((energyFactor ε hε h modelDirections pointField j).graph.smul_mem c.1
      (KFCausalDirectionalClockMomentum.factor_graph ε a h hε ha hh p 0 1 hb 0 modelDirections pointField j))
    ((energyFactor ε hε h modelDirections pointField j).graph.smul_mem c.2
      (KFCausalChargedPairFrequencyDomain.momentumOutput_graph ε b h hε hbw hh q hb modelDirections pointField j))

theorem clock_composition_graph (c : Coefficients) :
    (output ε a b h p q hε ha hbw hh hb c 0,
      momentumOutput ε a b h p q hε ha hbw hh hb c 0-
        correction ε hε h (output ε a b h p q hε ha hbw hh hb c 0)) ∈
      (pureMomentum ε hε h).graph := by
  have he := (pureMomentum ε hε h).graph.add_mem
    ((pureMomentum ε hε h).graph.smul_mem c.1
      (KFCausalDirectionalClockComposition.composition_graph ε a h hε ha hh hb 1 p 0 0))
    ((pureMomentum ε hε h).graph.smul_mem c.2
      (KFCausalChargedPairFrequencyDomain.clock_composition_graph ε b h hε hbw hh q hb))
  convert he using 1
  congr 1
  simp only [output,momentumOutput,combine,Prod.smul_mk,smul_sub,map_add,map_smul]
  abel

def factorEnergy (c : Coefficients) (j : Fin 8) : ℝ := ‖output ε a b h p q hε ha hbw hh hb c j‖^2
def factorRate (c : Coefficients) (j : Fin 8) : ℝ :=
  (-2/h)*(inner ℂ (output ε a b h p q hε ha hbw hh hb c j)
    (momentumOutput ε a b h p q hε ha hbw hh hb c j)).im

theorem clock_response (c : Coefficients) :
    factorRate ε a b h p q hε ha hbw hh hb c 0 =
      -KFCausalClockFloorPureClockKineticResponse.response ε hε
        (output ε a b h p q hε ha hbw hh hb c 0) :=
  KFCausalClockFloorPureClockClockResponse.weak_response ε hε h hh
    (state ε a b h p q hε ha hbw hh c) _ (momentum ε a b h p q hε ha hbw hh c) _ _
    (output_graph ε a b h p q hε ha hbw hh hb c 0)
    (momentum_graph ε a b h p q hε ha hbw hh c)
    (momentumOutput_graph ε a b h p q hε ha hbw hh hb c 0)
    (clock_composition_graph ε a b h p q hε ha hbw hh hb c)

theorem clock_energy_bounds (c : Coefficients) :
    -(1/(4*ε))*factorEnergy ε a b h p q hε ha hbw hh hb c 0 ≤
        factorRate ε a b h p q hε ha hbw hh hb c 0 ∧
      factorRate ε a b h p q hε ha hbw hh hb c 0 ≤ 0 := by
  rw [clock_response]
  exact KFCausalClockFloorPureClockClockResponse.response_bounds ε hε
    (state ε a b h p q hε ha hbw hh c) (output ε a b h p q hε ha hbw hh hb c 0)

theorem kinetic_response (c : Coefficients) (i : Fin 4) :
    factorRate ε a b h p q hε ha hbw hh hb c (KFCausalCoherentFactorResponseBounds.kineticIndex i) =
      KFCausalClockFloorPureClockKineticResponse.response ε hε
        (output ε a b h p q hε ha hbw hh hb c (KFCausalCoherentFactorResponseBounds.kineticIndex i)) := by
  apply KFCausalClockFloorPureClockKineticResponse.weak_response ε hε h hh (modelDirections i)
    (state ε a b h p q hε ha hbw hh c) _ (momentum ε a b h p q hε ha hbw hh c) _
  · have hg := output_graph ε a b h p q hε ha hbw hh hb c (KFCausalCoherentFactorResponseBounds.kineticIndex i)
    fin_cases i <;> exact hg
  · exact momentum_graph ε a b h p q hε ha hbw hh c
  · have hg := momentumOutput_graph ε a b h p q hε ha hbw hh hb c (KFCausalCoherentFactorResponseBounds.kineticIndex i)
    fin_cases i <;> exact hg

theorem kinetic_bounds (c : Coefficients) (i : Fin 4) :
    0 ≤ factorRate ε a b h p q hε ha hbw hh hb c (KFCausalCoherentFactorResponseBounds.kineticIndex i) ∧
      factorRate ε a b h p q hε ha hbw hh hb c (KFCausalCoherentFactorResponseBounds.kineticIndex i) ≤
        (1/(4*ε))*factorEnergy ε a b h p q hε ha hbw hh hb c
          (KFCausalCoherentFactorResponseBounds.kineticIndex i) := by
  rw [kinetic_response]
  exact KFCausalClockFloorPureClockKineticResponse.response_bounds ε hε _

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
end UnifiedTheory.Audit.KFCausalPairedSpanMixedClockDomain
