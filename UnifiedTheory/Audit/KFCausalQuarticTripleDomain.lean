/- Actual zero-charge centered/paired/corrected-quartic superpositions,
with common clock profile and all eight state/momentum operator graphs. -/
import UnifiedTheory.Audit.KFCausalPairedSpanDomain
import UnifiedTheory.Audit.KFCausalPairedQuarticDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalQuarticTripleDomain
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

abbrev Coefficients := (ℂ × ℂ) × ℂ

def combine (c : Coefficients) (f g : Hilbert) : Hilbert := f+c.2 • g

theorem combine_coe (c : Coefficients) (f g : Hilbert) (F G : Configuration → ℂ)
    (hf : f =ᵐ[volume] F) (hg : g =ᵐ[volume] G) :
    combine c f g =ᵐ[volume] fun x => F x+c.2*G x := by
  have he := KFCausalPairedSpanDomain.combine_coe (1,c.2) f g F G hf hg
  simpa only [KFCausalPairedSpanDomain.combine,Prod.fst,Prod.snd,one_smul,one_mul,combine] using he

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)

def state (c : Coefficients) : Hilbert :=
  combine c (KFCausalPairedSpanDomain.state ε a h hε ha hh c.1)
    (KFCausalPairedQuarticCharge.correctedState ε a h hε ha hh)
def momentum (c : Coefficients) : Hilbert :=
  combine c (KFCausalPairedSpanDomain.momentum ε a h hε ha hh c.1)
    (KFCausalPairedQuarticDomain.momentum ε a h hε ha hh)

theorem state_zeroSector (c : Coefficients) : state ε a h hε ha hh c ∈ zeroSector h hh :=
  (zeroSector h hh).add_mem (KFCausalPairedSpanDomain.state_zeroSector ε a h hε ha hh c.1)
    ((zeroSector h hh).smul_mem c.2 (KFCausalPairedQuarticCharge.corrected_zeroSector ε a h hε ha hh))

theorem momentum_graph (c : Coefficients) :
    (state ε a h hε ha hh c,momentum ε a h hε ha hh c) ∈ (pureMomentum ε hε h).graph :=
  (pureMomentum ε hε h).graph.add_mem (KFCausalPairedSpanDomain.momentum_graph ε a h hε ha hh c.1)
    ((pureMomentum ε hε h).graph.smul_mem c.2 (KFCausalPairedQuarticDomain.momentum_graph ε a h hε ha hh))

theorem momentum_zeroSector (c : Coefficients) :
    momentum ε a h hε ha hh c ∈ zeroSector h hh :=
  KFCausalPureClockZeroProjection.output_zeroSector ε hε h hh _ _
    (momentum_graph ε a h hε ha hh c) (state_zeroSector ε a h hε ha hh c)

variable (hb : |h| ≤ 2*Real.pi*ε/3)

def output (c : Coefficients) (j : Fin 8) : Hilbert :=
  combine c (KFCausalPairedSpanDomain.output ε a h hε ha hh hb c.1 j)
    (KFCausalPairedQuarticDomain.output ε a h hε ha hh hb modelDirections pointField j)
def momentumOutput (c : Coefficients) (j : Fin 8) : Hilbert :=
  combine c (KFCausalPairedSpanDomain.momentumOutput ε a h hε ha hh hb c.1 j)
    (KFCausalPairedQuarticDomain.momentumOutput ε a h hε ha hh hb modelDirections pointField j)

theorem output_graph (c : Coefficients) (j : Fin 8) :
    (state ε a h hε ha hh c,output ε a h hε ha hh hb c j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph :=
  (energyFactor ε hε h modelDirections pointField j).graph.add_mem
    (KFCausalPairedSpanDomain.output_graph ε a h hε ha hh hb c.1 j)
    ((energyFactor ε hε h modelDirections pointField j).graph.smul_mem c.2
      (KFCausalPairedQuarticDomain.output_graph ε a h hε ha hh hb modelDirections pointField j))

theorem momentumOutput_graph (c : Coefficients) (j : Fin 8) :
    (momentum ε a h hε ha hh c,momentumOutput ε a h hε ha hh hb c j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph :=
  (energyFactor ε hε h modelDirections pointField j).graph.add_mem
    (KFCausalPairedSpanDomain.momentumOutput_graph ε a h hε ha hh hb c.1 j)
    ((energyFactor ε hε h modelDirections pointField j).graph.smul_mem c.2
      (KFCausalPairedQuarticDomain.momentumOutput_graph ε a h hε ha hh hb modelDirections pointField j))

theorem clock_composition_graph (c : Coefficients) :
    (output ε a h hε ha hh hb c 0,
      momentumOutput ε a h hε ha hh hb c 0-correction ε hε h (output ε a h hε ha hh hb c 0)) ∈
        (pureMomentum ε hε h).graph := by
  have he := (pureMomentum ε hε h).graph.add_mem
    (KFCausalPairedSpanDomain.clock_composition_graph ε a h hε ha hh hb c.1)
    ((pureMomentum ε hε h).graph.smul_mem c.2
      (KFCausalPairedQuarticDomain.clock_composition_graph ε a h hε ha hh hb))
  convert he using 1
  congr 1
  simp only [output,momentumOutput,combine,Prod.smul_mk,smul_sub,map_add,map_smul]
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
end UnifiedTheory.Audit.KFCausalQuarticTripleDomain
