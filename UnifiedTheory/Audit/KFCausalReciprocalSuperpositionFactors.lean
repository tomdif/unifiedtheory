/- Actual factor graphs, representatives and clock/kinetic response
identities for finite reciprocal sums. Clock and charged widths may vary
independently between summands. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianResponse
import UnifiedTheory.Audit.KFCausalReciprocalCrossPhysical
import UnifiedTheory.Audit.KFCausalFiniteLpRepresentatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalSuperpositionFactors
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalStandingChargeOperator (zeroSector)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalCoherentFactorResponseBounds (kineticIndex)
open KFCausalSourcedResponseFactorBridge (index)

variable (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
  (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)

def state : Hilbert :=
  ∑ i, c i • KFCausalReciprocalGaussianCharge.state ε (a i) h (w i) hε (ha i) hh (by have := hw i; linarith)
def momentum : Hilbert :=
  ∑ i, c i • KFCausalReciprocalGaussianMomentum.momentum ε (a i) h (w i) hε (ha i) hh (hw i)

local notation "f" => state n ε h a w c hε ha hh hw
local notation "b" => momentum n ε h a w c hε ha hh hw

theorem state_zeroSector : f ∈ zeroSector h hh :=
  (zeroSector h hh).sum_mem (fun i (_ : i ∈ Finset.univ) => (zeroSector h hh).smul_mem (c i)
    (KFCausalReciprocalGaussianCharge.state_zeroSector ε (a i) h (w i) hε (ha i) hh (by have := hw i; linarith)))

theorem momentum_zeroSector : b ∈ zeroSector h hh :=
  (zeroSector h hh).sum_mem (fun i (_ : i ∈ Finset.univ) => (zeroSector h hh).smul_mem (c i)
    (KFCausalReciprocalGaussianMomentum.momentum_zeroSector ε (a i) h (w i) hε (ha i) hh (hw i)))

theorem momentum_graph : (f,b) ∈ (pureMomentum ε hε h).graph := by
  have hs := (pureMomentum ε hε h).graph.sum_mem (fun i (_ : i ∈ Finset.univ) =>
    (pureMomentum ε hε h).graph.smul_mem (c i)
      (KFCausalReciprocalGaussianMomentum.momentum_graph ε (a i) h (w i) hε (ha i) hh (hw i)))
  simpa only [state,momentum,Prod.smul_mk,← prod_mk_sum] using hs

variable (hb : |h| ≤ 2*Real.pi*ε/3)

def output (j : Fin 8) : Hilbert :=
  ∑ i, c i • KFCausalReciprocalGaussianMomentum.output ε (a i) h (w i) hε (ha i) hh (hw i) hb j
def momentumOutput (j : Fin 8) : Hilbert :=
  ∑ i, c i • KFCausalReciprocalGaussianMomentum.momentumOutput ε (a i) h (w i) hε (ha i) hh (hw i) hb j

local notation "u" => output n ε h a w c hε ha hh hw hb
local notation "v" => momentumOutput n ε h a w c hε ha hh hw hb

theorem output_graph (j : Fin 8) :
    (f,u j) ∈ (energyFactor ε hε h modelDirections pointField j).graph := by
  have hs := (energyFactor ε hε h modelDirections pointField j).graph.sum_mem
    (fun i (_ : i ∈ Finset.univ) => (energyFactor ε hε h modelDirections pointField j).graph.smul_mem (c i)
      (KFCausalReciprocalGaussianMomentum.output_graph ε (a i) h (w i) hε (ha i) hh (hw i) hb j))
  simpa only [state,output,Prod.smul_mk,← prod_mk_sum] using hs

theorem momentumOutput_graph (j : Fin 8) :
    (b,v j) ∈ (energyFactor ε hε h modelDirections pointField j).graph := by
  have hs := (energyFactor ε hε h modelDirections pointField j).graph.sum_mem
    (fun i (_ : i ∈ Finset.univ) => (energyFactor ε hε h modelDirections pointField j).graph.smul_mem (c i)
      (KFCausalReciprocalGaussianMomentum.momentumOutput_graph ε (a i) h (w i) hε (ha i) hh (hw i) hb j))
  simpa only [momentum,momentumOutput,Prod.smul_mk,← prod_mk_sum] using hs

theorem clock_output_domain : u 0 ∈ (pureMomentum ε hε h).domain :=
  (pureMomentum ε hε h).domain.sum_mem (fun i (_ : i ∈ Finset.univ) =>
    (pureMomentum ε hε h).domain.smul_mem (c i)
      (KFCausalReciprocalGaussianResponse.clock_output_domain ε (a i) h (w i) hε (ha i) hh (hw i) hb))

def factorEnergy (j : Fin 8) : ℝ := ‖u j‖^2
def factorRate (j : Fin 8) : ℝ := (-2/h)*(inner ℂ (u j) (v j)).im

local notation "E" => factorEnergy n ε h a w c hε ha hh hw hb
local notation "R" => factorRate n ε h a w c hε ha hh hw hb

theorem clock_response : R 0 = -KFCausalClockFloorPureClockKineticResponse.response ε hε (u 0) :=
  KFCausalClockFloorPureClockClockResponse.weak_response ε hε h hh f (u 0) b (v 0) _
    (output_graph n ε h a w c hε ha hh hw hb 0)
    (momentum_graph n ε h a w c hε ha hh hw)
    (momentumOutput_graph n ε h a w c hε ha hh hw hb 0)
    ((pureMomentum ε hε h).mem_graph ⟨u 0,clock_output_domain n ε h a w c hε ha hh hw hb⟩)

theorem kinetic_response (i : Fin 4) :
    R (kineticIndex i) = KFCausalClockFloorPureClockKineticResponse.response ε hε (u (kineticIndex i)) := by
  apply KFCausalClockFloorPureClockKineticResponse.weak_response ε hε h hh (modelDirections i) f _ b _
  · have hg := output_graph n ε h a w c hε ha hh hw hb (kineticIndex i)
    fin_cases i <;> exact hg
  · exact momentum_graph n ε h a w c hε ha hh hw
  · have hg := momentumOutput_graph n ε h a w c hε ha hh hw hb (kineticIndex i)
    fin_cases i <;> exact hg

theorem clock_energy_bounds : -(1/(4*ε))*E 0 ≤ R 0 ∧ R 0 ≤ 0 := by
  rw [clock_response]
  exact KFCausalClockFloorPureClockClockResponse.response_bounds ε hε f (u 0)

theorem kinetic_bounds (i : Fin 4) : 0 ≤ R (kineticIndex i) ∧ R (kineticIndex i) ≤ (1/(4*ε))*E (kineticIndex i) := by
  rw [kinetic_response]
  exact KFCausalClockFloorPureClockKineticResponse.response_bounds ε hε (u (kineticIndex i))

theorem output_coe (k : Fin 3) : u (index k) =ᵐ[volume] KFCausalReciprocalCrossPhysical.factorSum n ε h a w c k :=
  KFCausalFiniteLpRepresentatives.weighted_sum_coe volume c _ _ (fun i =>
    KFCausalReciprocalGaussianOutputs.output_coe ε (a i) h (w i) hε (ha i) hh (hw i) hb k)

theorem momentumOutput_coe (k : Fin 3) :
    v (index k) =ᵐ[volume] KFCausalReciprocalCrossPhysical.momentumFactorSum n ε h a w c k :=
  KFCausalFiniteLpRepresentatives.weighted_sum_coe volume c _ _ (fun i =>
    KFCausalReciprocalGaussianOutputs.momentumOutput_coe ε (a i) h (w i) hε (ha i) hh (hw i) hb k)

#print axioms state_zeroSector
#print axioms momentum_zeroSector
#print axioms momentum_graph
#print axioms output_graph
#print axioms momentumOutput_graph
#print axioms clock_output_domain
#print axioms clock_response
#print axioms kinetic_response
#print axioms clock_energy_bounds
#print axioms kinetic_bounds
#print axioms output_coe
#print axioms momentumOutput_coe
end
end UnifiedTheory.Audit.KFCausalReciprocalSuperpositionFactors
