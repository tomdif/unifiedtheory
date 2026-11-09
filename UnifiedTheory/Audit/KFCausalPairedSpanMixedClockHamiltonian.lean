/- The independently clocked centered/paired states in the completed
Hamiltonian form. Both lifts come from proved charge and factor graphs;
all eight physical contributions retain the full interference. -/
import UnifiedTheory.Audit.KFCausalPairedSpanMixedClockDomain
import UnifiedTheory.Audit.KFCausalFixedCommonEnergyPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalPairedSpanMixedClockHamiltonian
noncomputable section
open KFCausalPairedSpanMoments (Coefficients)
open KFCausalPairedSpanMixedClockDomain
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding energyOutput)
open KFCausalClockFloorAveragedHamiltonian (graphFormVector)
open KFCausalFixedCommonEnergyPairing
open KFCausalPhysicalEnergyFactors (energyWeight energyWeight_norm_square)
open KFCausalClockFloorPureClockMomentum (pureMomentum)

private theorem unit_sum (t : ℝ) (r : Fin 8 → ℝ) :
    (∑ i : Fin 8, ‖energyWeight 1 1 1 t i‖^2*r i) =
      (r 0+r 1+r 2)/2+Real.exp (2*t)*((r 3+r 4)/2+r 5/2+r 6/4+r 7) := by
  simp_rw [energyWeight_norm_square 1 1 1 t (by norm_num) (by norm_num) (by norm_num)]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  ring!

variable (ε a b h p q : ℝ) (hε : 0 < ε) (ha : 0 < a) (hbw : 0 < b) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (c : Coefficients)
local notation "f" => state ε a b h p q hε ha hbw hh c
local notation "Bf" => momentum ε a b h p q hε ha hbw hh c
local notation "u" => output ε a b h p q hε ha hbw hh hb c
local notation "v" => momentumOutput ε a b h p q hε ha hbw hh hb c
local notation "E" => factorEnergy ε a b h p q hε ha hbw hh hb c
local notation "R" => factorRate ε a b h p q hε ha hbw hh hb c

def inputLift (m g k t : ℝ) : FormSpace ε hε h hh hb m g k t :=
  graphFormVector ε hε h hh hb m g k t
    (fixedLift ε h hε hh hb m g k t f (state_zeroSector ε a b h p q hε ha hbw hh c) u
      (output_graph ε a b h p q hε ha hbw hh hb c))

def momentumLift (m g k t : ℝ) : FormSpace ε hε h hh hb m g k t :=
  graphFormVector ε hε h hh hb m g k t
    (fixedLift ε h hε hh hb m g k t Bf (momentum_zeroSector ε a b h p q hε ha hbw hh c) v
      (momentumOutput_graph ε a b h p q hε ha hbw hh hb c))

theorem inputLift_embedding (m g k t : ℝ) :
    embedding ε hε h hh hb m g k t (inputLift ε a b h p q hε ha hbw hh hb c m g k t) = f := rfl
theorem momentumLift_embedding (m g k t : ℝ) :
    embedding ε hε h hh hb m g k t (momentumLift ε a b h p q hε ha hbw hh hb c m g k t) = Bf := rfl

theorem lifted_momentum_graph (m g k t : ℝ) :
    (embedding ε hε h hh hb m g k t (inputLift ε a b h p q hε ha hbw hh hb c m g k t),
      embedding ε hε h hh hb m g k t (momentumLift ε a b h p q hε ha hbw hh hb c m g k t)) ∈
        (pureMomentum ε hε h).graph := momentum_graph ε a b h p q hε ha hbw hh c

def fullEnergy (m g k t : ℝ) : ℝ :=
  ‖energyOutput ε hε h hh hb m g k t (inputLift ε a b h p q hε ha hbw hh hb c m g k t)‖^2
def fullResponse (m g k t : ℝ) : ℝ :=
  (-2/h)*(inner ℂ
    (energyOutput ε hε h hh hb m g k t (inputLift ε a b h p q hε ha hbw hh hb c m g k t))
    (energyOutput ε hε h hh hb m g k t (momentumLift ε a b h p q hε ha hbw hh hb c m g k t))).im

theorem energy_decomposition (m g k t : ℝ) :
    fullEnergy ε a b h p q hε ha hbw hh hb c m g k t = ∑ j : Fin 8, ‖energyWeight m g k t j‖^2*E j :=
  fixedLift_energy ε h hε hh hb m g k t f (state_zeroSector ε a b h p q hε ha hbw hh c) u
    (output_graph ε a b h p q hε ha hbw hh hb c)

theorem response_decomposition (m g k t : ℝ) :
    fullResponse ε a b h p q hε ha hbw hh hb c m g k t = ∑ j : Fin 8, ‖energyWeight m g k t j‖^2*R j :=
  fixedLift_response ε h hε hh hb m g k t f (state_zeroSector ε a b h p q hε ha hbw hh c) u
    (output_graph ε a b h p q hε ha hbw hh hb c) Bf (momentum_zeroSector ε a b h p q hε ha hbw hh c) v
    (momentumOutput_graph ε a b h p q hε ha hbw hh hb c)

def clockKineticEnergy (t : ℝ) : ℝ := (E 0+E 1+E 2)/2+Real.exp (2*t)*(E 3+E 4)/2
def clockKineticResponse (t : ℝ) : ℝ := (R 0+R 1+R 2)/2+Real.exp (2*t)*(R 3+R 4)/2
def potentialEnergy : ℝ := E 7+E 5/2+E 6/4
def potentialResponse : ℝ := R 7+R 5/2+R 6/4

theorem unit_full_energy (t : ℝ) :
    fullEnergy ε a b h p q hε ha hbw hh hb c 1 1 1 t =
      clockKineticEnergy ε a b h p q hε ha hbw hh hb c t+Real.exp (2*t)*potentialEnergy ε a b h p q hε ha hbw hh hb c := by
  rw [energy_decomposition,unit_sum]
  unfold clockKineticEnergy potentialEnergy
  ring

theorem unit_full_response (t : ℝ) :
    fullResponse ε a b h p q hε ha hbw hh hb c 1 1 1 t =
      clockKineticResponse ε a b h p q hε ha hbw hh hb c t+Real.exp (2*t)*potentialResponse ε a b h p q hε ha hbw hh hb c := by
  rw [response_decomposition,unit_sum]
  unfold clockKineticResponse potentialResponse
  ring

theorem clockKinetic_lower (t : ℝ) :
    -(1/(4*ε))*clockKineticEnergy ε a b h p q hε ha hbw hh hb c t ≤
      clockKineticResponse ε a b h p q hε ha hbw hh hb c t := by
  have h0 := (clock_energy_bounds ε a b h p q hε ha hbw hh hb c).1
  have h1 := (kinetic_bounds ε a b h p q hε ha hbw hh hb c 0).1
  have h2 := (kinetic_bounds ε a b h p q hε ha hbw hh hb c 1).1
  have h3 := (kinetic_bounds ε a b h p q hε ha hbw hh hb c 2).1
  have h4 := (kinetic_bounds ε a b h p q hε ha hbw hh hb c 3).1
  change 0 ≤ R 1 at h1
  change 0 ≤ R 2 at h2
  change 0 ≤ R 3 at h3
  change 0 ≤ R 4 at h4
  have hc : 0 ≤ 1/(4*ε) := by positivity
  have he : E 0/2 ≤ clockKineticEnergy ε a b h p q hε ha hbw hh hb c t := by
    have hs : 0 ≤ (E 1+E 2)/2 := by unfold factorEnergy; positivity
    have hg : 0 ≤ Real.exp (2*t)*(E 3+E 4)/2 := by unfold factorEnergy; positivity
    unfold clockKineticEnergy
    linarith
  have hr : -(1/(4*ε))*(E 0/2) ≤ clockKineticResponse ε a b h p q hε ha hbw hh hb c t := by
    have hg := mul_nonneg (Real.exp_pos (2*t)).le (add_nonneg h3 h4)
    unfold clockKineticResponse
    linarith
  exact (mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hc)).trans hr

#print axioms inputLift_embedding
#print axioms momentumLift_embedding
#print axioms lifted_momentum_graph
#print axioms energy_decomposition
#print axioms response_decomposition
#print axioms unit_full_energy
#print axioms unit_full_response
#print axioms clockKinetic_lower
end
end UnifiedTheory.Audit.KFCausalPairedSpanMixedClockHamiltonian
