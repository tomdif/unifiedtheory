/- The paired excitation and its actual pure-clock momentum lift into
the full completed charge-averaged Hamiltonian form. Their exact signed
response includes all eight factors. The clock/kinetic part has a
uniform lower bound; the potential response remains explicit. -/
import UnifiedTheory.Audit.KFCausalChargedPairFactorResponse
import UnifiedTheory.Audit.KFCausalChargedPairHamiltonianForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedPairHamiltonianResponse
noncomputable section
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight energyWeight_norm_square)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalChargedPairDomain (state output output_graph state_ne_zero)
open KFCausalChargedPairCharge (state_zeroSector state_orthogonal_fixed)
open KFCausalChargedPairClockMomentum (momentum factor momentum_graph factor_graph momentum_zeroSector)
open KFCausalChargedPairFactorResponse (factorEnergy factorRate clock_energy_bounds kinetic_bounds)
open KFCausalChargedPairHamiltonianForm (pairedLift pairedLift_embedding)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding energyOutput)
open KFCausalClockFloorAveragedHamiltonian (graphFormVector)
open KFCausalFixedCommonEnergyPairing

private theorem physical_sum (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) (r : Fin 8 → ℝ) :
    (∑ i : Fin 8, ‖energyWeight mass2 quartic vacuum t i‖^2*r i) =
      (r 0+r 1+r 2)/2+Real.exp (2*t)*((r 3+r 4)/2+mass2/2*r 5+quartic/4*r 6+vacuum*r 7) := by
  simp_rw [energyWeight_norm_square mass2 quartic vacuum t hm hq hv]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  ring!

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "f" => state ε a h hε ha hh
local notation "Bf" => momentum ε a h hε ha hh
local notation "u" => output ε a h hε ha hh hb modelDirections pointField
local notation "v" => factor ε a h hε ha hh hb modelDirections pointField
local notation "E" => factorEnergy ε a h hε ha hh hb
local notation "R" => factorRate ε a h hε ha hh hb

def momentumLift (mass2 quartic vacuum t : ℝ) : FormSpace ε hε h hh hb mass2 quartic vacuum t :=
  graphFormVector ε hε h hh hb mass2 quartic vacuum t
    (fixedLift ε h hε hh hb mass2 quartic vacuum t Bf
      (momentum_zeroSector ε a h hε ha hh) v
      (factor_graph ε a h hε ha hh hb modelDirections pointField))

theorem momentumLift_embedding (mass2 quartic vacuum t : ℝ) :
    embedding ε hε h hh hb mass2 quartic vacuum t
      (momentumLift ε a h hε ha hh hb mass2 quartic vacuum t) = Bf := rfl

theorem lifted_momentum_graph (mass2 quartic vacuum t : ℝ) :
    (embedding ε hε h hh hb mass2 quartic vacuum t
        (pairedLift ε a h hε ha hh hb mass2 quartic vacuum t),
      embedding ε hε h hh hb mass2 quartic vacuum t
        (momentumLift ε a h hε ha hh hb mass2 quartic vacuum t)) ∈ (pureMomentum ε hε h).graph :=
  momentum_graph ε a h hε ha hh

theorem pair_outside_neutralCompletedPairs (t : ℝ) :
    (pairedLift ε a h hε ha hh hb 1 1 1 t,momentumLift ε a h hε ha hh hb 1 1 1 t) ∉
      KFCausalNeutralResponseGraphClosure.completedPairs ε h hε hh hb t := by
  intro hz
  have hf := KFCausalNeutralSwapConstraint.completedPairs_input_fixed ε h hε hh hb t _ hz
  change f ∈ KFCausalChargedPlaneSwap.fixedSpace at hf
  have hi := state_orthogonal_fixed ε a h hε ha hh f hf
  exact state_ne_zero ε a h hε ha hh (inner_self_eq_zero.mp hi)

def fullEnergy (mass2 quartic vacuum t : ℝ) : ℝ :=
  ‖energyOutput ε hε h hh hb mass2 quartic vacuum t
    (pairedLift ε a h hε ha hh hb mass2 quartic vacuum t)‖^2

def fullResponse (mass2 quartic vacuum t : ℝ) : ℝ :=
  (-2/h)*(inner ℂ
    (energyOutput ε hε h hh hb mass2 quartic vacuum t
      (pairedLift ε a h hε ha hh hb mass2 quartic vacuum t))
    (energyOutput ε hε h hh hb mass2 quartic vacuum t
      (momentumLift ε a h hε ha hh hb mass2 quartic vacuum t))).im

theorem energy_decomposition (mass2 quartic vacuum t : ℝ) :
    fullEnergy ε a h hε ha hh hb mass2 quartic vacuum t =
      ∑ j : Fin 8, ‖energyWeight mass2 quartic vacuum t j‖^2*E j :=
  fixedLift_energy ε h hε hh hb mass2 quartic vacuum t f
    (state_zeroSector ε a h hε ha hh) u
    (output_graph ε a h hε ha hh hb modelDirections pointField)

theorem response_decomposition (mass2 quartic vacuum t : ℝ) :
    fullResponse ε a h hε ha hh hb mass2 quartic vacuum t =
      ∑ j : Fin 8, ‖energyWeight mass2 quartic vacuum t j‖^2*R j :=
  fixedLift_response ε h hε hh hb mass2 quartic vacuum t f
    (state_zeroSector ε a h hε ha hh) u
    (output_graph ε a h hε ha hh hb modelDirections pointField) Bf
    (momentum_zeroSector ε a h hε ha hh) v
    (factor_graph ε a h hε ha hh hb modelDirections pointField)

theorem physical_energy (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    fullEnergy ε a h hε ha hh hb mass2 quartic vacuum t =
      (E 0+E 1+E 2)/2+Real.exp (2*t)*((E 3+E 4)/2+mass2/2*E 5+quartic/4*E 6+vacuum*E 7) := by
  rw [energy_decomposition]
  exact physical_sum mass2 quartic vacuum t hm hq hv E

theorem physical_response (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    fullResponse ε a h hε ha hh hb mass2 quartic vacuum t =
      (R 0+R 1+R 2)/2+Real.exp (2*t)*((R 3+R 4)/2+mass2/2*R 5+quartic/4*R 6+vacuum*R 7) := by
  rw [response_decomposition]
  exact physical_sum mass2 quartic vacuum t hm hq hv R

def clockKineticEnergy (t : ℝ) : ℝ :=
  (E 0+E 1+E 2)/2+Real.exp (2*t)*(E 3+E 4)/2
def clockKineticResponse (t : ℝ) : ℝ :=
  (R 0+R 1+R 2)/2+Real.exp (2*t)*(R 3+R 4)/2
def potentialEnergy : ℝ := E 7+E 5/2+E 6/4
def potentialResponse : ℝ := R 7+R 5/2+R 6/4

theorem clockKinetic_lower (t : ℝ) :
    -(1/(4*ε))*clockKineticEnergy ε a h hε ha hh hb t ≤
      clockKineticResponse ε a h hε ha hh hb t := by
  have h0 := (clock_energy_bounds ε a h hε ha hh hb).1
  have h1 := (kinetic_bounds ε a h hε ha hh hb 0).1
  have h2 := (kinetic_bounds ε a h hε ha hh hb 1).1
  have h3 := (kinetic_bounds ε a h hε ha hh hb 2).1
  have h4 := (kinetic_bounds ε a h hε ha hh hb 3).1
  change 0 ≤ R 1 at h1
  change 0 ≤ R 2 at h2
  change 0 ≤ R 3 at h3
  change 0 ≤ R 4 at h4
  have hc : 0 ≤ 1/(4*ε) := by positivity
  have he : E 0/2 ≤ clockKineticEnergy ε a h hε ha hh hb t := by
    have hs : 0 ≤ (E 1+E 2)/2 := by unfold factorEnergy; positivity
    have hg : 0 ≤ Real.exp (2*t)*(E 3+E 4)/2 := by unfold factorEnergy; positivity
    unfold clockKineticEnergy
    linarith
  have hr : -(1/(4*ε))*(E 0/2) ≤ clockKineticResponse ε a h hε ha hh hb t := by
    have hg := mul_nonneg (Real.exp_pos (2*t)).le (add_nonneg h3 h4)
    unfold clockKineticResponse
    linarith
  exact (mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hc)).trans hr

theorem unit_full_energy (t : ℝ) :
    fullEnergy ε a h hε ha hh hb 1 1 1 t =
      clockKineticEnergy ε a h hε ha hh hb t+
        Real.exp (2*t)*potentialEnergy ε a h hε ha hh hb := by
  rw [physical_energy ε a h hε ha hh hb 1 1 1 t (by norm_num) (by norm_num) (by norm_num)]
  unfold clockKineticEnergy potentialEnergy
  ring

theorem unit_full_response (t : ℝ) :
    fullResponse ε a h hε ha hh hb 1 1 1 t =
      clockKineticResponse ε a h hε ha hh hb t+
        Real.exp (2*t)*potentialResponse ε a h hε ha hh hb := by
  rw [physical_response ε a h hε ha hh hb 1 1 1 t (by norm_num) (by norm_num) (by norm_num)]
  unfold clockKineticResponse potentialResponse
  ring

theorem fullResponse_lower (t : ℝ) :
    -(1/(4*ε))*clockKineticEnergy ε a h hε ha hh hb t+
      Real.exp (2*t)*potentialResponse ε a h hε ha hh hb ≤
        fullResponse ε a h hε ha hh hb 1 1 1 t := by
  rw [unit_full_response]
  exact add_le_add (clockKinetic_lower ε a h hε ha hh hb t) le_rfl

#print axioms momentumLift_embedding
#print axioms lifted_momentum_graph
#print axioms pair_outside_neutralCompletedPairs
#print axioms energy_decomposition
#print axioms response_decomposition
#print axioms physical_energy
#print axioms physical_response
#print axioms clockKinetic_lower
#print axioms unit_full_energy
#print axioms unit_full_response
#print axioms fullResponse_lower
end
end UnifiedTheory.Audit.KFCausalChargedPairHamiltonianResponse
