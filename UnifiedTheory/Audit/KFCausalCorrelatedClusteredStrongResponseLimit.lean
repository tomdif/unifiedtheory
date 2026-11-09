/- The actual full interacting form energy and response are strong
Hamiltonian pairings on the clustered limit. All original finite form
values converge. These identities do not assert a uniform relative bound. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredStrongHamiltonianLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredFormBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredStrongResponseLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredFormBounds (factorEnergy factorResponse)
open KFCausalCorrelatedClusteredStrongHamiltonianLimit (inputHamiltonian momentumHamiltonian strong_pairing)
open KFCausalCorrelatedClusteredAllSecondLimit (inputSeconds input_reverse_graph)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalFixedCommonEnergyPairing (fixedLift fixedLift_energy fixedLift_response)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
  (mass2 quartic vacuum t : ℝ)
local notation "hb₀" => original_strip ε h hε hb
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha
local notation "b" => KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a p hε hh ha
local notation "u" => KFCausalCorrelatedClusteredAllFactorLimit.output f ε h a p hε hh hb₀ ha
local notation "v" => KFCausalCorrelatedClusteredAllFactorLimit.momentumOutput f ε h a p hε hh hb₀ ha
local notation "hf" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState_zeroSector f ε h a p hε hh ha
local notation "hbf" => KFCausalCorrelatedClusteredPureMomentumLimit.momentum_zeroSector f ε h a p hε hh ha
local notation "hg" => KFCausalCorrelatedClusteredAllFactorLimit.output_graph f ε h a p hε hh hb₀ ha
local notation "hbg" => KFCausalCorrelatedClusteredAllFactorLimit.momentumOutput_graph f ε h a p hε hh hb₀ ha
local notation "c" => energyWeight mass2 quartic vacuum t

def fullEnergy : ℝ := ∑ j, ‖c j‖^2*factorEnergy f ε h a p hε hh hb₀ ha j
def fullResponse : ℝ := ∑ j, ‖c j‖^2*factorResponse f ε h a p hε hh hb₀ ha j

theorem energy_identity : fullEnergy f ε h a p hε hh ha hb mass2 quartic vacuum t =
    (inner ℂ (inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t) ψ).re := by
  have hp := KFCausalFixedStrongHamiltonian.averaged_pairing ε h hε hh hb₀ mass2 quartic vacuum t
    ψ hf u (inputSeconds f ε h a p hε hh ha hb) hg (input_reverse_graph f ε h a p hε hh ha hb)
    (fixedLift ε h hε hh hb₀ mass2 quartic vacuum t ψ hf u hg)
  exact (fixedLift_energy ε h hε hh hb₀ mass2 quartic vacuum t ψ hf u hg).symm.trans
    ((norm_sq_eq_re_inner (𝕜 := ℂ) _).trans (congrArg Complex.re hp))

theorem response_identity : fullResponse f ε h a p hε hh ha hb mass2 quartic vacuum t =
    (-2/h)*(inner ℂ (inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t) b).im := by
  have hp := KFCausalFixedStrongHamiltonian.averaged_pairing ε h hε hh hb₀ mass2 quartic vacuum t
    ψ hf u (inputSeconds f ε h a p hε hh ha hb) hg (input_reverse_graph f ε h a p hε hh ha hb)
    (fixedLift ε h hε hh hb₀ mass2 quartic vacuum t b hbf v hbg)
  exact (fixedLift_response ε h hε hh hb₀ mass2 quartic vacuum t ψ hf u hg b hbf v hbg).symm.trans
    (congrArg (fun z : ℂ => (-2/h)*z.im) hp)

theorem hamiltonian_momentum_response_identity :
    fullResponse f ε h a p hε hh ha hb mass2 quartic vacuum t =
      (-2/h)*(inner ℂ ψ (momentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t)).im := by
  rw [response_identity,strong_pairing]

theorem energy_tendsto :
    Tendsto (fun δ => ∑ j, ‖c j‖^2*
      ‖KFCausalCorrelatedClusteredPhysicalCauchy.finiteOutput f ε h a p hε hh hb₀ ha δ j‖^2)
      (𝓝[>] 0) (𝓝 (fullEnergy f ε h a p hε hh ha hb mass2 quartic vacuum t)) :=
  KFCausalCorrelatedClusteredFormBounds.weighted_energy_tendsto f ε h a p hε hh hb₀ ha (fun j => ‖c j‖^2)

theorem response_tendsto :
    Tendsto (fun δ => ∑ j, ‖c j‖^2*((-2/h)*(inner ℂ
      (KFCausalCorrelatedClusteredPhysicalCauchy.finiteOutput f ε h a p hε hh hb₀ ha δ j)
      (KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput f ε h a p hε hh hb₀ ha δ j)).im))
      (𝓝[>] 0) (𝓝 (fullResponse f ε h a p hε hh ha hb mass2 quartic vacuum t)) :=
  KFCausalCorrelatedClusteredFormBounds.weighted_response_tendsto f ε h a p hε hh hb₀ ha (fun j => ‖c j‖^2)

#print axioms energy_identity
#print axioms response_identity
#print axioms hamiltonian_momentum_response_identity
#print axioms energy_tendsto
#print axioms response_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredStrongResponseLimit
