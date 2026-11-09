/- The previously proved packet-uniform form response is the actual
Hamiltonian/clock-momentum pairing. This needs H psi and the form domain
of B psi, not an unproved H B psi action or a trajectory derivative. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianStrongHamiltonian
import UnifiedTheory.Audit.KFCausalReciprocalGaussianUniformResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianStrongResponse
noncomputable section
open KFCausalReciprocalGaussianStrongHamiltonian (seconds output)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalReciprocalGaussianHamiltonian (fullEnergy fullResponse)

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "ψ" => KFCausalReciprocalGaussianCharge.state ε a h w hε ha hh (by linarith)
local notation "Bψ" => KFCausalReciprocalGaussianMomentum.momentum ε a h w hε ha hh hw
local notation "u" => KFCausalReciprocalGaussianMomentum.output ε a h w hε ha hh hw hb₀
local notation "v" => KFCausalReciprocalGaussianMomentum.momentumOutput ε a h w hε ha hh hw hb₀
local notation "hf" => KFCausalReciprocalGaussianCharge.state_zeroSector ε a h w hε ha hh (by linarith)
local notation "hg" => KFCausalReciprocalGaussianMomentum.output_graph ε a h w hε ha hh hw hb₀
local notation "hz" => KFCausalReciprocalGaussianStrongReduction.state_reverse_graphs ε a h w hε ha hh hw hb _ _
  (KFCausalReciprocalGaussianMatterSquare.linear_reverse_graph ε a h w hε ha hh hw hb)
  (KFCausalReciprocalGaussianMatterSquare.quadratic_reverse_graph ε a h w hε ha hh hw hb)

theorem energy_identity (mass2 quartic vacuum t : ℝ) :
    fullEnergy ε a h w hε ha hh hw hb₀ mass2 quartic vacuum t =
      (inner ℂ (output ε a h w hε ha hh hw hb mass2 quartic vacuum t) ψ).re := by
  have hp := KFCausalFixedStrongHamiltonian.averaged_pairing ε h hε hh hb₀
    mass2 quartic vacuum t ψ hf u (seconds ε a h w hε ha hh hw hb) hg hz
    (KFCausalFixedCommonEnergyPairing.fixedLift ε h hε hh hb₀ mass2 quartic vacuum t ψ hf u hg)
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).trans (congrArg Complex.re hp)

theorem response_identity (mass2 quartic vacuum t : ℝ) :
    fullResponse ε a h w hε ha hh hw hb₀ mass2 quartic vacuum t =
      (-2/h)*(inner ℂ (output ε a h w hε ha hh hw hb mass2 quartic vacuum t) Bψ).im := by
  have hp := KFCausalFixedStrongHamiltonian.averaged_pairing ε h hε hh hb₀
    mass2 quartic vacuum t ψ hf u (seconds ε a h w hε ha hh hw hb) hg hz
    (KFCausalFixedCommonEnergyPairing.fixedLift ε h hε hh hb₀ mass2 quartic vacuum t Bψ
      (KFCausalReciprocalGaussianMomentum.momentum_zeroSector ε a h w hε ha hh hw) v
      (KFCausalReciprocalGaussianMomentum.momentumOutput_graph ε a h w hε ha hh hw hb₀))
  exact congrArg (fun z : ℂ => (-2/h)*z.im) hp

theorem exists_uniform_strong_response (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε a w : ℝ, ∀ (hε : 0 < ε) (ha : 0 < a) (hw : 1 ≤ w)
      (hb : |h| ≤ Real.pi*ε/3) (t : ℝ),
      -((C+2)/ε)*(inner ℂ (output ε a h w hε ha hh hw hb 1 1 1 t)
        (KFCausalReciprocalGaussianCharge.state ε a h w hε ha hh (by linarith))).re ≤
      (-2/h)*(inner ℂ (output ε a h w hε ha hh hw hb 1 1 1 t)
        (KFCausalReciprocalGaussianMomentum.momentum ε a h w hε ha hh hw)).im := by
  obtain ⟨C,hC,hbound⟩ := KFCausalReciprocalGaussianUniformResponse.exists_uniform_full_response h hh
  refine ⟨C,hC,?_⟩
  intro ε a w hε ha hw hb t
  have hr := hbound ε a w hε ha hw (original_strip ε h hε hb) t
  rwa [energy_identity ε a h w hε ha hh hw hb,response_identity ε a h w hε ha hh hw hb] at hr

#print axioms energy_identity
#print axioms response_identity
#print axioms exists_uniform_strong_response
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianStrongResponse
