/- The enlarged joint-family energy and form response are the actual
strong-Hamiltonian pairings. This does not assume a uniform response
bound, a second Hamiltonian action on B psi, or a trajectory derivative. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralStrongHamiltonian
import UnifiedTheory.Audit.KFCausalReciprocalNeutralHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralStrongResponse
noncomputable section
open KFCausalReciprocalNeutralStrongHamiltonian (seconds hamiltonianOutput reverse_graph)
open KFCausalReciprocalNeutralHamiltonian (fullEnergy fullResponse)
open KFCausalGaussianVacuumSquare (original_strip)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "ψ" => KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw
local notation "Bψ" => KFCausalReciprocalNeutralSuperposition.momentum n ε h a w p C b P hε ha hh hw
local notation "u" => KFCausalReciprocalNeutralSuperposition.output n ε h a w p C b P hε ha hh hw hb₀
local notation "v" => KFCausalReciprocalNeutralSuperposition.momentumOutput n ε h a w p C b P hε ha hh hw hb₀
local notation "hf" => KFCausalReciprocalNeutralSuperposition.state_zeroSector n ε h a w p C b P hε ha hh hw
local notation "hg" => KFCausalReciprocalNeutralSuperposition.output_graph n ε h a w p C b P hε ha hh hw hb₀
local notation "hz" => reverse_graph n ε h a w p C b P hε ha hh hw hb

theorem energy_identity (mass2 quartic vacuum t : ℝ) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb₀ mass2 quartic vacuum t =
      (inner ℂ (hamiltonianOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t) ψ).re := by
  have hp := KFCausalFixedStrongHamiltonian.averaged_pairing ε h hε hh hb₀
    mass2 quartic vacuum t ψ hf u (seconds n ε h a w p C b P hε ha hh hw hb) hg hz
    (KFCausalFixedCommonEnergyPairing.fixedLift ε h hε hh hb₀ mass2 quartic vacuum t ψ hf u hg)
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).trans (congrArg Complex.re hp)

theorem response_identity (mass2 quartic vacuum t : ℝ) :
    fullResponse n ε h a w p C b P hε ha hh hw hb₀ mass2 quartic vacuum t =
      (-2/h)*(inner ℂ (hamiltonianOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t) Bψ).im := by
  have hp := KFCausalFixedStrongHamiltonian.averaged_pairing ε h hε hh hb₀
    mass2 quartic vacuum t ψ hf u (seconds n ε h a w p C b P hε ha hh hw hb) hg hz
    (KFCausalFixedCommonEnergyPairing.fixedLift ε h hε hh hb₀ mass2 quartic vacuum t Bψ
      (KFCausalReciprocalNeutralSuperposition.momentum_zeroSector n ε h a w p C b P hε ha hh hw) v
      (KFCausalReciprocalNeutralSuperposition.momentumOutput_graph n ε h a w p C b P hε ha hh hw hb₀))
  exact congrArg (fun z : ℂ => (-2/h)*z.im) hp

#print axioms energy_identity
#print axioms response_identity
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralStrongResponse
