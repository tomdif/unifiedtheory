/- A nonzero actual state witnesses both independently rotated vacuum
square domains and the projected second vacuum-square graph. -/
import UnifiedTheory.Audit.KFCausalSingleGaussianNonzero
import UnifiedTheory.Audit.KFCausalSingleGaussianTwoAngleSquare
import UnifiedTheory.Audit.KFCausalSingleGaussianProjectedSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSingleGaussianMixedWitness
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorVacuumSquare (square)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalOrderedOperatorComposition (composition)
open KFCausalSingleGaussianSecondInput (state firstOutput first_graph)
open KFCausalSingleGaussianMixedSquare (original_strip)
open KFCausalSingleGaussianTwoAngleSquare (squareAt two_angle_domain)
open KFCausalSingleGaussianProjectedSquare (projectedOutput projected_square_graph)

theorem exists_nonzero_mixed_witness (ε h a : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (ha : 0 < a) (hb : |h| ≤ ε/10) :
    ∃ ψ u v : Hilbert, ψ ≠ 0 ∧ (ψ,u) ∈ (square ε hε h).graph ∧
      (zeroProjection h hh u,v) ∈ (square ε hε h).graph ∧
      ∀ θ φ : ℝ, ψ ∈ (composition (squareAt ε hε h hh φ) (squareAt ε hε h hh θ)).domain :=
  ⟨state ε h a hε hh ha,firstOutput ε h a hε hh ha (original_strip ε h hε hb),
    projectedOutput ε h a hε hh ha hb,
    KFCausalSingleGaussianNonzero.state_ne_zero ε h a hε hh ha,
    first_graph ε h a hε hh ha (original_strip ε h hε hb),
    projected_square_graph ε h a hε hh ha hb,
    two_angle_domain ε hε h hh a ha hb⟩

#print axioms exists_nonzero_mixed_witness
end
end UnifiedTheory.Audit.KFCausalSingleGaussianMixedWitness
