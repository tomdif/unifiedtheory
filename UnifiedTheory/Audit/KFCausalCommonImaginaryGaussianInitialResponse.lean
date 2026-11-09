/- For one common purely imaginary neutral source, initial derivatives of
the original bounded momentum expectations
converge to the weighted full Hamiltonian response, which obeys the same
136/epsilon lower bound for all nonnegative potential couplings. The actual
initial Schrödinger derivative and central-difference convergence come from
the already constructed finite-family domains. No unbounded expectation
derivative, evolved-family closure or exchange of limits is asserted. -/
import UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianHamiltonianResponse
import UnifiedTheory.Audit.KFCausalCommonRealGaussianInitialResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianInitialResponse
noncomputable section
open Filter
open scoped Topology
open KFCausalReciprocalNeutralHamiltonian (fullEnergy)
open KFCausalCommonRealGaussianInitialResponse (expectation initial_derivative_tendsto)
open KFCausalGaussianVacuumSquare (original_strip)

theorem common_imaginary_limit_lower (mass2 quartic vacuum : ℝ) (n : ℕ) (ε h D : ℝ)
    (a w p : Fin n → ℝ) (C : Fin n → ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
    (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ Real.pi*ε/3)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) (s : ℝ) :
    ∃ R : ℝ,
      -(136/ε)*fullEnergy n ε h a w p C (fun _ => (D:ℂ)*Complex.I) (fun _ => 1)
        hε ha hh hw (original_strip ε h hε hb) mass2 quartic vacuum s ≤ R ∧
      Tendsto (fun τ => deriv (expectation n ε h a w p C (fun _ => (D:ℂ)*Complex.I) (fun _ => 1)
        hε ha hh hw hb mass2 quartic vacuum s τ) s) (𝓝[≠] 0) (𝓝 R) :=
  ⟨_,KFCausalCommonImaginaryGaussianHamiltonianResponse.full_bound mass2 quartic vacuum
      n ε h D a w p C hε ha hh hw (original_strip ε h hε hb) hmass hquartic hvacuum s,
    initial_derivative_tendsto n ε h a w p C (fun _ => (D:ℂ)*Complex.I) (fun _ => 1)
      hε ha hh hw hb mass2 quartic vacuum s⟩

theorem common_imaginary_eventually_lower (mass2 quartic vacuum : ℝ) (n : ℕ) (ε h D : ℝ)
    (a w p : Fin n → ℝ) (C : Fin n → ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
    (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ Real.pi*ε/3)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) (s δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ τ in 𝓝[≠] (0:ℝ),
      -(136/ε)*fullEnergy n ε h a w p C (fun _ => (D:ℂ)*Complex.I) (fun _ => 1)
        hε ha hh hw (original_strip ε h hε hb) mass2 quartic vacuum s-δ <
      deriv (expectation n ε h a w p C (fun _ => (D:ℂ)*Complex.I) (fun _ => 1)
        hε ha hh hw hb mass2 quartic vacuum s τ) s := by
  obtain ⟨R,hR,hlim⟩ := common_imaginary_limit_lower mass2 quartic vacuum n ε h D a w p C
    hε ha hh hw hb hmass hquartic hvacuum s
  exact hlim.eventually (eventually_gt_nhds (by linarith))

#print axioms common_imaginary_limit_lower
#print axioms common_imaginary_eventually_lower
end
end UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianInitialResponse
