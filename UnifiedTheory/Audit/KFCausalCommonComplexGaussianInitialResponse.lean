/- For one common complex neutral source, initial derivatives of the
original bounded momentum expectations converge to the weighted full
Hamiltonian response, which obeys a uniform M/epsilon lower bound across
all nonnegative potential couplings. The actual initial Schrödinger
derivative and central-difference convergence come from the already
constructed finite-family domains. No unbounded expectation derivative,
evolved-family closure or exchange of limits is asserted. -/
import UnifiedTheory.Audit.KFCausalCommonComplexGaussianHamiltonianResponse
import UnifiedTheory.Audit.KFCausalCommonRealGaussianInitialResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexGaussianInitialResponse
noncomputable section
open Filter
open scoped Topology
open KFCausalCommonComplexQuarticJointAngular (source)
open KFCausalReciprocalNeutralHamiltonian (fullEnergy)
open KFCausalCommonRealGaussianInitialResponse (expectation initial_derivative_tendsto)
open KFCausalGaussianVacuumSquare (original_strip)

theorem common_complex_limit_lower : ∃ M : ℝ,0≤M ∧ ∀ (mass2 quartic vacuum : ℝ),
    0≤mass2→0≤quartic→0≤vacuum→
    ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C : Fin n → ℂ)
    (hε : 0<ε) (ha : ∀i,0<a i) (hh : h≠0) (hw : ∀i,1≤w i)
    (hb : |h|≤Real.pi*ε/3) (s : ℝ),
    ∃ R : ℝ,
      -(M/ε)*fullEnergy n ε h a w p C (fun _=>source A D) (fun _=>1)
        hε ha hh hw (original_strip ε h hε hb) mass2 quartic vacuum s≤R ∧
      Tendsto (fun τ=>deriv (expectation n ε h a w p C (fun _=>source A D) (fun _=>1)
        hε ha hh hw hb mass2 quartic vacuum s τ) s) (𝓝[≠] 0) (𝓝 R) := by
  obtain ⟨M,hM,hbound⟩ := KFCausalCommonComplexGaussianHamiltonianResponse.full_bound
  refine ⟨M,hM,?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C hε ha hh hw hb s
  exact ⟨_,hbound mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C
      hε ha hh hw (original_strip ε h hε hb) s,
    initial_derivative_tendsto n ε h a w p C (fun _=>source A D) (fun _=>1)
      hε ha hh hw hb mass2 quartic vacuum s⟩

theorem common_complex_eventually_lower : ∃ M : ℝ,0≤M ∧ ∀ (mass2 quartic vacuum : ℝ),
    0≤mass2→0≤quartic→0≤vacuum→
    ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C : Fin n → ℂ)
    (hε : 0<ε) (ha : ∀i,0<a i) (hh : h≠0) (hw : ∀i,1≤w i)
    (hb : |h|≤Real.pi*ε/3) (s δ : ℝ),0<δ→
    ∀ᶠ τ in 𝓝[≠] (0:ℝ),
      -(M/ε)*fullEnergy n ε h a w p C (fun _=>source A D) (fun _=>1)
        hε ha hh hw (original_strip ε h hε hb) mass2 quartic vacuum s-δ<
      deriv (expectation n ε h a w p C (fun _=>source A D) (fun _=>1)
        hε ha hh hw hb mass2 quartic vacuum s τ) s := by
  obtain ⟨M,hM,hbound⟩ := common_complex_limit_lower
  refine ⟨M,hM,?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C hε ha hh hw hb s δ hδ
  obtain ⟨R,hR,hlim⟩ := hbound mass2 quartic vacuum hmass hquartic hvacuum
    n ε h A D a w p C hε ha hh hw hb s
  exact hlim.eventually (eventually_gt_nhds (by linarith))

#print axioms common_complex_limit_lower
#print axioms common_complex_eventually_lower
end
end UnifiedTheory.Audit.KFCausalCommonComplexGaussianInitialResponse
