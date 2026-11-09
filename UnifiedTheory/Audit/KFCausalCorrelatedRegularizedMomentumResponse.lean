/- Actual bounded pure-clock expectations along the full correlated Hamiltonian
trajectory. Their initial derivatives converge to the already identified full
strong commutator response. This is an iterated limit statement, not preservation
of Dom(BH), Dom(HB), or differentiation of an unbounded expectation in time. -/
import UnifiedTheory.Audit.KFCausalUnitaryMomentumCentralDifference
import UnifiedTheory.Audit.KFCausalCorrelatedHamiltonianDomainEvolution
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredStrongCommutatorResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedRegularizedMomentumResponse
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalClockFloorPureClockMomentum (pureGroup pureMomentum)
open KFCausalUnitaryMomentumCentralDifference
open KFCausalCorrelatedClusteredStrongHamiltonianLimit (inputHamiltonian)
open KFCausalCorrelatedClusteredStrongResponseLimit (fullResponse)
open KFCausalClockFloorAveragedEvolution (evolution evolution_initial)

def momentumApprox (ε : ℝ) (hε : 0 < ε) (h τ : ℝ) : Hilbert →L[ℂ] Hilbert :=
  central (pureGroup ε hε) h τ

theorem schrodinger_pairing (h : ℝ) (x y : Hilbert) :
    2*(inner ℂ ((-Complex.I*((1/h:ℝ):ℂ)) • x) y).re =
      (-2/h)*(inner ℂ x y).im := by
  simp only [inner_smul_left,map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal,
    neg_neg,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.mul_im]
  ring

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
  (mass2 quartic vacuum : ℝ)
local notation "hb₀" => KFCausalGaussianVacuumSquare.original_strip ε h hε hb
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha
local notation "b" => KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a p hε hh ha
local notation "U" => evolution ε hε h hh hb₀ mass2 quartic vacuum
local notation "A" => momentumApprox ε hε h
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

def expectation (s τ t : ℝ) : ℝ := (inner ℂ (U s t ψ) (A τ (U s t ψ))).re

def initialRate (s τ : ℝ) : ℝ :=
  (-2/h)*(inner ℂ (inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum s) (A τ ψ)).im

theorem initial_expectation_hasDerivAt (s τ : ℝ) :
    HasDerivAt (expectation f ε h a p hε hh ha hb mass2 quartic vacuum s τ)
      (initialRate f ε h a p hε hh ha hb mass2 quartic vacuum s τ) s := by
  have hd := expectation_hasDerivAt (pureGroup ε hε) h τ s (fun t => U s t ψ)
    (c • inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum s)
    (KFCausalCorrelatedHamiltonianDomainEvolution.input_initial_derivative
      f ε h a p hε hh ha hb mass2 quartic vacuum s)
  have he : U s s ψ = ψ := by
    change (U s s : Hilbert →L[ℂ] Hilbert) ψ = ψ
    rw [evolution_initial,ContinuousLinearMap.one_apply]
  simpa only [expectation,initialRate,momentumApprox,he,schrodinger_pairing] using hd

theorem momentumApprox_tendsto : Tendsto (fun τ => A τ ψ) (𝓝[≠] 0) (𝓝 b) :=
  central_tendsto (pureGroup ε hε) h hh ψ b
    (KFCausalCorrelatedClusteredPureMomentumLimit.limiting_graph f ε h a p hε hh ha)

theorem initialRate_tendsto (s : ℝ) :
    Tendsto (initialRate f ε h a p hε hh ha hb mass2 quartic vacuum s) (𝓝[≠] 0)
      (𝓝 (fullResponse f ε h a p hε hh ha hb mass2 quartic vacuum s)) := by
  rw [KFCausalCorrelatedClusteredStrongResponseLimit.response_identity]
  have hp := tendsto_const_nhds.inner (𝕜 := ℂ) (momentumApprox_tendsto f ε h a p hε hh ha)
    (x := inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum s)
  exact ((Complex.continuous_im.tendsto _).comp hp).const_mul (-2/h)

theorem initial_derivative_tendsto (s : ℝ) :
    Tendsto (fun τ => deriv (expectation f ε h a p hε hh ha hb mass2 quartic vacuum s τ) s)
      (𝓝[≠] 0) (𝓝 (fullResponse f ε h a p hε hh ha hb mass2 quartic vacuum s)) := by
  simpa only [(initial_expectation_hasDerivAt f ε h a p hε hh ha hb mass2 quartic vacuum s _).deriv]
    using initialRate_tendsto f ε h a p hε hh ha hb mass2 quartic vacuum s

theorem initial_value_tendsto (s : ℝ) :
    Tendsto (fun τ => expectation f ε h a p hε hh ha hb mass2 quartic vacuum s τ s)
      (𝓝[≠] 0) (𝓝 (inner ℂ ψ b).re) := by
  have he : U s s ψ = ψ := by
    change (U s s : Hilbert →L[ℂ] Hilbert) ψ = ψ
    rw [evolution_initial,ContinuousLinearMap.one_apply]
  have hp := tendsto_const_nhds.inner (𝕜 := ℂ)
    (momentumApprox_tendsto f ε h a p hε hh ha) (x := ψ)
  simpa only [expectation,he] using ((Complex.continuous_re.tendsto _).comp hp)

theorem forward_expectation_hasDerivAt (s t τ : ℝ) (hst : s ≤ t) :
    ∃ hx : U s t ψ ∈ (KFCausalClockFloorAveragedHamiltonian.hamiltonian
        ε hε h hh hb₀ mass2 quartic vacuum t).domain,
      HasDerivAt (expectation f ε h a p hε hh ha hb mass2 quartic vacuum s τ)
        ((-2/h)*(inner ℂ (KFCausalClockFloorAveragedHamiltonian.hamiltonian
          ε hε h hh hb₀ mass2 quartic vacuum t ⟨U s t ψ,hx⟩) (A τ (U s t ψ))).im) t := by
  obtain ⟨hx,hd⟩ := KFCausalCorrelatedHamiltonianDomainEvolution.input_forward_schrodinger
    f ε h a p hε hh ha hb mass2 quartic vacuum s t hst
  refine ⟨hx,?_⟩
  simpa only [expectation,momentumApprox,schrodinger_pairing] using
    expectation_hasDerivAt (pureGroup ε hε) h τ t (fun z => U s z ψ) _ hd

#print axioms schrodinger_pairing
#print axioms initial_expectation_hasDerivAt
#print axioms momentumApprox_tendsto
#print axioms initialRate_tendsto
#print axioms initial_derivative_tendsto
#print axioms initial_value_tendsto
#print axioms forward_expectation_hasDerivAt
end
end UnifiedTheory.Audit.KFCausalCorrelatedRegularizedMomentumResponse
