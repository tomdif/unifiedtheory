/- Bounded pure-clock momentum expectations along the original nonautonomous
Hamiltonian evolution have actual initial derivatives. Their central-difference
limit is the original finite-family response. For common real neutral source,
P=1 and unit couplings, that limit obeys the proved 136/epsilon energy bound.
No unbounded expectation derivative or exchange of time and regulator limits
is asserted; the eventual estimate permits any strictly positive tolerance. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianHamiltonianResponse
import UnifiedTheory.Audit.KFCausalUnitaryMomentumCentralDifference
import UnifiedTheory.Audit.KFCausalClockFloorDomainSchrodinger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianInitialResponse
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorPureClockMomentum (pureGroup)
open KFCausalUnitaryMomentumCentralDifference (central central_tendsto expectation_hasDerivAt)
open KFCausalClockFloorAveragedEvolution (evolution evolution_initial)
open KFCausalReciprocalNeutralStrongHamiltonian (hamiltonianOutput hamiltonian_domain hamiltonian_action)
open KFCausalReciprocalNeutralHamiltonian (fullResponse fullEnergy)
open KFCausalGaussianVacuumSquare (original_strip)

def momentumApprox (ε : ℝ) (hε : 0 < ε) (h τ : ℝ) : Hilbert →L[ℂ] Hilbert :=
  central (pureGroup ε hε) h τ

private theorem schrodinger_pairing (h : ℝ) (x y : Hilbert) :
    2*(inner ℂ ((-Complex.I*((1/h:ℝ):ℂ)) • x) y).re = (-2/h)*(inner ℂ x y).im := by
  simp only [inner_smul_left,map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal,
    neg_neg,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.mul_im]
  ring

section Finite
variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "hb₀" => original_strip ε h hε hb
local notation "ψ" => KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw
local notation "Bψ" => KFCausalReciprocalNeutralSuperposition.momentum n ε h a w p C b P hε ha hh hw
local notation "U" => evolution ε hε h hh hb₀ mass2 quartic vacuum
local notation "A" => momentumApprox ε hε h
local notation "Hψ" => hamiltonianOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum

def expectation (s τ t : ℝ) : ℝ := (inner ℂ (U s t ψ) (A τ (U s t ψ))).re
def initialRate (s τ : ℝ) : ℝ := (-2/h)*(inner ℂ (Hψ s) (A τ ψ)).im

theorem initial_state_derivative (s : ℝ) :
    HasDerivAt (fun t => U s t ψ) ((-Complex.I*((1/h:ℝ):ℂ)) • Hψ s) s :=
  (KFCausalClockFloorDomainSchrodinger.initial_derivative_iff ε hε h hh hb₀
    mass2 quartic vacuum s ψ (Hψ s)).mpr
    ⟨hamiltonian_domain n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s,
      hamiltonian_action n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s⟩

theorem expectation_initial_derivative (s τ : ℝ) :
    HasDerivAt (expectation n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s τ)
      (initialRate n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s τ) s := by
  have hd := expectation_hasDerivAt (pureGroup ε hε) h τ s (fun t => U s t ψ) _
    (initial_state_derivative n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s)
  have he : U s s ψ=ψ := by
    change (U s s : Hilbert →L[ℂ] Hilbert) ψ=ψ
    rw [evolution_initial,ContinuousLinearMap.one_apply]
  simpa only [expectation,initialRate,momentumApprox,he,schrodinger_pairing] using hd

omit hb mass2 quartic vacuum in
theorem momentumApprox_tendsto : Tendsto (fun τ => A τ ψ) (𝓝[≠] 0) (𝓝 Bψ) :=
  central_tendsto (pureGroup ε hε) h hh ψ Bψ
    (KFCausalReciprocalNeutralSuperposition.momentum_graph n ε h a w p C b P hε ha hh hw)

theorem initial_derivative_tendsto (s : ℝ) :
    Tendsto (fun τ => deriv
      (expectation n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s τ) s)
      (𝓝[≠] 0) (𝓝 (fullResponse n ε h a w p C b P hε ha hh hw hb₀ mass2 quartic vacuum s)) := by
  simp only [(expectation_initial_derivative n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s _).deriv]
  rw [KFCausalReciprocalNeutralStrongResponse.response_identity]
  have hp := tendsto_const_nhds.inner (𝕜 := ℂ)
    (momentumApprox_tendsto n ε h a w p C b P hε ha hh hw) (x := Hψ s)
  exact ((Complex.continuous_im.tendsto _).comp hp).const_mul (-2/h)

theorem initial_value_tendsto (s : ℝ) :
    Tendsto (fun τ => expectation n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s τ s)
      (𝓝[≠] 0) (𝓝 (inner ℂ ψ Bψ).re) := by
  have he : U s s ψ=ψ := by
    change (U s s : Hilbert →L[ℂ] Hilbert) ψ=ψ
    rw [evolution_initial,ContinuousLinearMap.one_apply]
  have hp := tendsto_const_nhds.inner (𝕜 := ℂ)
    (momentumApprox_tendsto n ε h a w p C b P hε ha hh hw) (x := ψ)
  simpa only [expectation,he] using (Complex.continuous_re.tendsto _).comp hp
end Finite

theorem common_real_limit_lower (n : ℕ) (ε h B : ℝ) (a w p : Fin n → ℝ)
    (C : Fin n → ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
    (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ Real.pi*ε/3) (s : ℝ) :
    ∃ R : ℝ,
      -(136/ε)*fullEnergy n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1)
        hε ha hh hw (original_strip ε h hε hb) 1 1 1 s ≤ R ∧
      Tendsto (fun τ => deriv (expectation n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1)
        hε ha hh hw hb 1 1 1 s τ) s) (𝓝[≠] 0) (𝓝 R) :=
  ⟨_,KFCausalCommonRealGaussianHamiltonianResponse.full_bound n ε h B a w p C hε ha hh hw
      (original_strip ε h hε hb) s,
    initial_derivative_tendsto n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1) hε ha hh hw hb 1 1 1 s⟩

theorem common_real_eventually_lower (n : ℕ) (ε h B : ℝ) (a w p : Fin n → ℝ)
    (C : Fin n → ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
    (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ Real.pi*ε/3) (s δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ τ in 𝓝[≠] (0:ℝ),
      -(136/ε)*fullEnergy n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1)
        hε ha hh hw (original_strip ε h hε hb) 1 1 1 s-δ <
      deriv (expectation n ε h a w p C (fun _ => (B:ℂ)) (fun _ => 1)
        hε ha hh hw hb 1 1 1 s τ) s := by
  obtain ⟨R,hR,hlim⟩ := common_real_limit_lower n ε h B a w p C hε ha hh hw hb s
  exact hlim.eventually (eventually_gt_nhds (by linarith))

#print axioms initial_state_derivative
#print axioms expectation_initial_derivative
#print axioms momentumApprox_tendsto
#print axioms initial_derivative_tendsto
#print axioms initial_value_tendsto
#print axioms common_real_limit_lower
#print axioms common_real_eventually_lower
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianInitialResponse
