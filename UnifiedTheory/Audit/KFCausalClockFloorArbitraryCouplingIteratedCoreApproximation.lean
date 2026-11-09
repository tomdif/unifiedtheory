/- Unconditional Iterated Yosida Approximants, Three-Tier Second-Power Graph
Convergence, and Arbitrary-Coupling (k ∈ ℝ) Multi-Operator Clock-Core
Approximation and Shifted Resolvent Defect Synthesis:
1. Defines the iterated Yosida approximant
   iteratedYosida R a u := (a : ℂ) • R ((a : ℂ) • R u) = ((a ^ 2 : ℝ) : ℂ) • R (R u)
   for any positive operator A with shifted resolvent R(a), proving unconditional
   contractivity ‖iteratedYosida R a u‖ ≤ ‖u‖, domain error bound
   ‖iteratedYosida R a x - x‖ ≤ 2 * a⁻¹ * ‖A x‖, graph convergence
   (iteratedYosida (R (cutoff n)) (cutoff n) x, iteratedYosida (R (cutoff n)) (cutoff n) (A x))
   → (x, A x) in secondPowerGraph A, and simultaneous 3-tier convergence
   (x_n → x, A x_n → A x, A(A x_n) → A(A x)) for every (x, y) ∈ secondPowerGraph A.
2. Instantiates 3-tier second-power graph convergence and iterated Yosida
   approximation across all five clock-floor Hamiltonians T, P, G, S(t), and H(t)
   for arbitrary real couplings m, g, k, t ∈ ℝ.
3. Establishes for ALL real couplings m, g, k ∈ ℝ (including k ≤ 0, without
   requiring 0 < k) on commonOperatorDomain and unconditionalCoreDomain:
   - exact three-operator and two-operator shifted left-inverse cancellations,
   - exact static-Hamiltonian, static-residual, and residual-Hamiltonian shifted
     resolvent defect identities and norm bounds,
   - exact two-time shifted resolvent defect identities and Lipschitz bounds for
     both H(t) and S(t),
   - simultaneous 9-graph two-time convergence of the Gaussian sequence
     coreApproxSeq ε f in unconditionalCoreDomain together with termwise shifted
     resolvent defect identities at every index j : ℕ. -/
import UnifiedTheory.Audit.KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumUnconditionalCoreBridge

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorArbitraryCouplingIteratedCoreApproximation

noncomputable section

open Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorClockOperator (clockOperator)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalPositiveResolventBounds
  (Resolves point point_value resolvent_apply_norm_bound)
open KFCausalYosidaApproximation (scaled_resolvent_strong_limit)
open KFCausalClockFloorPotentialClockApproximation (cutoff cutoff_pos cutoff_tendsto)
open KFCausalClockFloorStaticResolventRadialCommutator
  (staticOperator_positive staticResolvent staticResolvent_resolves staticResolvent_left_inverse)
open KFCausalClockFloorSecondPowerOperatorCores
  (secondPowerGraph secondPowerDomain
   resolvent_commutes_on_domain scaled_resolvent_mem_secondPowerGraph
   scaled_resolvent_error_on_domain scaled_resolvent_output_error_on_secondPowerDomain
   secondPowerGraph_sequence_approximation)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (scaled_resolvent_norm_bound)
open KFCausalClockFloorUnconditionalThreeOperatorDecomposition
  (unconditional_three_operator_residual_graph
   unconditional_three_operator_hamiltonian_graph)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain common_domain_subset_hamiltonian
   common_domain_subset_residual common_domain_subset_growing)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (commonOperatorDomain_le_clockHalf_domain)
open KFCausalClockFloorGaussianGrowingTransport (action)
open KFCausalClockFloorGaussianGrowingApproximation (sequence_tendsto)
open KFCausalClockFloorGaussianClockCommutation
  (unconditional_clock_sequence_multi_operator_approximation)
open KFCausalClockFloorPositiveVacuumHamiltonianGaussianCore
  (unconditionalClockCore unconditional_gaussian_mem_clock_core_of_pos)
open KFCausalClockFloorPositiveVacuumUnconditionalCoreBridge
  (unconditionalCoreDomain growingClockCoreDomain coreApproxSeq
   coreDomains_le_growingClockCoreDomain)

/-! ### 1. Abstract Iterated Yosida Approximants and 3-Tier Second-Power Graph Convergence -/

section AbstractIteratedYosida

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The iterated Yosida approximant `J_a(u) := (a : ℂ) • R ((a : ℂ) • R u)`. -/
def iteratedYosida (R : H →L[ℂ] H) (a : ℝ) (u : H) : H :=
  (a : ℂ) • R ((a : ℂ) • R u)

/-- Algebraic identity `iteratedYosida R a u = ((a ^ 2 : ℝ) : ℂ) • R (R u)`. -/
theorem iteratedYosida_eq_sq_smul (R : H →L[ℂ] H) (a : ℝ) (u : H) :
    iteratedYosida R a u = ((a ^ 2 : ℝ) : ℂ) • R (R u) := by
  unfold iteratedYosida
  rw [map_smul, smul_smul, sq, Complex.ofReal_mul]

/-- Unconditional contractivity `‖iteratedYosida R a u‖ ≤ ‖u‖` for `0 < a` and `u : H`. -/
theorem iteratedYosida_norm_bound (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a) (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re) (u : H) :
    ‖iteratedYosida R a u‖ ≤ ‖u‖ :=
  (scaled_resolvent_norm_bound A R a ha hr hp ((a : ℂ) • R u)).trans
    (scaled_resolvent_norm_bound A R a ha hr hp u)

/-- Decomposition of the iterated Yosida approximation error:
`iteratedYosida R a u - u = (a : ℂ) • R ((a : ℂ) • R u - u) + ((a : ℂ) • R u - u)`. -/
theorem iteratedYosida_sub_eq (R : H →L[ℂ] H) (a : ℝ) (u : H) :
    iteratedYosida R a u - u =
      (a : ℂ) • R ((a : ℂ) • R u - u) + ((a : ℂ) • R u - u) := by
  unfold iteratedYosida
  rw [map_sub, smul_sub]
  abel

/-- Universal two-factor error bound `‖iteratedYosida R a u - u‖ ≤ 2 * ‖(a : ℂ) • R u - u‖`. -/
theorem iteratedYosida_sub_norm_le_two_mul (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a) (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re) (u : H) :
    ‖iteratedYosida R a u - u‖ ≤ 2 * ‖(a : ℂ) • R u - u‖ := by
  rw [iteratedYosida_sub_eq R a u]
  have htri := norm_add_le ((a : ℂ) • R ((a : ℂ) • R u - u)) ((a : ℂ) • R u - u)
  have hsc := scaled_resolvent_norm_bound A R a ha hr hp ((a : ℂ) • R u - u)
  linarith

/-- Quantitative domain error bound `‖iteratedYosida R a x - x‖ ≤ 2 * (a⁻¹ * ‖A x‖)` for `x : A.domain`. -/
theorem iteratedYosida_error_on_domain (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a) (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H)) (x : A.domain) :
    ‖iteratedYosida R a (x : H) - (x : H)‖ ≤ 2 * (a⁻¹ * ‖A x‖) :=
  (iteratedYosida_sub_norm_le_two_mul A R a ha hr hp (x : H)).trans
    (mul_le_mul_of_nonneg_left
      (scaled_resolvent_error_on_domain A R a ha hr hp hl x).2 (by norm_num))

/-- For every `x : A.domain`, `(iteratedYosida R a x, iteratedYosida R a (A x))` lies in `secondPowerGraph A`. -/
theorem iteratedYosida_mem_secondPowerGraph (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (x : A.domain) :
    (iteratedYosida R a (x : H), iteratedYosida R a (A x)) ∈ secondPowerGraph A := by
  have h1 := scaled_resolvent_mem_secondPowerGraph A R a hr hl x
  let u : A.domain := ⟨(a : ℂ) • R (x : H), LinearPMap.mem_domain_of_mem_graph h1.1⟩
  have hu : A u = (a : ℂ) • R (A x) :=
    A.mem_graph_snd_inj' (A.mem_graph u) h1.1 rfl
  have h2 := scaled_resolvent_mem_secondPowerGraph A R a hr hl u
  simpa only [iteratedYosida, u, hu] using h2

/-- Along `cutoff n = (n : ℝ) + 1`, for every `x : A.domain`, the iterated Yosida pair
`(iteratedYosida (R (cutoff n)) (cutoff n) x, iteratedYosida (R (cutoff n)) (cutoff n) (A x))`
lies in `secondPowerGraph A`, satisfies `‖iteratedYosida ... x - x‖ ≤ 2 * ((cutoff n)⁻¹ * ‖A x‖)`,
and converges to `(x, A x)`. -/
theorem iteratedYosida_sequence_approximation (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hd : Dense (A.domain : Set H))
    (hr : ∀ a, 0 < a → Resolves A (R a) a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ a, 0 < a → ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H))
    (x : A.domain) :
    (∀ n : ℕ,
      (iteratedYosida (R (cutoff n)) (cutoff n) (x : H),
        iteratedYosida (R (cutoff n)) (cutoff n) (A x)) ∈ secondPowerGraph A ∧
      ‖iteratedYosida (R (cutoff n)) (cutoff n) (x : H) - (x : H)‖ ≤
        2 * ((cutoff n)⁻¹ * ‖A x‖)) ∧
    Tendsto (fun n : ℕ =>
      (iteratedYosida (R (cutoff n)) (cutoff n) (x : H),
        iteratedYosida (R (cutoff n)) (cutoff n) (A x)))
      atTop (𝓝 ((x : H), A x)) := by
  have h (u : H) :
      Tendsto (fun n : ℕ => iteratedYosida (R (cutoff n)) (cutoff n) u) atTop (𝓝 u) := by
    have hI : Tendsto (fun n : ℕ => (cutoff n : ℂ) • R (cutoff n) u - u) atTop (𝓝 0) := by
      simpa only [Complex.coe_smul, sub_self] using
        ((scaled_resolvent_strong_limit A R hd hr hp hl u).comp cutoff_tendsto).sub_const u
    have hnorm0 : Tendsto (fun n : ℕ => 2 * ‖(cutoff n : ℂ) • R (cutoff n) u - u‖) atTop (𝓝 0) := by
      simpa only [norm_zero, mul_zero] using hI.norm.const_mul 2
    have hdiff0 : Tendsto (fun n : ℕ => ‖iteratedYosida (R (cutoff n)) (cutoff n) u - u‖) atTop (𝓝 0) :=
      squeeze_zero (fun _ => norm_nonneg _)
        (fun n => iteratedYosida_sub_norm_le_two_mul A (R (cutoff n)) (cutoff n)
          (cutoff_pos n) (hr (cutoff n) (cutoff_pos n)) hp u)
        hnorm0
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hdiff0
  refine ⟨fun n => ?_, (h (x : H)).prodMk_nhds (h (A x))⟩
  have hpos := cutoff_pos n
  exact ⟨iteratedYosida_mem_secondPowerGraph A (R (cutoff n)) (cutoff n)
      (hr (cutoff n) hpos) (hl (cutoff n) hpos) x,
    iteratedYosida_error_on_domain A (R (cutoff n)) (cutoff n) hpos
      (hr (cutoff n) hpos) hp (hl (cutoff n) hpos) x⟩

/-- Strong convergence `iteratedYosida (R (cutoff n)) (cutoff n) u → u` on all of `H`. -/
theorem iteratedYosida_strong_limit (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hd : Dense (A.domain : Set H))
    (hr : ∀ a, 0 < a → Resolves A (R a) a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ a, 0 < a → ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H))
    (u : H) :
    Tendsto (fun n : ℕ => iteratedYosida (R (cutoff n)) (cutoff n) u) atTop (𝓝 u) := by
  have hI : Tendsto (fun n : ℕ => (cutoff n : ℂ) • R (cutoff n) u - u) atTop (𝓝 0) := by
    simpa only [Complex.coe_smul, sub_self] using
      ((scaled_resolvent_strong_limit A R hd hr hp hl u).comp cutoff_tendsto).sub_const u
  have hnorm0 : Tendsto (fun n : ℕ => 2 * ‖(cutoff n : ℂ) • R (cutoff n) u - u‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hI.norm.const_mul 2
  have hdiff0 : Tendsto (fun n : ℕ => ‖iteratedYosida (R (cutoff n)) (cutoff n) u - u‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _)
      (fun n => iteratedYosida_sub_norm_le_two_mul A (R (cutoff n)) (cutoff n)
        (cutoff_pos n) (hr (cutoff n) (cutoff_pos n)) hp u)
      hnorm0
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hdiff0

/-- Three-tier error bounds on `secondPowerGraph A`: for `x : A.domain` with `hAx : A x ∈ A.domain`,
both `((a : ℂ) • R x - x)` and `((a : ℂ) • R (A x) - A x)` satisfy explicit `O(a⁻¹)` bounds,
and `((a : ℂ) • R (A x), (a : ℂ) • R (A ⟨A x, hAx⟩)) ∈ secondPowerGraph A`. -/
theorem secondPowerGraph_three_tier_error_bounds
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a) (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (x : A.domain) (hAx : A x ∈ A.domain) :
    ((a : ℂ) • R (x : H), (a : ℂ) • R (A x)) ∈ secondPowerGraph A ∧
    ((a : ℂ) • R (A x), (a : ℂ) • R (A ⟨A x, hAx⟩)) ∈ secondPowerGraph A ∧
    ‖(a : ℂ) • R (x : H) - (x : H)‖ ≤ a⁻¹ * ‖A x‖ ∧
    ‖(a : ℂ) • R (A x) - A x‖ ≤ a⁻¹ * ‖A ⟨A x, hAx⟩‖ :=
  ⟨scaled_resolvent_mem_secondPowerGraph A R a hr hl x,
   scaled_resolvent_mem_secondPowerGraph A R a hr hl ⟨A x, hAx⟩,
   (scaled_resolvent_error_on_domain A R a ha hr hp hl x).2,
   (scaled_resolvent_output_error_on_secondPowerDomain A R a ha hr hp hl x hAx).2⟩

/-- Simultaneous 3-tier convergence on `Dom(A²)`: for `x : A.domain` with `hAx : A x ∈ A.domain`,
`((cutoff n : ℂ) • R (cutoff n) x, (cutoff n : ℂ) • R (cutoff n) (A x), (cutoff n : ℂ) • R (cutoff n) (A ⟨A x, hAx⟩))`
converges to `(x, A x, A ⟨A x, hAx⟩)` with `O((n + 1)⁻¹)` error bounds on Tiers 0 and 1. -/
theorem secondPowerGraph_three_tier_sequence_convergence
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hd : Dense (A.domain : Set H))
    (hr : ∀ a, 0 < a → Resolves A (R a) a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ a, 0 < a → ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H))
    (x : A.domain) (hAx : A x ∈ A.domain) :
    (∀ n : ℕ,
      ((cutoff n : ℂ) • R (cutoff n) (x : H),
        (cutoff n : ℂ) • R (cutoff n) (A x)) ∈ secondPowerGraph A ∧
      ((cutoff n : ℂ) • R (cutoff n) (A x),
        (cutoff n : ℂ) • R (cutoff n) (A ⟨A x, hAx⟩)) ∈ secondPowerGraph A ∧
      ‖(cutoff n : ℂ) • R (cutoff n) (x : H) - (x : H)‖ ≤ (cutoff n)⁻¹ * ‖A x‖ ∧
      ‖(cutoff n : ℂ) • R (cutoff n) (A x) - A x‖ ≤ (cutoff n)⁻¹ * ‖A ⟨A x, hAx⟩‖) ∧
    Tendsto (fun n : ℕ =>
      ((cutoff n : ℂ) • R (cutoff n) (x : H),
        ((cutoff n : ℂ) • R (cutoff n) (A x),
          (cutoff n : ℂ) • R (cutoff n) (A ⟨A x, hAx⟩))))
      atTop (𝓝 ((x : H), (A x, A ⟨A x, hAx⟩))) := by
  have hs0 := secondPowerGraph_sequence_approximation A R hd hr hp hl x
  have hs1 := secondPowerGraph_sequence_approximation A R hd hr hp hl ⟨A x, hAx⟩
  refine ⟨fun n => ?_, ?_⟩
  · have hpos := cutoff_pos n
    exact secondPowerGraph_three_tier_error_bounds A (R (cutoff n)) (cutoff n) hpos
      (hr (cutoff n) hpos) hp (hl (cutoff n) hpos) x hAx
  · have h0 : Tendsto (fun n : ℕ => (cutoff n : ℂ) • R (cutoff n) (x : H)) atTop (𝓝 (x : H)) :=
      (continuous_fst.tendsto ((x : H), A x)).comp hs0.2
    exact h0.prodMk_nhds hs1.2

end AbstractIteratedYosida

/-! ### 2. Concrete 3-Tier Second-Power Graph Convergence for `T`, `P`, `G`, `S(t)`, and `H(t)` -/

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "AD" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => staticResolvent ε hε h hb hh
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k

private theorem static_selfAdjoint : IsSelfAdjoint T :=
  KFCausalRealMultiplierSelfAdjoint.realPullback_selfAdjoint
    KFCausalChargeTransverseSplit.dualPhysical
    (KFCausalClockFloorStaticMultiplierForm.symbol ε h)
    (KFCausalClockFloorStaticMultiplierForm.symbol_continuous ε hε h).measurable

/-- Simultaneous 3-tier Yosida convergence on `Dom(T²)` for all `x : (T).domain` with `T x ∈ (T).domain`. -/
theorem static_secondPowerGraph_three_tier_convergence
    (x : (T).domain) (hTx : T x ∈ (T).domain) :
    (∀ n : ℕ,
      ((cutoff n : ℂ) • RT (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RT (cutoff n) (T x)) ∈ secondPowerGraph T ∧
      ((cutoff n : ℂ) • RT (cutoff n) (T x),
        (cutoff n : ℂ) • RT (cutoff n) (T ⟨T x, hTx⟩)) ∈ secondPowerGraph T ∧
      ‖(cutoff n : ℂ) • RT (cutoff n) (x : Hilbert) - (x : Hilbert)‖ ≤ (cutoff n)⁻¹ * ‖T x‖ ∧
      ‖(cutoff n : ℂ) • RT (cutoff n) (T x) - T x‖ ≤ (cutoff n)⁻¹ * ‖T ⟨T x, hTx⟩‖) ∧
    Tendsto (fun n : ℕ =>
      ((cutoff n : ℂ) • RT (cutoff n) (x : Hilbert),
        ((cutoff n : ℂ) • RT (cutoff n) (T x),
          (cutoff n : ℂ) • RT (cutoff n) (T ⟨T x, hTx⟩))))
      atTop (𝓝 ((x : Hilbert), (T x, T ⟨T x, hTx⟩))) :=
  secondPowerGraph_three_tier_sequence_convergence T RT
    (static_selfAdjoint ε hε h).dense_domain
    (staticResolvent_resolves ε hε h hb hh)
    (staticOperator_positive ε hε h)
    (staticResolvent_left_inverse ε hε h hb hh) x hTx

/-- Simultaneous 3-tier Yosida convergence on `Dom(P²)` for all real `m, g, k`. -/
theorem potential_secondPowerGraph_three_tier_convergence
    (x : (P).domain) (hPx : P x ∈ (P).domain) :
    (∀ n : ℕ,
      ((cutoff n : ℂ) • RP (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RP (cutoff n) (P x)) ∈ secondPowerGraph P ∧
      ((cutoff n : ℂ) • RP (cutoff n) (P x),
        (cutoff n : ℂ) • RP (cutoff n) (P ⟨P x, hPx⟩)) ∈ secondPowerGraph P ∧
      ‖(cutoff n : ℂ) • RP (cutoff n) (x : Hilbert) - (x : Hilbert)‖ ≤ (cutoff n)⁻¹ * ‖P x‖ ∧
      ‖(cutoff n : ℂ) • RP (cutoff n) (P x) - P x‖ ≤ (cutoff n)⁻¹ * ‖P ⟨P x, hPx⟩‖) ∧
    Tendsto (fun n : ℕ =>
      ((cutoff n : ℂ) • RP (cutoff n) (x : Hilbert),
        ((cutoff n : ℂ) • RP (cutoff n) (P x),
          (cutoff n : ℂ) • RP (cutoff n) (P ⟨P x, hPx⟩))))
      atTop (𝓝 ((x : Hilbert), (P x, P ⟨P x, hPx⟩))) :=
  secondPowerGraph_three_tier_sequence_convergence P RP
    (KFCausalClosedGraphForm.hamiltonian_dense PD)
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (KFCausalClosedGraphForm.hamiltonian_positive PD)
    (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k) x hPx

/-- Simultaneous 3-tier Yosida convergence on `Dom(G²)` for all real `m, g, k`. -/
theorem growing_secondPowerGraph_three_tier_convergence
    (x : (G).domain) (hGx : G x ∈ (G).domain) :
    (∀ n : ℕ,
      ((cutoff n : ℂ) • RG (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RG (cutoff n) (G x)) ∈ secondPowerGraph G ∧
      ((cutoff n : ℂ) • RG (cutoff n) (G x),
        (cutoff n : ℂ) • RG (cutoff n) (G ⟨G x, hGx⟩)) ∈ secondPowerGraph G ∧
      ‖(cutoff n : ℂ) • RG (cutoff n) (x : Hilbert) - (x : Hilbert)‖ ≤ (cutoff n)⁻¹ * ‖G x‖ ∧
      ‖(cutoff n : ℂ) • RG (cutoff n) (G x) - G x‖ ≤ (cutoff n)⁻¹ * ‖G ⟨G x, hGx⟩‖) ∧
    Tendsto (fun n : ℕ =>
      ((cutoff n : ℂ) • RG (cutoff n) (x : Hilbert),
        ((cutoff n : ℂ) • RG (cutoff n) (G x),
          (cutoff n : ℂ) • RG (cutoff n) (G ⟨G x, hGx⟩))))
      atTop (𝓝 ((x : Hilbert), (G x, G ⟨G x, hGx⟩))) :=
  secondPowerGraph_three_tier_sequence_convergence G RG
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_dense ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) x hGx

/-- Simultaneous 3-tier Yosida convergence on `Dom(S(t)²)` for all real `m, g, k, t`. -/
theorem residual_secondPowerGraph_three_tier_convergence
    (t : ℝ) (x : (S t).domain) (hSx : S t x ∈ (S t).domain) :
    (∀ n : ℕ,
      ((cutoff n : ℂ) • RS t (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RS t (cutoff n) (S t x)) ∈ secondPowerGraph (S t) ∧
      ((cutoff n : ℂ) • RS t (cutoff n) (S t x),
        (cutoff n : ℂ) • RS t (cutoff n) (S t ⟨S t x, hSx⟩)) ∈ secondPowerGraph (S t) ∧
      ‖(cutoff n : ℂ) • RS t (cutoff n) (x : Hilbert) - (x : Hilbert)‖ ≤ (cutoff n)⁻¹ * ‖S t x‖ ∧
      ‖(cutoff n : ℂ) • RS t (cutoff n) (S t x) - S t x‖ ≤ (cutoff n)⁻¹ * ‖S t ⟨S t x, hSx⟩‖) ∧
    Tendsto (fun n : ℕ =>
      ((cutoff n : ℂ) • RS t (cutoff n) (x : Hilbert),
        ((cutoff n : ℂ) • RS t (cutoff n) (S t x),
          (cutoff n : ℂ) • RS t (cutoff n) (S t ⟨S t x, hSx⟩))))
      atTop (𝓝 ((x : Hilbert), (S t x, S t ⟨S t x, hSx⟩))) :=
  secondPowerGraph_three_tier_sequence_convergence (S t) (RS t)
    (KFCausalClosedGraphForm.hamiltonian_dense (SD t))
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
    (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t) x hSx

/-- Simultaneous 3-tier Yosida convergence on `Dom(H(t)²)` for all real `m, g, k, t`. -/
theorem hamiltonian_secondPowerGraph_three_tier_convergence
    (t : ℝ) (x : (H t).domain) (hHx : H t x ∈ (H t).domain) :
    (∀ n : ℕ,
      ((cutoff n : ℂ) • RH t (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RH t (cutoff n) (H t x)) ∈ secondPowerGraph (H t) ∧
      ((cutoff n : ℂ) • RH t (cutoff n) (H t x),
        (cutoff n : ℂ) • RH t (cutoff n) (H t ⟨H t x, hHx⟩)) ∈ secondPowerGraph (H t) ∧
      ‖(cutoff n : ℂ) • RH t (cutoff n) (x : Hilbert) - (x : Hilbert)‖ ≤ (cutoff n)⁻¹ * ‖H t x‖ ∧
      ‖(cutoff n : ℂ) • RH t (cutoff n) (H t x) - H t x‖ ≤ (cutoff n)⁻¹ * ‖H t ⟨H t x, hHx⟩‖) ∧
    Tendsto (fun n : ℕ =>
      ((cutoff n : ℂ) • RH t (cutoff n) (x : Hilbert),
        ((cutoff n : ℂ) • RH t (cutoff n) (H t x),
          (cutoff n : ℂ) • RH t (cutoff n) (H t ⟨H t x, hHx⟩))))
      atTop (𝓝 ((x : Hilbert), (H t x, H t ⟨H t x, hHx⟩))) :=
  secondPowerGraph_three_tier_sequence_convergence (H t) (RH t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_dense ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) x hHx

/-- Unconditional iterated-Yosida sequence approximation in `secondPowerGraph (H t)`
for every `x : (H t).domain` and arbitrary real couplings `m, g, k, t`. -/
theorem hamiltonian_iteratedYosida_sequence_approximation
    (t : ℝ) (x : (H t).domain) :
    (∀ n : ℕ,
      (iteratedYosida (RH t (cutoff n)) (cutoff n) (x : Hilbert),
        iteratedYosida (RH t (cutoff n)) (cutoff n) (H t x)) ∈ secondPowerGraph (H t) ∧
      ‖iteratedYosida (RH t (cutoff n)) (cutoff n) (x : Hilbert) - (x : Hilbert)‖ ≤
        2 * ((cutoff n)⁻¹ * ‖H t x‖)) ∧
    Tendsto (fun n : ℕ =>
      (iteratedYosida (RH t (cutoff n)) (cutoff n) (x : Hilbert),
        iteratedYosida (RH t (cutoff n)) (cutoff n) (H t x)))
      atTop (𝓝 ((x : Hilbert), H t x)) :=
  iteratedYosida_sequence_approximation (H t) (RH t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_dense ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) x

/-! ### 3. Arbitrary-Coupling (`k ∈ ℝ`) Shifted Resolvent Defects, Two-Time Continuity, and 9-Graph Clock-Core Approximation -/

/-- Unconditionally for ALL real couplings `m, g, k, t` and `0 < a`, every
`x ∈ commonOperatorDomain` satisfies `RH t a (T x + exp(2t) • (K x + P x) + a • x) = x`. -/
theorem unconditional_common_three_operator_left_inverse_cancel
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    RH t a (T ⟨x, hx.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) + a • x) = x := by
  let xH : (H t).domain := ⟨x, common_domain_subset_hamiltonian ε hε h hh hb m g k t hx⟩
  have hH : H t xH = T ⟨x, hx.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) :=
    (H t).mem_graph_snd_inj' ((H t).mem_graph xH)
      (unconditional_three_operator_hamiltonian_graph
        ε hε h hh hb m g k t x (T ⟨x, hx.1.1.1⟩) (K ⟨x, hx.1.1.2⟩) (P ⟨x, hx.1.2⟩)
        ((T).mem_graph ⟨x, hx.1.1.1⟩) ((K).mem_graph ⟨x, hx.1.1.2⟩)
        ((P).mem_graph ⟨x, hx.1.2⟩) hx.2) rfl
  rw [← hH]
  exact KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha xH

/-- Unconditionally for ALL real couplings `m, g, k, t` and `0 < a`, every
`x ∈ commonOperatorDomain` satisfies `RS t a (T x + exp(2t) • P x + a • x) = x`. -/
theorem unconditional_common_residual_two_operator_left_inverse_cancel
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    RS t a (T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ + a • x) = x := by
  let xS : (S t).domain := ⟨x, common_domain_subset_residual ε hε h hh hb m g k t hx⟩
  have hS : S t xS = T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ :=
    (S t).mem_graph_snd_inj' ((S t).mem_graph xS)
      (unconditional_three_operator_residual_graph
        ε hε h hh hb m g k t x (T ⟨x, hx.1.1.1⟩) (P ⟨x, hx.1.2⟩)
        ((T).mem_graph ⟨x, hx.1.1.1⟩) ((P).mem_graph ⟨x, hx.1.2⟩) hx.2) rfl
  rw [← hS]
  exact KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha xS

/-- Unconditionally for ALL real couplings `m, g, k, t` and `0 < a`, every
`x ∈ commonOperatorDomain` satisfies
`x - RH t a (T x + a • x) = exp(2t) • RH t a (K x + P x)`. -/
theorem unconditional_common_hamiltonian_static_shifted_resolvent_defect
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    x - RH t a (T ⟨x, hx.1.1.1⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • RH t a (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) := by
  have hleft := unconditional_common_three_operator_left_inverse_cancel
    ε hε h hh hb m g k t a ha x hx
  have hsub : (T ⟨x, hx.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) + a • x) -
      (T ⟨x, hx.1.1.1⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) := by abel
  calc
    x - RH t a (T ⟨x, hx.1.1.1⟩ + a • x) =
        RH t a (T ⟨x, hx.1.1.1⟩ +
          (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) + a • x) -
          RH t a (T ⟨x, hx.1.1.1⟩ + a • x) := by rw [hleft]
    _ = RH t a ((T ⟨x, hx.1.1.1⟩ +
          (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) + a • x) -
          (T ⟨x, hx.1.1.1⟩ + a • x)) := (map_sub (RH t a) _ _).symm
    _ = RH t a ((Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩)) := by rw [hsub]
    _ = (Real.exp (2 * t) : ℂ) • RH t a (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) :=
        map_smul (RH t a) _ _

/-- Unconditionally for ALL real couplings `m, g, k, t` and `0 < a`, every
`x ∈ commonOperatorDomain` satisfies
`x - RS t a (T x + a • x) = exp(2t) • RS t a (P x)`. -/
theorem unconditional_common_residual_static_shifted_resolvent_defect
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    x - RS t a (T ⟨x, hx.1.1.1⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • RS t a (P ⟨x, hx.1.2⟩) := by
  have hleft := unconditional_common_residual_two_operator_left_inverse_cancel
    ε hε h hh hb m g k t a ha x hx
  have hsub : (T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ + a • x) -
      (T ⟨x, hx.1.1.1⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ := by abel
  calc
    x - RS t a (T ⟨x, hx.1.1.1⟩ + a • x) =
        RS t a (T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ + a • x) -
          RS t a (T ⟨x, hx.1.1.1⟩ + a • x) := by rw [hleft]
    _ = RS t a ((T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ + a • x) -
          (T ⟨x, hx.1.1.1⟩ + a • x)) := (map_sub (RS t a) _ _).symm
    _ = RS t a ((Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩) := by rw [hsub]
    _ = (Real.exp (2 * t) : ℂ) • RS t a (P ⟨x, hx.1.2⟩) := map_smul (RS t a) _ _

/-- Unconditionally for ALL real couplings `m, g, k, t` and `0 < a`, every
`x ∈ commonOperatorDomain` satisfies
`x - RH t a (T x + exp(2t) • P x + a • x) = exp(2t) • RH t a (K x)`. -/
theorem unconditional_common_hamiltonian_residual_shifted_resolvent_defect
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    x - RH t a (T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • RH t a (K ⟨x, hx.1.1.2⟩) := by
  have hleft := unconditional_common_three_operator_left_inverse_cancel
    ε hε h hh hb m g k t a ha x hx
  have hsub : (T ⟨x, hx.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) + a • x) -
      (T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • K ⟨x, hx.1.1.2⟩ := by
    rw [smul_add]
    abel
  calc
    x - RH t a (T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ + a • x) =
        RH t a (T ⟨x, hx.1.1.1⟩ +
          (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) + a • x) -
          RH t a (T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ + a • x) := by rw [hleft]
    _ = RH t a ((T ⟨x, hx.1.1.1⟩ +
          (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) + a • x) -
          (T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ + a • x)) :=
        (map_sub (RH t a) _ _).symm
    _ = RH t a ((Real.exp (2 * t) : ℂ) • K ⟨x, hx.1.1.2⟩) := by rw [hsub]
    _ = (Real.exp (2 * t) : ℂ) • RH t a (K ⟨x, hx.1.1.2⟩) := map_smul (RH t a) _ _

/-- Unconditional norm bound `‖x - RH t a (T x + a • x)‖ ≤ a⁻¹ * exp(2t) * (‖K x‖ + ‖P x‖)`
on `commonOperatorDomain` for all real `m, g, k, t`. -/
theorem unconditional_common_hamiltonian_static_shifted_resolvent_defect_norm_le
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    ‖x - RH t a (T ⟨x, hx.1.1.1⟩ + a • x)‖ ≤
      a⁻¹ * Real.exp (2 * t) * (‖K ⟨x, hx.1.1.2⟩‖ + ‖P ⟨x, hx.1.2⟩‖) := by
  rw [unconditional_common_hamiltonian_static_shifted_resolvent_defect
      ε hε h hh hb m g k t a ha x hx,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (2 * t))]
  have h1 := KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_norm_le
    ε hε h hh hb m g k t a ha (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩)
  have h2 : a⁻¹ * ‖K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩‖ ≤
      a⁻¹ * (‖K ⟨x, hx.1.1.2⟩‖ + ‖P ⟨x, hx.1.2⟩‖) :=
    mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.mpr ha.le)
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos (2 * t)).le
  linarith

/-- Unconditional norm bound `‖x - RS t a (T x + a • x)‖ ≤ a⁻¹ * exp(2t) * ‖P x‖`
on `commonOperatorDomain` for all real `m, g, k, t`. -/
theorem unconditional_common_residual_static_shifted_resolvent_defect_norm_le
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    ‖x - RS t a (T ⟨x, hx.1.1.1⟩ + a • x)‖ ≤
      a⁻¹ * Real.exp (2 * t) * ‖P ⟨x, hx.1.2⟩‖ := by
  rw [unconditional_common_residual_static_shifted_resolvent_defect
      ε hε h hh hb m g k t a ha x hx,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (2 * t))]
  have h1 := KFCausalClockFloorResidualResolventRadialRootRegularity.residual_resolvent_norm_le
    ε hε h hh hb m g k t a ha (P ⟨x, hx.1.2⟩)
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (2 * t)).le
  linarith

/-- Unconditional norm bound `‖x - RH t a (T x + exp(2t) • P x + a • x)‖ ≤ a⁻¹ * exp(2t) * ‖K x‖`
on `commonOperatorDomain` for all real `m, g, k, t`. -/
theorem unconditional_common_hamiltonian_residual_shifted_resolvent_defect_norm_le
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    ‖x - RH t a (T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ + a • x)‖ ≤
      a⁻¹ * Real.exp (2 * t) * ‖K ⟨x, hx.1.1.2⟩‖ := by
  rw [unconditional_common_hamiltonian_residual_shifted_resolvent_defect
      ε hε h hh hb m g k t a ha x hx,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (2 * t))]
  have h1 := KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_norm_le
    ε hε h hh hb m g k t a ha (K ⟨x, hx.1.1.2⟩)
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (2 * t)).le
  linarith

/-- Unconditional two-time Hamiltonian difference identity on `commonOperatorDomain`
for all real couplings `m, g, k` and times `s, t`:
`H t x - H s x = ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • (K x + P x)`. -/
theorem unconditional_common_two_time_hamiltonian_diff_eq
    (s t : ℝ) (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    let hxt : x ∈ (H t).domain := common_domain_subset_hamiltonian ε hε h hh hb m g k t hx
    let hxs : x ∈ (H s).domain := common_domain_subset_hamiltonian ε hε h hh hb m g k s hx
    H t ⟨x, hxt⟩ - H s ⟨x, hxs⟩ =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) := by
  intro hxt hxs
  have hHt : H t ⟨x, hxt⟩ = T ⟨x, hx.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) :=
    (H t).mem_graph_snd_inj' ((H t).mem_graph ⟨x, hxt⟩)
      (unconditional_three_operator_hamiltonian_graph
        ε hε h hh hb m g k t x (T ⟨x, hx.1.1.1⟩) (K ⟨x, hx.1.1.2⟩) (P ⟨x, hx.1.2⟩)
        ((T).mem_graph ⟨x, hx.1.1.1⟩) ((K).mem_graph ⟨x, hx.1.1.2⟩)
        ((P).mem_graph ⟨x, hx.1.2⟩) hx.2) rfl
  have hHs : H s ⟨x, hxs⟩ = T ⟨x, hx.1.1.1⟩ +
      (Real.exp (2 * s) : ℂ) • (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) :=
    (H s).mem_graph_snd_inj' ((H s).mem_graph ⟨x, hxs⟩)
      (unconditional_three_operator_hamiltonian_graph
        ε hε h hh hb m g k s x (T ⟨x, hx.1.1.1⟩) (K ⟨x, hx.1.1.2⟩) (P ⟨x, hx.1.2⟩)
        ((T).mem_graph ⟨x, hx.1.1.1⟩) ((K).mem_graph ⟨x, hx.1.1.2⟩)
        ((P).mem_graph ⟨x, hx.1.2⟩) hx.2) rfl
  rw [hHt, hHs, Complex.ofReal_sub, sub_smul]
  abel

/-- Unconditional two-time shifted resolvent defect identity on `commonOperatorDomain`
for all real couplings `m, g, k` and times `s, t`:
`x - RH t a (H s x + a • x) = ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • RH t a (K x + P x)`. -/
theorem unconditional_common_two_time_shifted_resolvent_defect_eq
    (s t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    let hxs : x ∈ (H s).domain := common_domain_subset_hamiltonian ε hε h hh hb m g k s hx
    x - RH t a (H s ⟨x, hxs⟩ + a • x) =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
        RH t a (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) := by
  intro hxs
  let hxt : x ∈ (H t).domain := common_domain_subset_hamiltonian ε hε h hh hb m g k t hx
  have hlinv : RH t a (H t ⟨x, hxt⟩ + a • x) = x :=
    KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha ⟨x, hxt⟩
  have hsub : (H t ⟨x, hxt⟩ + a • x) - (H s ⟨x, hxs⟩ + a • x) =
      H t ⟨x, hxt⟩ - H s ⟨x, hxs⟩ := by abel
  calc
    x - RH t a (H s ⟨x, hxs⟩ + a • x) =
        RH t a (H t ⟨x, hxt⟩ + a • x) - RH t a (H s ⟨x, hxs⟩ + a • x) := by rw [hlinv]
    _ = RH t a ((H t ⟨x, hxt⟩ + a • x) - (H s ⟨x, hxs⟩ + a • x)) := (map_sub (RH t a) _ _).symm
    _ = RH t a (H t ⟨x, hxt⟩ - H s ⟨x, hxs⟩) := by rw [hsub]
    _ = RH t a (((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
          (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩)) := by
        rw [unconditional_common_two_time_hamiltonian_diff_eq ε hε h hh hb m g k s t x hx]
    _ = ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
          RH t a (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) := map_smul (RH t a) _ _

/-- Unconditional two-time shifted resolvent Lipschitz bound on `commonOperatorDomain`
for all real couplings `m, g, k` and times `s, t`:
`‖x - RH t a (H s x + a • x)‖ ≤ |Real.exp (2 * t) - Real.exp (2 * s)| * (a⁻¹ * (‖K x‖ + ‖P x‖))`. -/
theorem unconditional_common_two_time_shifted_resolvent_defect_norm_le
    (s t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    let hxs : x ∈ (H s).domain := common_domain_subset_hamiltonian ε hε h hh hb m g k s hx
    ‖x - RH t a (H s ⟨x, hxs⟩ + a • x)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (a⁻¹ * (‖K ⟨x, hx.1.1.2⟩‖ + ‖P ⟨x, hx.1.2⟩‖)) := by
  intro hxs
  rw [unconditional_common_two_time_shifted_resolvent_defect_eq ε hε h hh hb m g k s t a ha x hx,
    norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_norm_le
    ε hε h hh hb m g k t a ha (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩)
  have h2 : a⁻¹ * ‖K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩‖ ≤
      a⁻¹ * (‖K ⟨x, hx.1.1.2⟩‖ + ‖P ⟨x, hx.1.2⟩‖) :=
    mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.mpr ha.le)
  exact mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)

/-- Unconditional two-time residual shifted resolvent defect identity on `commonOperatorDomain`
for all real couplings `m, g, k` and times `s, t`:
`x - RS t a (S s x + a • x) = ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • RS t a (P x)`. -/
theorem unconditional_common_two_time_residual_shifted_resolvent_defect_eq
    (s t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    let hxs : x ∈ (S s).domain := common_domain_subset_residual ε hε h hh hb m g k s hx
    x - RS t a (S s ⟨x, hxs⟩ + a • x) =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • RS t a (P ⟨x, hx.1.2⟩) := by
  intro hxs
  let hxt : x ∈ (S t).domain := common_domain_subset_residual ε hε h hh hb m g k t hx
  have hlinv : RS t a (S t ⟨x, hxt⟩ + a • x) = x :=
    KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha ⟨x, hxt⟩
  have hSt : S t ⟨x, hxt⟩ = T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ :=
    (S t).mem_graph_snd_inj' ((S t).mem_graph ⟨x, hxt⟩)
      (unconditional_three_operator_residual_graph
        ε hε h hh hb m g k t x (T ⟨x, hx.1.1.1⟩) (P ⟨x, hx.1.2⟩)
        ((T).mem_graph ⟨x, hx.1.1.1⟩) ((P).mem_graph ⟨x, hx.1.2⟩) hx.2) rfl
  have hSs : S s ⟨x, hxs⟩ = T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * s) : ℂ) • P ⟨x, hx.1.2⟩ :=
    (S s).mem_graph_snd_inj' ((S s).mem_graph ⟨x, hxs⟩)
      (unconditional_three_operator_residual_graph
        ε hε h hh hb m g k s x (T ⟨x, hx.1.1.1⟩) (P ⟨x, hx.1.2⟩)
        ((T).mem_graph ⟨x, hx.1.1.1⟩) ((P).mem_graph ⟨x, hx.1.2⟩) hx.2) rfl
  have hdiff : (S t ⟨x, hxt⟩ + a • x) - (S s ⟨x, hxs⟩ + a • x) =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • P ⟨x, hx.1.2⟩ := by
    rw [hSt, hSs, Complex.ofReal_sub, sub_smul]
    abel
  calc
    x - RS t a (S s ⟨x, hxs⟩ + a • x) =
        RS t a (S t ⟨x, hxt⟩ + a • x) - RS t a (S s ⟨x, hxs⟩ + a • x) := by rw [hlinv]
    _ = RS t a ((S t ⟨x, hxt⟩ + a • x) - (S s ⟨x, hxs⟩ + a • x)) := (map_sub (RS t a) _ _).symm
    _ = RS t a (((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • P ⟨x, hx.1.2⟩) := by rw [hdiff]
    _ = ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • RS t a (P ⟨x, hx.1.2⟩) :=
        map_smul (RS t a) _ _

/-- Unconditional two-time residual shifted resolvent Lipschitz bound on `commonOperatorDomain`
for all real couplings `m, g, k` and times `s, t`:
`‖x - RS t a (S s x + a • x)‖ ≤ |Real.exp (2 * t) - Real.exp (2 * s)| * (a⁻¹ * ‖P x‖)`. -/
theorem unconditional_common_two_time_residual_shifted_resolvent_defect_norm_le
    (s t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    let hxs : x ∈ (S s).domain := common_domain_subset_residual ε hε h hh hb m g k s hx
    ‖x - RS t a (S s ⟨x, hxs⟩ + a • x)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * (a⁻¹ * ‖P ⟨x, hx.1.2⟩‖) := by
  intro hxs
  rw [unconditional_common_two_time_residual_shifted_resolvent_defect_eq
      ε hε h hh hb m g k s t a ha x hx,
    norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := KFCausalClockFloorResidualResolventRadialRootRegularity.residual_resolvent_norm_le
    ε hε h hh hb m g k t a ha (P ⟨x, hx.1.2⟩)
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

/-- Complete unconditional shifted resolvent defect package on `unconditionalCoreDomain`
for ALL real couplings `m, g, k, t` and `0 < a` (removing the `0 < k` hypothesis of
`KFCausalClockFloorPositiveVacuumUnconditionalCoreBridge`). -/
theorem unconditionalCoreDomain_shifted_resolvent_defect_package
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ unconditionalCoreDomain ε hε h hh hb m g k) :
    RH t a (T ⟨x, hx.1.1.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.1.1.1.2⟩ + P ⟨x, hx.1.1.1.2⟩) + a • x) = x ∧
    RS t a (T ⟨x, hx.1.1.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.1.1.2⟩ + a • x) = x ∧
    x - RH t a (T ⟨x, hx.1.1.1.1.1⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • RH t a (K ⟨x, hx.1.1.1.1.2⟩ + P ⟨x, hx.1.1.1.2⟩) ∧
    x - RS t a (T ⟨x, hx.1.1.1.1.1⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • RS t a (P ⟨x, hx.1.1.1.2⟩) ∧
    x - RH t a (T ⟨x, hx.1.1.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.1.1.2⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • RH t a (K ⟨x, hx.1.1.1.1.2⟩) :=
  ⟨unconditional_common_three_operator_left_inverse_cancel ε hε h hh hb m g k t a ha x hx.1.1,
   unconditional_common_residual_two_operator_left_inverse_cancel ε hε h hh hb m g k t a ha x hx.1.1,
   unconditional_common_hamiltonian_static_shifted_resolvent_defect ε hε h hh hb m g k t a ha x hx.1.1,
   unconditional_common_residual_static_shifted_resolvent_defect ε hε h hh hb m g k t a ha x hx.1.1,
   unconditional_common_hamiltonian_residual_shifted_resolvent_defect ε hε h hh hb m g k t a ha x hx.1.1⟩

/-- Unconditionally for ALL real couplings `m, g, k`, every `f ∈ commonOperatorDomain`,
and every pair of times `(s, t)`, the centered clock-Gaussian sequence
`coreApproxSeq ε f n = action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f` lies in
`unconditionalClockCore` for all `n : ℕ` and converges simultaneously across all 9
operator and clock graphs `(clockHalf ε).graph`, `(T).graph`, `(K).graph`, `(P).graph`,
`(G).graph`, `(S s).graph`, `(S t).graph`, `(H s).graph`, and `(H t).graph`. -/
theorem unconditional_two_time_clock_core_sequence_approximation
    (s t : ℝ) {f : Hilbert}
    (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    let c := clockHalf ε ⟨f, commonOperatorDomain_le_clockHalf_domain ε hε h hh hb m g k hf⟩
    let y := T ⟨f, hf.1.1.1⟩
    let r := K ⟨f, hf.1.1.2⟩
    let z := P ⟨f, hf.1.2⟩
    (∀ n : ℕ,
      action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f ∈
        unconditionalClockCore ε hε h hh hb m g k ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 c) ∈ (clockHalf ε).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y) ∈ (T).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r) ∈ (K).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈ (P).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
          action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈ (G).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
          (Real.exp (2 * s) : ℂ) • action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈
        (S s).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
          (Real.exp (2 * t) : ℂ) • action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈
        (S t).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
          (Real.exp (2 * s) : ℂ) •
            (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
              action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z)) ∈ (H s).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
          (Real.exp (2 * t) : ℂ) •
            (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
              action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z)) ∈ (H t).graph) ∧
    Tendsto (fun n : ℕ =>
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 c,
          (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y,
            (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r,
              (action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
                  action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                  (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
                    (Real.exp (2 * s) : ℂ) • action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                    action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
                      (Real.exp (2 * s) : ℂ) •
                        (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
                          action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z))))))))) atTop
      (𝓝 (f, (c, (y, (r, (z, (r + z, (y + (Real.exp (2 * s) : ℂ) • z,
        y + (Real.exp (2 * s) : ℂ) • (r + z))))))))) ∧
    Tendsto (fun n : ℕ =>
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 c,
          (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y,
            (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r,
              (action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
                  action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                  (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
                    (Real.exp (2 * t) : ℂ) • action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                    action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
                      (Real.exp (2 * t) : ℂ) •
                        (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
                          action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z))))))))) atTop
      (𝓝 (f, (c, (y, (r, (z, (r + z, (y + (Real.exp (2 * t) : ℂ) • z,
        y + (Real.exp (2 * t) : ℂ) • (r + z))))))))) := by
  intro c y r z
  have hc : (f, c) ∈ (clockHalf ε).graph :=
    (clockHalf ε).mem_graph ⟨f, commonOperatorDomain_le_clockHalf_domain ε hε h hh hb m g k hf⟩
  have ht : (f, y) ∈ (T).graph := (T).mem_graph ⟨f, hf.1.1.1⟩
  have hr : (f, r) ∈ (K).graph := (K).mem_graph ⟨f, hf.1.1.2⟩
  have hp : (f, z) ∈ (P).graph := (P).mem_graph ⟨f, hf.1.2⟩
  have hs_app :=
    unconditional_clock_sequence_multi_operator_approximation
      ε hε h hh hb m g k s f c y r z hc ht hr hp hf.2
  have ht_app :=
    unconditional_clock_sequence_multi_operator_approximation
      ε hε h hh hb m g k t f c y r z hc ht hr hp hf.2
  refine ⟨fun n => ?_, hs_app.2, ht_app.2⟩
  have hpos : 0 < (((n : ℝ) + 1)⁻¹) := by positivity
  have hcore :=
    (unconditional_gaussian_mem_clock_core_of_pos ε hε h hh hb m g k s
      (((n : ℝ) + 1)⁻¹) hpos hf).1
  have hgs := hs_app.1 n
  have hgt := ht_app.1 n
  exact ⟨hcore, hgs.1, hgs.2.1, hgs.2.2.1, hgs.2.2.2.1, hgs.2.2.2.2.1,
    hgs.2.2.2.2.2.1, hgt.2.2.2.2.2.1, hgs.2.2.2.2.2.2, hgt.2.2.2.2.2.2⟩

/-- Unconditionally for ALL real couplings `m, g, k` (including `k ≤ 0`), for any `s : ℝ`,
`a > 0`, and `x ∈ commonOperatorDomain`, the canonical sequence `coreApproxSeq ε x`
lies in `unconditionalCoreDomain` and `growingClockCoreDomain` for every `j : ℕ`,
converges to `x` in `Hilbert`, and satisfies all three shifted resolvent defect
identities at time `s` for every `j : ℕ`. -/
theorem unconditional_coreApproxSeq_with_resolvent_identities
    (s a : ℝ) (ha : 0 < a)
    (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    (∀ j, coreApproxSeq ε x j ∈ unconditionalCoreDomain ε hε h hh hb m g k) ∧
      (∀ j, coreApproxSeq ε x j ∈ growingClockCoreDomain ε hε h hh hb m g k) ∧
      (∀ j, ∃ hTj : coreApproxSeq ε x j ∈ (T).domain,
        ∃ hKj : coreApproxSeq ε x j ∈ (K).domain,
        ∃ hPj : coreApproxSeq ε x j ∈ (P).domain,
          coreApproxSeq ε x j - RH s a (T ⟨coreApproxSeq ε x j, hTj⟩ + a • coreApproxSeq ε x j) =
            (Real.exp (2 * s) : ℂ) •
              RH s a (K ⟨coreApproxSeq ε x j, hKj⟩ + P ⟨coreApproxSeq ε x j, hPj⟩) ∧
          coreApproxSeq ε x j - RS s a (T ⟨coreApproxSeq ε x j, hTj⟩ + a • coreApproxSeq ε x j) =
            (Real.exp (2 * s) : ℂ) • RS s a (P ⟨coreApproxSeq ε x j, hPj⟩) ∧
          coreApproxSeq ε x j - RH s a (T ⟨coreApproxSeq ε x j, hTj⟩ +
              (Real.exp (2 * s) : ℂ) • P ⟨coreApproxSeq ε x j, hPj⟩ + a • coreApproxSeq ε x j) =
            (Real.exp (2 * s) : ℂ) • RH s a (K ⟨coreApproxSeq ε x j, hKj⟩)) ∧
      Tendsto (coreApproxSeq ε x) atTop (𝓝 x) := by
  have hmem : ∀ j, coreApproxSeq ε x j ∈ unconditionalCoreDomain ε hε h hh hb m g k :=
    fun j => (unconditional_gaussian_mem_clock_core_of_pos
      ε hε h hh hb m g k s (((j : ℝ) + 1)⁻¹) (by positivity) hx).1
  have hgrow : ∀ j, coreApproxSeq ε x j ∈ growingClockCoreDomain ε hε h hh hb m g k :=
    fun j => (coreDomains_le_growingClockCoreDomain ε hε h hh hb m g k).1 (hmem j)
  refine ⟨hmem, hgrow, ?_, sequence_tendsto ε 0 x⟩
  intro j
  have hj := (hmem j).1.1
  refine ⟨hj.1.1.1, hj.1.1.2, hj.1.2, ?_, ?_, ?_⟩
  · exact unconditional_common_hamiltonian_static_shifted_resolvent_defect
      ε hε h hh hb m g k s a ha (coreApproxSeq ε x j) hj
  · exact unconditional_common_residual_static_shifted_resolvent_defect
      ε hε h hh hb m g k s a ha (coreApproxSeq ε x j) hj
  · exact unconditional_common_hamiltonian_residual_shifted_resolvent_defect
      ε hε h hh hb m g k s a ha (coreApproxSeq ε x j) hj

#print axioms iteratedYosida_eq_sq_smul
#print axioms iteratedYosida_norm_bound
#print axioms iteratedYosida_sub_eq
#print axioms iteratedYosida_sub_norm_le_two_mul
#print axioms iteratedYosida_error_on_domain
#print axioms iteratedYosida_mem_secondPowerGraph
#print axioms iteratedYosida_sequence_approximation
#print axioms iteratedYosida_strong_limit
#print axioms secondPowerGraph_three_tier_error_bounds
#print axioms secondPowerGraph_three_tier_sequence_convergence
#print axioms static_secondPowerGraph_three_tier_convergence
#print axioms potential_secondPowerGraph_three_tier_convergence
#print axioms growing_secondPowerGraph_three_tier_convergence
#print axioms residual_secondPowerGraph_three_tier_convergence
#print axioms hamiltonian_secondPowerGraph_three_tier_convergence
#print axioms hamiltonian_iteratedYosida_sequence_approximation
#print axioms unconditional_common_three_operator_left_inverse_cancel
#print axioms unconditional_common_residual_two_operator_left_inverse_cancel
#print axioms unconditional_common_hamiltonian_static_shifted_resolvent_defect
#print axioms unconditional_common_residual_static_shifted_resolvent_defect
#print axioms unconditional_common_hamiltonian_residual_shifted_resolvent_defect
#print axioms unconditional_common_hamiltonian_static_shifted_resolvent_defect_norm_le
#print axioms unconditional_common_residual_static_shifted_resolvent_defect_norm_le
#print axioms unconditional_common_hamiltonian_residual_shifted_resolvent_defect_norm_le
#print axioms unconditional_common_two_time_hamiltonian_diff_eq
#print axioms unconditional_common_two_time_shifted_resolvent_defect_eq
#print axioms unconditional_common_two_time_shifted_resolvent_defect_norm_le
#print axioms unconditional_common_two_time_residual_shifted_resolvent_defect_eq
#print axioms unconditional_common_two_time_residual_shifted_resolvent_defect_norm_le
#print axioms unconditionalCoreDomain_shifted_resolvent_defect_package
#print axioms unconditional_two_time_clock_core_sequence_approximation
#print axioms unconditional_coreApproxSeq_with_resolvent_identities

end

end UnifiedTheory.Audit.KFCausalClockFloorArbitraryCouplingIteratedCoreApproximation
