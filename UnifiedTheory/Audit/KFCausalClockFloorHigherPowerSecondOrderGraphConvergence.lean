/- Higher-Power Second-Order and Third-Order Yosida Graph Convergence,
Operator-Square Commutation, and Three-Tier Graph-Norm Contraction Across
All Five Clock-Floor Hamiltonians T, P, G, S(t), and H(t):
1. Proves that for any positive operator A with shifted resolvent R(a) (a > 0),
   every r-th order Yosida-scaled identity approximant
   `iteratedIdentityPower R a r x = ((a ^ r : ℝ) : ℂ) • R^r x` maps `A.domain`
   into `A.domain`, maps `secondPowerDomain A` (`Dom(A²)`) into `secondPowerDomain A`,
   and commutes with both `A` and `A²`:
   - `A (iteratedIdentityPower R a r x) = iteratedIdentityPower R a r (A x)`
   - `A (A (iteratedIdentityPower R a r x)) = iteratedIdentityPower R a r (A (A x))`.
2. Establishes explicit 3-tier error bounds on `secondPowerDomain A` (`Dom(A²)`):
   - Tier 0: `‖iteratedIdentityPower R a r x - x‖ ≤ (r : ℝ) * a⁻¹ * ‖A x‖`,
   - Tier 1: `‖iteratedIdentityPower R a r (A x) - A x‖ ≤ (r : ℝ) * a⁻¹ * ‖A (A x)‖`,
   - Tier 2 (on `Dom(A²)`): `‖iteratedIdentityPower R a r (A (A x)) - A (A x)‖ ≤ 2 * ‖A (A x)‖`,
   - Tier 2 (on `Dom(A³)`): `‖iteratedIdentityPower R a r (A (A x)) - A (A x)‖ ≤ (r : ℝ) * a⁻¹ * ‖A (A (A x))‖`,
   together with `secondPowerGraphNormSq` contraction and quadratic error bounds.
3. Proves strong convergence `iteratedIdentityPower (R (cutoff n)) (cutoff n) r u → u`
   for all `u : H` when `Dense (A.domain : Set H)`, deducing simultaneous 3-tier
   `Dom(A²)` and `Dom(A³)` graph convergence across all five clock-floor operators
   `T`, `P`, `G`, `S t`, and `H t`. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerYosidaGraphConvergence
import UnifiedTheory.Audit.KFCausalClockFloorArbitraryCouplingIteratedThreeOperatorSynthesis

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerSecondOrderGraphConvergence

noncomputable section

open Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalPositiveResolventBounds
  (Resolves point resolvent_apply_norm_bound)
open KFCausalYosidaApproximation (scaled_resolvent_strong_limit)
open KFCausalClockFloorPotentialClockApproximation (cutoff cutoff_pos cutoff_tendsto)
open KFCausalClockFloorStaticResolventRadialCommutator
  (staticOperator_positive staticResolvent staticResolvent_resolves staticResolvent_left_inverse)
open KFCausalClockFloorSecondPowerOperatorCores
  (secondPowerGraph secondPowerDomain mem_secondPowerDomain_iff
   scaled_resolvent_mem_secondPowerGraph)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (scaled_resolvent_norm_bound)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain iteratedResolventPower
   staticPowerDomain potentialPowerDomain growingPowerDomain
   residualPowerDomain hamiltonianPowerDomain)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedIdentityPower iteratedIdentityPower_zero iteratedIdentityPower_succ
   iteratedIdentityPower_sub_self_right_step
   iteratedIdentityPower_mem_operatorPowerDomain
   iteratedIdentityPower_norm_le
   single_yosida_defect_on_domain
   iteratedIdentityPower_domain_rate_bound)
open KFCausalClockFloorArbitraryCouplingIteratedThreeOperatorSynthesis
  (twoTimeIteratedHamiltonianYosidaDiff
   twoTimeIteratedHamiltonianYosidaDiff_mem_common_time_independent_domains)

/-! ### 1. Abstract Higher-Power `Dom(A²)` & `Dom(A³)` Commutation and 3-Tier Graph Convergence -/

section AbstractSecondOrderGraphConvergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The 3-tier squared second-power graph norm `‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2`. -/
def secondPowerGraphNormSq (u v w : H) : ℝ :=
  ‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2

/-- For every `x : A.domain` and `r : ℕ`, the pair
`(iteratedIdentityPower R a r (x : H), iteratedIdentityPower R a r (A x))` lies in `A.graph`. -/
theorem iteratedIdentityPower_mem_graph_of_mem_domain
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H)) :
    ∀ r : ℕ, ∀ x : A.domain,
      (iteratedIdentityPower R a r (x : H), iteratedIdentityPower R a r (A x)) ∈ A.graph
  | 0, x => by
    rw [iteratedIdentityPower_zero, iteratedIdentityPower_zero]
    exact A.mem_graph x
  | r + 1, x => by
    have ih := iteratedIdentityPower_mem_graph_of_mem_domain A R a hr hl r x
    let u : A.domain := ⟨iteratedIdentityPower R a r (x : H), LinearPMap.mem_domain_of_mem_graph ih⟩
    have hu : A u = iteratedIdentityPower R a r (A x) :=
      A.mem_graph_snd_inj' (A.mem_graph u) ih rfl
    have hsc := (scaled_resolvent_mem_secondPowerGraph A R a hr hl u).1
    change ((a : ℂ) • R (iteratedIdentityPower R a r (x : H)),
            (a : ℂ) • R (A u)) ∈ A.graph at hsc
    rw [hu, ← iteratedIdentityPower_succ, ← iteratedIdentityPower_succ] at hsc
    exact hsc

/-- For every `x : A.domain` and `r : ℕ`, `iteratedIdentityPower R a r (x : H) ∈ A.domain`. -/
theorem iteratedIdentityPower_mem_domain_of_mem_domain
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) :
    iteratedIdentityPower R a r (x : H) ∈ A.domain :=
  LinearPMap.mem_domain_of_mem_graph
    (iteratedIdentityPower_mem_graph_of_mem_domain A R a hr hl r x)

/-- Exact commutation of `A` with `iteratedIdentityPower R a r` on `A.domain`:
`A ⟨iteratedIdentityPower R a r x, ...⟩ = iteratedIdentityPower R a r (A x)`. -/
theorem iteratedIdentityPower_commutes_with_operator
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) :
    A ⟨iteratedIdentityPower R a r (x : H),
       iteratedIdentityPower_mem_domain_of_mem_domain A R a hr hl r x⟩ =
      iteratedIdentityPower R a r (A x) := by
  let u : A.domain :=
    ⟨iteratedIdentityPower R a r (x : H),
     iteratedIdentityPower_mem_domain_of_mem_domain A R a hr hl r x⟩
  exact A.mem_graph_snd_inj' (A.mem_graph u)
    (iteratedIdentityPower_mem_graph_of_mem_domain A R a hr hl r x) rfl

/-- For every `x : A.domain` and `r : ℕ` (order `r + 1 ≥ 1`), the pair
`(iteratedIdentityPower R a (r + 1) x, iteratedIdentityPower R a (r + 1) (A x))` lies in `secondPowerGraph A`. -/
theorem iteratedIdentityPower_succ_mem_secondPowerGraph_of_mem_domain
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) :
    (iteratedIdentityPower R a (r + 1) (x : H),
      iteratedIdentityPower R a (r + 1) (A x)) ∈ secondPowerGraph A := by
  have ih := iteratedIdentityPower_mem_graph_of_mem_domain A R a hr hl r x
  let u : A.domain := ⟨iteratedIdentityPower R a r (x : H), LinearPMap.mem_domain_of_mem_graph ih⟩
  have hu : A u = iteratedIdentityPower R a r (A x) :=
    A.mem_graph_snd_inj' (A.mem_graph u) ih rfl
  have hsc := scaled_resolvent_mem_secondPowerGraph A R a hr hl u
  change ((a : ℂ) • R (iteratedIdentityPower R a r (x : H)),
          (a : ℂ) • R (A u)) ∈ secondPowerGraph A at hsc
  rw [hu, ← iteratedIdentityPower_succ, ← iteratedIdentityPower_succ] at hsc
  exact hsc

/-- For every `x : A.domain` with `hAx : A x ∈ A.domain` and every `r : ℕ`, the pair
`(iteratedIdentityPower R a r x, iteratedIdentityPower R a r (A x))` lies in `secondPowerGraph A`. -/
theorem iteratedIdentityPower_mem_secondPowerGraph_of_secondPower
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) (hAx : A x ∈ A.domain) :
    (iteratedIdentityPower R a r (x : H),
      iteratedIdentityPower R a r (A x)) ∈ secondPowerGraph A :=
  ⟨iteratedIdentityPower_mem_graph_of_mem_domain A R a hr hl r x,
   iteratedIdentityPower_mem_domain_of_mem_domain A R a hr hl r ⟨A x, hAx⟩⟩

/-- For every `x : A.domain` with `hAx : A x ∈ A.domain` and every `r : ℕ`,
`iteratedIdentityPower R a r (x : H) ∈ secondPowerDomain A`. -/
theorem iteratedIdentityPower_mem_secondPowerDomain_of_secondPower
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) (hAx : A x ∈ A.domain) :
    iteratedIdentityPower R a r (x : H) ∈ secondPowerDomain A :=
  ⟨(iteratedIdentityPower R a r (x : H), iteratedIdentityPower R a r (A x)),
   iteratedIdentityPower_mem_secondPowerGraph_of_secondPower A R a hr hl r x hAx,
   rfl⟩

/-- Invariance of `secondPowerDomain A` under `iteratedIdentityPower R a r` for all `r : ℕ`. -/
theorem iteratedIdentityPower_mem_secondPowerDomain
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (r : ℕ) {z : H} (hz : z ∈ secondPowerDomain A) :
    iteratedIdentityPower R a r z ∈ secondPowerDomain A := by
  rcases (mem_secondPowerDomain_iff A z).mp hz with ⟨hz_dom, hAz⟩
  exact iteratedIdentityPower_mem_secondPowerDomain_of_secondPower A R a hr hl r ⟨z, hz_dom⟩ hAz

/-- Simultaneous commutation of `iteratedIdentityPower R a r` with both `A` and `A²`
for every `x : A.domain` with `hAx : A x ∈ A.domain`. -/
theorem iteratedIdentityPower_commutes_with_second_power
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) (hAx : A x ∈ A.domain) :
    A ⟨iteratedIdentityPower R a r (x : H),
       iteratedIdentityPower_mem_domain_of_mem_domain A R a hr hl r x⟩ =
      iteratedIdentityPower R a r (A x) ∧
    A ⟨iteratedIdentityPower R a r (A x),
       iteratedIdentityPower_mem_domain_of_mem_domain A R a hr hl r ⟨A x, hAx⟩⟩ =
      iteratedIdentityPower R a r (A ⟨A x, hAx⟩) :=
  ⟨iteratedIdentityPower_commutes_with_operator A R a hr hl r x,
   iteratedIdentityPower_commutes_with_operator A R a hr hl r ⟨A x, hAx⟩⟩

/-- Exact first- and second-order operator defect identities on `Dom(A²)` for
`iteratedIdentityPower R a r`. -/
theorem iteratedIdentityPower_second_power_defect_eq
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) (hAx : A x ∈ A.domain) :
    A ⟨iteratedIdentityPower R a r (x : H),
       iteratedIdentityPower_mem_domain_of_mem_domain A R a hr hl r x⟩ - A x =
      iteratedIdentityPower R a r (A x) - A x ∧
    A ⟨iteratedIdentityPower R a r (A x),
       iteratedIdentityPower_mem_domain_of_mem_domain A R a hr hl r ⟨A x, hAx⟩⟩ -
      A ⟨A x, hAx⟩ =
      iteratedIdentityPower R a r (A ⟨A x, hAx⟩) - A ⟨A x, hAx⟩ := by
  rw [iteratedIdentityPower_commutes_with_operator A R a hr hl r x,
      iteratedIdentityPower_commutes_with_operator A R a hr hl r ⟨A x, hAx⟩]
  exact ⟨rfl, rfl⟩

/-- Explicit 3-tier approximation bounds on `Dom(A²)` (`x : A.domain`, `hAx : A x ∈ A.domain`):
`O(r * a⁻¹)` on Tiers 0 and 1, and uniform `2 * ‖A (A x)‖` bound on Tier 2. -/
theorem iteratedIdentityPower_three_tier_bounds_on_secondPower
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) (hAx : A x ∈ A.domain) :
    ‖iteratedIdentityPower R a r (x : H) - (x : H)‖ ≤ (r : ℝ) * a⁻¹ * ‖A x‖ ∧
    ‖iteratedIdentityPower R a r (A x) - A x‖ ≤ (r : ℝ) * a⁻¹ * ‖A ⟨A x, hAx⟩‖ ∧
    ‖iteratedIdentityPower R a r (A ⟨A x, hAx⟩) - A ⟨A x, hAx⟩‖ ≤ 2 * ‖A ⟨A x, hAx⟩‖ := by
  refine ⟨iteratedIdentityPower_domain_rate_bound A R a ha hr hp hl r x,
          iteratedIdentityPower_domain_rate_bound A R a ha hr hp hl r ⟨A x, hAx⟩,
          ?_⟩
  have htri := norm_sub_le (iteratedIdentityPower R a r (A ⟨A x, hAx⟩)) (A ⟨A x, hAx⟩)
  have hcon := iteratedIdentityPower_norm_le A R a ha hr hp r (A ⟨A x, hAx⟩)
  linarith

/-- Explicit 3-tier `O(r * a⁻¹)` rate bounds on `Dom(A³)`
(`x : A.domain`, `hAx : A x ∈ A.domain`, `hAAx : A ⟨A x, hAx⟩ ∈ A.domain`). -/
theorem iteratedIdentityPower_three_tier_rate_bounds_on_thirdPower
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) (hAx : A x ∈ A.domain) (hAAx : A ⟨A x, hAx⟩ ∈ A.domain) :
    ‖iteratedIdentityPower R a r (x : H) - (x : H)‖ ≤ (r : ℝ) * a⁻¹ * ‖A x‖ ∧
    ‖iteratedIdentityPower R a r (A x) - A x‖ ≤ (r : ℝ) * a⁻¹ * ‖A ⟨A x, hAx⟩‖ ∧
    ‖iteratedIdentityPower R a r (A ⟨A x, hAx⟩) - A ⟨A x, hAx⟩‖ ≤
      (r : ℝ) * a⁻¹ * ‖A ⟨A ⟨A x, hAx⟩, hAAx⟩‖ :=
  ⟨iteratedIdentityPower_domain_rate_bound A R a ha hr hp hl r x,
   iteratedIdentityPower_domain_rate_bound A R a ha hr hp hl r ⟨A x, hAx⟩,
   iteratedIdentityPower_domain_rate_bound A R a ha hr hp hl r ⟨A ⟨A x, hAx⟩, hAAx⟩⟩

omit [InnerProductSpace ℂ H] in
/-- Nonnegativity of `secondPowerGraphNormSq u v w`. -/
theorem secondPowerGraphNormSq_nonneg (u v w : H) :
    0 ≤ secondPowerGraphNormSq u v w := by
  unfold secondPowerGraphNormSq
  positivity

/-- Uniform contraction of `secondPowerGraphNormSq` under `iteratedIdentityPower R a r`. -/
theorem secondPowerGraphNormSq_iteratedIdentityPower_contraction
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (r : ℕ) (u v w : H) :
    secondPowerGraphNormSq
      (iteratedIdentityPower R a r u)
      (iteratedIdentityPower R a r v)
      (iteratedIdentityPower R a r w) ≤
      secondPowerGraphNormSq u v w := by
  unfold secondPowerGraphNormSq
  have hu : ‖iteratedIdentityPower R a r u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (iteratedIdentityPower_norm_le A R a ha hr hp r u) 2
  have hv : ‖iteratedIdentityPower R a r v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (iteratedIdentityPower_norm_le A R a ha hr hp r v) 2
  have hw : ‖iteratedIdentityPower R a r w‖ ^ 2 ≤ ‖w‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (iteratedIdentityPower_norm_le A R a ha hr hp r w) 2
  linarith

/-- Quadratic 3-tier `secondPowerGraphNormSq` error bound on `Dom(A²)`. -/
theorem secondPowerGraphNormSq_defect_bound_on_secondPower
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) (hAx : A x ∈ A.domain) :
    secondPowerGraphNormSq
      (iteratedIdentityPower R a r (x : H) - (x : H))
      (iteratedIdentityPower R a r (A x) - A x)
      (iteratedIdentityPower R a r (A ⟨A x, hAx⟩) - A ⟨A x, hAx⟩) ≤
      ((r : ℝ) * a⁻¹ * ‖A x‖) ^ 2 +
        ((r : ℝ) * a⁻¹ * ‖A ⟨A x, hAx⟩‖) ^ 2 +
        (2 * ‖A ⟨A x, hAx⟩‖) ^ 2 := by
  unfold secondPowerGraphNormSq
  have hb := iteratedIdentityPower_three_tier_bounds_on_secondPower A R a ha hr hp hl r x hAx
  have h0 : ‖iteratedIdentityPower R a r (x : H) - (x : H)‖ ^ 2 ≤
      ((r : ℝ) * a⁻¹ * ‖A x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb.1 2
  have h1 : ‖iteratedIdentityPower R a r (A x) - A x‖ ^ 2 ≤
      ((r : ℝ) * a⁻¹ * ‖A ⟨A x, hAx⟩‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb.2.1 2
  have h2 : ‖iteratedIdentityPower R a r (A ⟨A x, hAx⟩) - A ⟨A x, hAx⟩‖ ^ 2 ≤
      (2 * ‖A ⟨A x, hAx⟩‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb.2.2 2
  linarith

/-- Quadratic 3-tier `secondPowerGraphNormSq` `O((r * a⁻¹)²)` rate bound on `Dom(A³)`. -/
theorem secondPowerGraphNormSq_defect_rate_bound_on_thirdPower
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) (hAx : A x ∈ A.domain) (hAAx : A ⟨A x, hAx⟩ ∈ A.domain) :
    secondPowerGraphNormSq
      (iteratedIdentityPower R a r (x : H) - (x : H))
      (iteratedIdentityPower R a r (A x) - A x)
      (iteratedIdentityPower R a r (A ⟨A x, hAx⟩) - A ⟨A x, hAx⟩) ≤
      ((r : ℝ) * a⁻¹ * ‖A x‖) ^ 2 +
        ((r : ℝ) * a⁻¹ * ‖A ⟨A x, hAx⟩‖) ^ 2 +
        ((r : ℝ) * a⁻¹ * ‖A ⟨A ⟨A x, hAx⟩, hAAx⟩‖) ^ 2 := by
  unfold secondPowerGraphNormSq
  have hb :=
    iteratedIdentityPower_three_tier_rate_bounds_on_thirdPower A R a ha hr hp hl r x hAx hAAx
  have h0 : ‖iteratedIdentityPower R a r (x : H) - (x : H)‖ ^ 2 ≤
      ((r : ℝ) * a⁻¹ * ‖A x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb.1 2
  have h1 : ‖iteratedIdentityPower R a r (A x) - A x‖ ^ 2 ≤
      ((r : ℝ) * a⁻¹ * ‖A ⟨A x, hAx⟩‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb.2.1 2
  have h2 : ‖iteratedIdentityPower R a r (A ⟨A x, hAx⟩) - A ⟨A x, hAx⟩‖ ^ 2 ≤
      ((r : ℝ) * a⁻¹ * ‖A ⟨A ⟨A x, hAx⟩, hAAx⟩‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb.2.2 2
  linarith

/-- Universal `r`-factor defect bound on all of `H`:
`‖iteratedIdentityPower R a r u - u‖ ≤ (r : ℝ) * ‖(a : ℂ) • R u - u‖` for all `r : ℕ` and `u : H`. -/
theorem iteratedIdentityPower_sub_norm_le_mul
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re) :
    ∀ r : ℕ, ∀ u : H,
      ‖iteratedIdentityPower R a r u - u‖ ≤ (r : ℝ) * ‖(a : ℂ) • R u - u‖
  | 0, u => by
    rw [iteratedIdentityPower_zero, sub_self, norm_zero, Nat.cast_zero, zero_mul]
  | r + 1, u => by
    rw [iteratedIdentityPower_sub_self_right_step, Nat.cast_succ]
    have htri :=
      norm_add_le
        (iteratedIdentityPower R a r ((a : ℂ) • R u - u))
        (iteratedIdentityPower R a r u - u)
    have h1 := iteratedIdentityPower_norm_le A R a ha hr hp r ((a : ℂ) • R u - u)
    have h2 := iteratedIdentityPower_sub_norm_le_mul A R a ha hr hp r u
    linarith

/-- Strong convergence on all of `H`: when `Dense (A.domain : Set H)`, for every `r : ℕ` and
`u : H`, `iteratedIdentityPower (R (cutoff n)) (cutoff n) r u → u` as `n → ∞`. -/
theorem iteratedIdentityPower_strong_limit_on_hilbert
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hd : Dense (A.domain : Set H))
    (hr : ∀ a, 0 < a → Resolves A (R a) a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ a, 0 < a → ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H))
    (r : ℕ) (u : H) :
    Tendsto (fun n : ℕ => iteratedIdentityPower (R (cutoff n)) (cutoff n) r u) atTop (𝓝 u) := by
  have hI : Tendsto (fun n : ℕ => (cutoff n : ℂ) • R (cutoff n) u - u) atTop (𝓝 0) := by
    simpa only [Complex.coe_smul, sub_self] using
      ((scaled_resolvent_strong_limit A R hd hr hp hl u).comp cutoff_tendsto).sub_const u
  have hnorm0 :
      Tendsto (fun n : ℕ => (r : ℝ) * ‖(cutoff n : ℂ) • R (cutoff n) u - u‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hI.norm.const_mul (r : ℝ)
  have hdiff0 :
      Tendsto
        (fun n : ℕ => ‖iteratedIdentityPower (R (cutoff n)) (cutoff n) r u - u‖)
        atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _)
      (fun n => iteratedIdentityPower_sub_norm_le_mul A (R (cutoff n)) (cutoff n)
        (cutoff_pos n) (hr (cutoff n) (cutoff_pos n)) hp r u)
      hnorm0
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hdiff0

/-- Simultaneous 3-tier convergence on `Dom(A²)` for arbitrary order `r : ℕ` along `cutoff n`. -/
theorem iteratedIdentityPower_three_tier_tendsto_on_secondPower
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hd : Dense (A.domain : Set H))
    (hr : ∀ a, 0 < a → Resolves A (R a) a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ a, 0 < a → ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) (hAx : A x ∈ A.domain) :
    (∀ n : ℕ,
      (iteratedIdentityPower (R (cutoff n)) (cutoff n) r (x : H),
        iteratedIdentityPower (R (cutoff n)) (cutoff n) r (A x)) ∈ secondPowerGraph A ∧
      ‖iteratedIdentityPower (R (cutoff n)) (cutoff n) r (x : H) - (x : H)‖ ≤
        (r : ℝ) * (cutoff n)⁻¹ * ‖A x‖ ∧
      ‖iteratedIdentityPower (R (cutoff n)) (cutoff n) r (A x) - A x‖ ≤
        (r : ℝ) * (cutoff n)⁻¹ * ‖A ⟨A x, hAx⟩‖ ∧
      ‖iteratedIdentityPower (R (cutoff n)) (cutoff n) r (A ⟨A x, hAx⟩) - A ⟨A x, hAx⟩‖ ≤
        2 * ‖A ⟨A x, hAx⟩‖) ∧
    Tendsto (fun n : ℕ =>
      (iteratedIdentityPower (R (cutoff n)) (cutoff n) r (x : H),
        (iteratedIdentityPower (R (cutoff n)) (cutoff n) r (A x),
          iteratedIdentityPower (R (cutoff n)) (cutoff n) r (A ⟨A x, hAx⟩))))
      atTop (𝓝 ((x : H), (A x, A ⟨A x, hAx⟩))) := by
  refine ⟨fun n => ?_, ?_⟩
  · have hpos := cutoff_pos n
    have hb :=
      iteratedIdentityPower_three_tier_bounds_on_secondPower A (R (cutoff n)) (cutoff n) hpos
        (hr (cutoff n) hpos) hp (hl (cutoff n) hpos) r x hAx
    exact ⟨iteratedIdentityPower_mem_secondPowerGraph_of_secondPower A (R (cutoff n)) (cutoff n)
      (hr (cutoff n) hpos) (hl (cutoff n) hpos) r x hAx,
      hb.1, hb.2.1, hb.2.2⟩
  · exact (iteratedIdentityPower_strong_limit_on_hilbert A R hd hr hp hl r (x : H)).prodMk_nhds
      ((iteratedIdentityPower_strong_limit_on_hilbert A R hd hr hp hl r (A x)).prodMk_nhds
        (iteratedIdentityPower_strong_limit_on_hilbert A R hd hr hp hl r (A ⟨A x, hAx⟩)))

/-- Simultaneous 3-tier `O((cutoff n)⁻¹)` convergence on `Dom(A³)` for arbitrary order `r : ℕ`. -/
theorem iteratedIdentityPower_three_tier_tendsto_on_thirdPower
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hd : Dense (A.domain : Set H))
    (hr : ∀ a, 0 < a → Resolves A (R a) a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ a, 0 < a → ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) (hAx : A x ∈ A.domain) (hAAx : A ⟨A x, hAx⟩ ∈ A.domain) :
    (∀ n : ℕ,
      ‖iteratedIdentityPower (R (cutoff n)) (cutoff n) r (x : H) - (x : H)‖ ≤
        (r : ℝ) * (cutoff n)⁻¹ * ‖A x‖ ∧
      ‖iteratedIdentityPower (R (cutoff n)) (cutoff n) r (A x) - A x‖ ≤
        (r : ℝ) * (cutoff n)⁻¹ * ‖A ⟨A x, hAx⟩‖ ∧
      ‖iteratedIdentityPower (R (cutoff n)) (cutoff n) r (A ⟨A x, hAx⟩) - A ⟨A x, hAx⟩‖ ≤
        (r : ℝ) * (cutoff n)⁻¹ * ‖A ⟨A ⟨A x, hAx⟩, hAAx⟩‖) ∧
    Tendsto (fun n : ℕ =>
      (iteratedIdentityPower (R (cutoff n)) (cutoff n) r (x : H),
        (iteratedIdentityPower (R (cutoff n)) (cutoff n) r (A x),
          iteratedIdentityPower (R (cutoff n)) (cutoff n) r (A ⟨A x, hAx⟩))))
      atTop (𝓝 ((x : H), (A x, A ⟨A x, hAx⟩))) :=
  ⟨fun n =>
    iteratedIdentityPower_three_tier_rate_bounds_on_thirdPower A (R (cutoff n)) (cutoff n)
      (cutoff_pos n) (hr (cutoff n) (cutoff_pos n)) hp (hl (cutoff n) (cutoff_pos n)) r x hAx hAAx,
   (iteratedIdentityPower_three_tier_tendsto_on_secondPower A R hd hr hp hl r x hAx).2⟩

end AbstractSecondOrderGraphConvergence

/-! ### 2. Concrete Higher-Power `Dom(A²)` & `Dom(A³)` Convergence for `T`, `P`, `G`, `S(t)`, and `H(t)` -/

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
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k

private theorem static_selfAdjoint : IsSelfAdjoint T :=
  KFCausalRealMultiplierSelfAdjoint.realPullback_selfAdjoint
    KFCausalChargeTransverseSplit.dualPhysical
    (KFCausalClockFloorStaticMultiplierForm.symbol ε h)
    (KFCausalClockFloorStaticMultiplierForm.symbol_continuous ε hε h).measurable

/-- Higher-power `Dom(T²)` membership, `T`/`T²` commutation, and 3-tier bounds for `T`. -/
theorem static_iteratedIdentityPower_secondPower_comm_and_bounds
    (a : ℝ) (ha : 0 < a) (r : ℕ) (x : (T).domain) (hTx : T x ∈ (T).domain) :
    iteratedIdentityPower (RT a) a r (x : Hilbert) ∈ secondPowerDomain T ∧
    (iteratedIdentityPower (RT a) a r (x : Hilbert),
      iteratedIdentityPower (RT a) a r (T x)) ∈ secondPowerGraph T ∧
    (T ⟨iteratedIdentityPower (RT a) a r (x : Hilbert),
        iteratedIdentityPower_mem_domain_of_mem_domain T (RT a) a
          (staticResolvent_resolves ε hε h hb hh a ha)
          (staticResolvent_left_inverse ε hε h hb hh a ha) r x⟩ =
      iteratedIdentityPower (RT a) a r (T x) ∧
     T ⟨iteratedIdentityPower (RT a) a r (T x),
        iteratedIdentityPower_mem_domain_of_mem_domain T (RT a) a
          (staticResolvent_resolves ε hε h hb hh a ha)
          (staticResolvent_left_inverse ε hε h hb hh a ha) r ⟨T x, hTx⟩⟩ =
      iteratedIdentityPower (RT a) a r (T ⟨T x, hTx⟩)) ∧
    ‖iteratedIdentityPower (RT a) a r (x : Hilbert) - (x : Hilbert)‖ ≤ (r : ℝ) * a⁻¹ * ‖T x‖ ∧
    ‖iteratedIdentityPower (RT a) a r (T x) - T x‖ ≤ (r : ℝ) * a⁻¹ * ‖T ⟨T x, hTx⟩‖ ∧
    ‖iteratedIdentityPower (RT a) a r (T ⟨T x, hTx⟩) - T ⟨T x, hTx⟩‖ ≤ 2 * ‖T ⟨T x, hTx⟩‖ :=
  ⟨iteratedIdentityPower_mem_secondPowerDomain_of_secondPower T (RT a) a
     (staticResolvent_resolves ε hε h hb hh a ha)
     (staticResolvent_left_inverse ε hε h hb hh a ha) r x hTx,
   iteratedIdentityPower_mem_secondPowerGraph_of_secondPower T (RT a) a
     (staticResolvent_resolves ε hε h hb hh a ha)
     (staticResolvent_left_inverse ε hε h hb hh a ha) r x hTx,
   iteratedIdentityPower_commutes_with_second_power T (RT a) a
     (staticResolvent_resolves ε hε h hb hh a ha)
     (staticResolvent_left_inverse ε hε h hb hh a ha) r x hTx,
   iteratedIdentityPower_three_tier_bounds_on_secondPower T (RT a) a ha
     (staticResolvent_resolves ε hε h hb hh a ha)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh a ha) r x hTx⟩

/-- Higher-power `Dom(P²)` membership, `P`/`P²` commutation, and 3-tier bounds for `P`. -/
theorem potential_iteratedIdentityPower_secondPower_comm_and_bounds
    (a : ℝ) (ha : 0 < a) (r : ℕ) (x : (P).domain) (hPx : P x ∈ (P).domain) :
    iteratedIdentityPower (RP a) a r (x : Hilbert) ∈ secondPowerDomain P ∧
    (iteratedIdentityPower (RP a) a r (x : Hilbert),
      iteratedIdentityPower (RP a) a r (P x)) ∈ secondPowerGraph P ∧
    (P ⟨iteratedIdentityPower (RP a) a r (x : Hilbert),
        iteratedIdentityPower_mem_domain_of_mem_domain P (RP a) a
          (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
          (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) r x⟩ =
      iteratedIdentityPower (RP a) a r (P x) ∧
     P ⟨iteratedIdentityPower (RP a) a r (P x),
        iteratedIdentityPower_mem_domain_of_mem_domain P (RP a) a
          (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
          (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha)
          r ⟨P x, hPx⟩⟩ =
      iteratedIdentityPower (RP a) a r (P ⟨P x, hPx⟩)) ∧
    ‖iteratedIdentityPower (RP a) a r (x : Hilbert) - (x : Hilbert)‖ ≤ (r : ℝ) * a⁻¹ * ‖P x‖ ∧
    ‖iteratedIdentityPower (RP a) a r (P x) - P x‖ ≤ (r : ℝ) * a⁻¹ * ‖P ⟨P x, hPx⟩‖ ∧
    ‖iteratedIdentityPower (RP a) a r (P ⟨P x, hPx⟩) - P ⟨P x, hPx⟩‖ ≤ 2 * ‖P ⟨P x, hPx⟩‖ :=
  ⟨iteratedIdentityPower_mem_secondPowerDomain_of_secondPower P (RP a) a
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) r x hPx,
   iteratedIdentityPower_mem_secondPowerGraph_of_secondPower P (RP a) a
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) r x hPx,
   iteratedIdentityPower_commutes_with_second_power P (RP a) a
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) r x hPx,
   iteratedIdentityPower_three_tier_bounds_on_secondPower P (RP a) a ha
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) r x hPx⟩

/-- Higher-power `Dom(G²)` membership, `G`/`G²` commutation, and 3-tier bounds for `G`. -/
theorem growing_iteratedIdentityPower_secondPower_comm_and_bounds
    (a : ℝ) (ha : 0 < a) (r : ℕ) (x : (G).domain) (hGx : G x ∈ (G).domain) :
    iteratedIdentityPower (RG a) a r (x : Hilbert) ∈ secondPowerDomain G ∧
    (iteratedIdentityPower (RG a) a r (x : Hilbert),
      iteratedIdentityPower (RG a) a r (G x)) ∈ secondPowerGraph G ∧
    (G ⟨iteratedIdentityPower (RG a) a r (x : Hilbert),
        iteratedIdentityPower_mem_domain_of_mem_domain G (RG a) a
          (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
          (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) r x⟩ =
      iteratedIdentityPower (RG a) a r (G x) ∧
     G ⟨iteratedIdentityPower (RG a) a r (G x),
        iteratedIdentityPower_mem_domain_of_mem_domain G (RG a) a
          (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
          (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) r ⟨G x, hGx⟩⟩ =
      iteratedIdentityPower (RG a) a r (G ⟨G x, hGx⟩)) ∧
    ‖iteratedIdentityPower (RG a) a r (x : Hilbert) - (x : Hilbert)‖ ≤ (r : ℝ) * a⁻¹ * ‖G x‖ ∧
    ‖iteratedIdentityPower (RG a) a r (G x) - G x‖ ≤ (r : ℝ) * a⁻¹ * ‖G ⟨G x, hGx⟩‖ ∧
    ‖iteratedIdentityPower (RG a) a r (G ⟨G x, hGx⟩) - G ⟨G x, hGx⟩‖ ≤ 2 * ‖G ⟨G x, hGx⟩‖ :=
  ⟨iteratedIdentityPower_mem_secondPowerDomain_of_secondPower G (RG a) a
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) r x hGx,
   iteratedIdentityPower_mem_secondPowerGraph_of_secondPower G (RG a) a
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) r x hGx,
   iteratedIdentityPower_commutes_with_second_power G (RG a) a
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) r x hGx,
   iteratedIdentityPower_three_tier_bounds_on_secondPower G (RG a) a ha
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) r x hGx⟩

/-- Higher-power `Dom(S(t)²)` membership, `S(t)`/`S(t)²` commutation, and 3-tier bounds for `S t`. -/
theorem residual_iteratedIdentityPower_secondPower_comm_and_bounds
    (t a : ℝ) (ha : 0 < a) (r : ℕ) (x : (S t).domain) (hSx : S t x ∈ (S t).domain) :
    iteratedIdentityPower (RS t a) a r (x : Hilbert) ∈ secondPowerDomain (S t) ∧
    (iteratedIdentityPower (RS t a) a r (x : Hilbert),
      iteratedIdentityPower (RS t a) a r (S t x)) ∈ secondPowerGraph (S t) ∧
    (S t ⟨iteratedIdentityPower (RS t a) a r (x : Hilbert),
          iteratedIdentityPower_mem_domain_of_mem_domain (S t) (RS t a) a
            (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
            (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) r x⟩ =
      iteratedIdentityPower (RS t a) a r (S t x) ∧
     S t ⟨iteratedIdentityPower (RS t a) a r (S t x),
          iteratedIdentityPower_mem_domain_of_mem_domain (S t) (RS t a) a
            (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
            (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha)
            r ⟨S t x, hSx⟩⟩ =
      iteratedIdentityPower (RS t a) a r (S t ⟨S t x, hSx⟩)) ∧
    ‖iteratedIdentityPower (RS t a) a r (x : Hilbert) - (x : Hilbert)‖ ≤
      (r : ℝ) * a⁻¹ * ‖S t x‖ ∧
    ‖iteratedIdentityPower (RS t a) a r (S t x) - S t x‖ ≤
      (r : ℝ) * a⁻¹ * ‖S t ⟨S t x, hSx⟩‖ ∧
    ‖iteratedIdentityPower (RS t a) a r (S t ⟨S t x, hSx⟩) - S t ⟨S t x, hSx⟩‖ ≤
      2 * ‖S t ⟨S t x, hSx⟩‖ :=
  ⟨iteratedIdentityPower_mem_secondPowerDomain_of_secondPower (S t) (RS t a) a
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) r x hSx,
   iteratedIdentityPower_mem_secondPowerGraph_of_secondPower (S t) (RS t a) a
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) r x hSx,
   iteratedIdentityPower_commutes_with_second_power (S t) (RS t a) a
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) r x hSx,
   iteratedIdentityPower_three_tier_bounds_on_secondPower (S t) (RS t a) a ha
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) r x hSx⟩

/-- Higher-power `Dom(H(t)²)` membership, `H(t)`/`H(t)²` commutation, and 3-tier bounds for `H t`. -/
theorem hamiltonian_iteratedIdentityPower_secondPower_comm_and_bounds
    (t a : ℝ) (ha : 0 < a) (r : ℕ) (x : (H t).domain) (hHx : H t x ∈ (H t).domain) :
    iteratedIdentityPower (RH t a) a r (x : Hilbert) ∈ secondPowerDomain (H t) ∧
    (iteratedIdentityPower (RH t a) a r (x : Hilbert),
      iteratedIdentityPower (RH t a) a r (H t x)) ∈ secondPowerGraph (H t) ∧
    (H t ⟨iteratedIdentityPower (RH t a) a r (x : Hilbert),
          iteratedIdentityPower_mem_domain_of_mem_domain (H t) (RH t a) a
            (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
            (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) r x⟩ =
      iteratedIdentityPower (RH t a) a r (H t x) ∧
     H t ⟨iteratedIdentityPower (RH t a) a r (H t x),
          iteratedIdentityPower_mem_domain_of_mem_domain (H t) (RH t a) a
            (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
            (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha)
            r ⟨H t x, hHx⟩⟩ =
      iteratedIdentityPower (RH t a) a r (H t ⟨H t x, hHx⟩)) ∧
    ‖iteratedIdentityPower (RH t a) a r (x : Hilbert) - (x : Hilbert)‖ ≤
      (r : ℝ) * a⁻¹ * ‖H t x‖ ∧
    ‖iteratedIdentityPower (RH t a) a r (H t x) - H t x‖ ≤
      (r : ℝ) * a⁻¹ * ‖H t ⟨H t x, hHx⟩‖ ∧
    ‖iteratedIdentityPower (RH t a) a r (H t ⟨H t x, hHx⟩) - H t ⟨H t x, hHx⟩‖ ≤
      2 * ‖H t ⟨H t x, hHx⟩‖ :=
  ⟨iteratedIdentityPower_mem_secondPowerDomain_of_secondPower (H t) (RH t a) a
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) r x hHx,
   iteratedIdentityPower_mem_secondPowerGraph_of_secondPower (H t) (RH t a) a
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) r x hHx,
   iteratedIdentityPower_commutes_with_second_power (H t) (RH t a) a
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) r x hHx,
   iteratedIdentityPower_three_tier_bounds_on_secondPower (H t) (RH t a) a ha
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) r x hHx⟩

/-- Quantitative 3-tier `O(r * a⁻¹)` rate bounds on `Dom(T³)` for `T`. -/
theorem static_iteratedIdentityPower_thirdPower_rate_bounds
    (a : ℝ) (ha : 0 < a) (r : ℕ)
    (x : (T).domain) (hTx : T x ∈ (T).domain) (hTTx : T ⟨T x, hTx⟩ ∈ (T).domain) :
    ‖iteratedIdentityPower (RT a) a r (x : Hilbert) - (x : Hilbert)‖ ≤ (r : ℝ) * a⁻¹ * ‖T x‖ ∧
    ‖iteratedIdentityPower (RT a) a r (T x) - T x‖ ≤ (r : ℝ) * a⁻¹ * ‖T ⟨T x, hTx⟩‖ ∧
    ‖iteratedIdentityPower (RT a) a r (T ⟨T x, hTx⟩) - T ⟨T x, hTx⟩‖ ≤
      (r : ℝ) * a⁻¹ * ‖T ⟨T ⟨T x, hTx⟩, hTTx⟩‖ :=
  iteratedIdentityPower_three_tier_rate_bounds_on_thirdPower T (RT a) a ha
    (staticResolvent_resolves ε hε h hb hh a ha)
    (staticOperator_positive ε hε h)
    (staticResolvent_left_inverse ε hε h hb hh a ha) r x hTx hTTx

/-- Quantitative 3-tier `O(r * a⁻¹)` rate bounds on `Dom(P³)` for `P`. -/
theorem potential_iteratedIdentityPower_thirdPower_rate_bounds
    (a : ℝ) (ha : 0 < a) (r : ℕ)
    (x : (P).domain) (hPx : P x ∈ (P).domain) (hPPx : P ⟨P x, hPx⟩ ∈ (P).domain) :
    ‖iteratedIdentityPower (RP a) a r (x : Hilbert) - (x : Hilbert)‖ ≤ (r : ℝ) * a⁻¹ * ‖P x‖ ∧
    ‖iteratedIdentityPower (RP a) a r (P x) - P x‖ ≤ (r : ℝ) * a⁻¹ * ‖P ⟨P x, hPx⟩‖ ∧
    ‖iteratedIdentityPower (RP a) a r (P ⟨P x, hPx⟩) - P ⟨P x, hPx⟩‖ ≤
      (r : ℝ) * a⁻¹ * ‖P ⟨P ⟨P x, hPx⟩, hPPx⟩‖ :=
  iteratedIdentityPower_three_tier_rate_bounds_on_thirdPower P (RP a) a ha
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
    (KFCausalClosedGraphForm.hamiltonian_positive PD)
    (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha)
    r x hPx hPPx

/-- Quantitative 3-tier `O(r * a⁻¹)` rate bounds on `Dom(G³)` for `G`. -/
theorem growing_iteratedIdentityPower_thirdPower_rate_bounds
    (a : ℝ) (ha : 0 < a) (r : ℕ)
    (x : (G).domain) (hGx : G x ∈ (G).domain) (hGGx : G ⟨G x, hGx⟩ ∈ (G).domain) :
    ‖iteratedIdentityPower (RG a) a r (x : Hilbert) - (x : Hilbert)‖ ≤ (r : ℝ) * a⁻¹ * ‖G x‖ ∧
    ‖iteratedIdentityPower (RG a) a r (G x) - G x‖ ≤ (r : ℝ) * a⁻¹ * ‖G ⟨G x, hGx⟩‖ ∧
    ‖iteratedIdentityPower (RG a) a r (G ⟨G x, hGx⟩) - G ⟨G x, hGx⟩‖ ≤
      (r : ℝ) * a⁻¹ * ‖G ⟨G ⟨G x, hGx⟩, hGGx⟩‖ :=
  iteratedIdentityPower_three_tier_rate_bounds_on_thirdPower G (RG a) a ha
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha)
    r x hGx hGGx

/-- Quantitative 3-tier `O(r * a⁻¹)` rate bounds on `Dom(S(t)³)` for `S t`. -/
theorem residual_iteratedIdentityPower_thirdPower_rate_bounds
    (t a : ℝ) (ha : 0 < a) (r : ℕ)
    (x : (S t).domain) (hSx : S t x ∈ (S t).domain) (hSSx : S t ⟨S t x, hSx⟩ ∈ (S t).domain) :
    ‖iteratedIdentityPower (RS t a) a r (x : Hilbert) - (x : Hilbert)‖ ≤
      (r : ℝ) * a⁻¹ * ‖S t x‖ ∧
    ‖iteratedIdentityPower (RS t a) a r (S t x) - S t x‖ ≤
      (r : ℝ) * a⁻¹ * ‖S t ⟨S t x, hSx⟩‖ ∧
    ‖iteratedIdentityPower (RS t a) a r (S t ⟨S t x, hSx⟩) - S t ⟨S t x, hSx⟩‖ ≤
      (r : ℝ) * a⁻¹ * ‖S t ⟨S t ⟨S t x, hSx⟩, hSSx⟩‖ :=
  iteratedIdentityPower_three_tier_rate_bounds_on_thirdPower (S t) (RS t a) a ha
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
    (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha)
    r x hSx hSSx

/-- Quantitative 3-tier `O(r * a⁻¹)` rate bounds on `Dom(H(t)³)` for `H t`. -/
theorem hamiltonian_iteratedIdentityPower_thirdPower_rate_bounds
    (t a : ℝ) (ha : 0 < a) (r : ℕ)
    (x : (H t).domain) (hHx : H t x ∈ (H t).domain) (hHHx : H t ⟨H t x, hHx⟩ ∈ (H t).domain) :
    ‖iteratedIdentityPower (RH t a) a r (x : Hilbert) - (x : Hilbert)‖ ≤
      (r : ℝ) * a⁻¹ * ‖H t x‖ ∧
    ‖iteratedIdentityPower (RH t a) a r (H t x) - H t x‖ ≤
      (r : ℝ) * a⁻¹ * ‖H t ⟨H t x, hHx⟩‖ ∧
    ‖iteratedIdentityPower (RH t a) a r (H t ⟨H t x, hHx⟩) - H t ⟨H t x, hHx⟩‖ ≤
      (r : ℝ) * a⁻¹ * ‖H t ⟨H t ⟨H t x, hHx⟩, hHHx⟩‖ :=
  iteratedIdentityPower_three_tier_rate_bounds_on_thirdPower (H t) (RH t a) a ha
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha)
    r x hHx hHHx

/-- Simultaneous 3-tier `Dom(T²)` and `Dom(P²)` sequential convergence for arbitrary `r : ℕ`. -/
theorem static_and_potential_iteratedIdentityPower_three_tier_tendsto
    (r : ℕ)
    (xT : (T).domain) (hTx : T xT ∈ (T).domain)
    (xP : (P).domain) (hPx : P xP ∈ (P).domain) :
    Tendsto (fun n : ℕ =>
      (iteratedIdentityPower (RT (cutoff n)) (cutoff n) r (xT : Hilbert),
        (iteratedIdentityPower (RT (cutoff n)) (cutoff n) r (T xT),
          iteratedIdentityPower (RT (cutoff n)) (cutoff n) r (T ⟨T xT, hTx⟩))))
      atTop (𝓝 ((xT : Hilbert), (T xT, T ⟨T xT, hTx⟩))) ∧
    Tendsto (fun n : ℕ =>
      (iteratedIdentityPower (RP (cutoff n)) (cutoff n) r (xP : Hilbert),
        (iteratedIdentityPower (RP (cutoff n)) (cutoff n) r (P xP),
          iteratedIdentityPower (RP (cutoff n)) (cutoff n) r (P ⟨P xP, hPx⟩))))
      atTop (𝓝 ((xP : Hilbert), (P xP, P ⟨P xP, hPx⟩))) :=
  ⟨(iteratedIdentityPower_three_tier_tendsto_on_secondPower T RT
     (static_selfAdjoint ε hε h).dense_domain
     (staticResolvent_resolves ε hε h hb hh)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh) r xT hTx).2,
   (iteratedIdentityPower_three_tier_tendsto_on_secondPower P RP
     (KFCausalClosedGraphForm.hamiltonian_dense PD)
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k) r xP hPx).2⟩

/-- Simultaneous 3-tier `Dom(G²)` and `Dom(S(t)²)` sequential convergence for arbitrary `r : ℕ`. -/
theorem growing_and_residual_iteratedIdentityPower_three_tier_tendsto
    (t : ℝ) (r : ℕ)
    (xG : (G).domain) (hGx : G xG ∈ (G).domain)
    (xS : (S t).domain) (hSx : S t xS ∈ (S t).domain) :
    Tendsto (fun n : ℕ =>
      (iteratedIdentityPower (RG (cutoff n)) (cutoff n) r (xG : Hilbert),
        (iteratedIdentityPower (RG (cutoff n)) (cutoff n) r (G xG),
          iteratedIdentityPower (RG (cutoff n)) (cutoff n) r (G ⟨G xG, hGx⟩))))
      atTop (𝓝 ((xG : Hilbert), (G xG, G ⟨G xG, hGx⟩))) ∧
    Tendsto (fun n : ℕ =>
      (iteratedIdentityPower (RS t (cutoff n)) (cutoff n) r (xS : Hilbert),
        (iteratedIdentityPower (RS t (cutoff n)) (cutoff n) r (S t xS),
          iteratedIdentityPower (RS t (cutoff n)) (cutoff n) r (S t ⟨S t xS, hSx⟩))))
      atTop (𝓝 ((xS : Hilbert), (S t xS, S t ⟨S t xS, hSx⟩))) :=
  ⟨(iteratedIdentityPower_three_tier_tendsto_on_secondPower G RG
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_dense ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) r xG hGx).2,
   (iteratedIdentityPower_three_tier_tendsto_on_secondPower (S t) (RS t)
     (KFCausalClosedGraphForm.hamiltonian_dense (SD t))
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t) r xS hSx).2⟩

/-- Full-Hamiltonian 3-tier `Dom(H(t)²)` sequential convergence for arbitrary `r : ℕ`
combined with unconditional five-domain time-independent stability of
`twoTimeIteratedHamiltonianYosidaDiff s t a f`. -/
theorem hamiltonian_iteratedIdentityPower_three_tier_tendsto_and_twoTime_diff
    (s t a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert)
    (xH : (H t).domain) (hHx : H t xH ∈ (H t).domain) :
    (∀ n : ℕ,
      (iteratedIdentityPower (RH t (cutoff n)) (cutoff n) r (xH : Hilbert),
        iteratedIdentityPower (RH t (cutoff n)) (cutoff n) r (H t xH)) ∈ secondPowerGraph (H t) ∧
      ‖iteratedIdentityPower (RH t (cutoff n)) (cutoff n) r (xH : Hilbert) - (xH : Hilbert)‖ ≤
        (r : ℝ) * (cutoff n)⁻¹ * ‖H t xH‖ ∧
      ‖iteratedIdentityPower (RH t (cutoff n)) (cutoff n) r (H t xH) - H t xH‖ ≤
        (r : ℝ) * (cutoff n)⁻¹ * ‖H t ⟨H t xH, hHx⟩‖ ∧
      ‖iteratedIdentityPower (RH t (cutoff n)) (cutoff n) r (H t ⟨H t xH, hHx⟩) -
        H t ⟨H t xH, hHx⟩‖ ≤ 2 * ‖H t ⟨H t xH, hHx⟩‖) ∧
    Tendsto (fun n : ℕ =>
      (iteratedIdentityPower (RH t (cutoff n)) (cutoff n) r (xH : Hilbert),
        (iteratedIdentityPower (RH t (cutoff n)) (cutoff n) r (H t xH),
          iteratedIdentityPower (RH t (cutoff n)) (cutoff n) r (H t ⟨H t xH, hHx⟩))))
      atTop (𝓝 ((xH : Hilbert), (H t xH, H t ⟨H t xH, hHx⟩))) ∧
    (let d := twoTimeIteratedHamiltonianYosidaDiff ε hε h hh hb m g k s t a f
     d ∈ (K).domain ∧
       d ∈ (Tstat).domain ∧
       d ∈ (Kroot).domain ∧
       d ∈ (Tpot).domain ∧
       d ∈ (clockHalf ε).domain) := by
  have hconv :=
    iteratedIdentityPower_three_tier_tendsto_on_secondPower (H t) (RH t)
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian_dense ε hε h hh hw m g k t)
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
      (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) r xH hHx
  exact ⟨hconv.1, hconv.2,
    twoTimeIteratedHamiltonianYosidaDiff_mem_common_time_independent_domains
      ε hε h hh hb m g k s t a ha f⟩

/-- Master 5-Operator Higher-Power `Dom(A²)` & `Dom(A³)` Yosida Graph Convergence Synthesis
across `T`, `P`, `G`, `S(t)`, and `H(t)`. -/
theorem five_operators_higher_power_second_and_third_order_yosida_convergence_master
    (t a : ℝ) (ha : 0 < a) (r : ℕ)
    (xT : (T).domain) (hTx : T xT ∈ (T).domain)
    (xP : (P).domain) (hPx : P xP ∈ (P).domain)
    (xG : (G).domain) (hGx : G xG ∈ (G).domain)
    (xS : (S t).domain) (hSx : S t xS ∈ (S t).domain)
    (xH : (H t).domain) (hHx : H t xH ∈ (H t).domain)
    (hHHx : H t ⟨H t xH, hHx⟩ ∈ (H t).domain) :
    (iteratedIdentityPower (RT a) a r (xT : Hilbert) ∈ secondPowerDomain T ∧
     iteratedIdentityPower (RP a) a r (xP : Hilbert) ∈ secondPowerDomain P ∧
     iteratedIdentityPower (RG a) a r (xG : Hilbert) ∈ secondPowerDomain G ∧
     iteratedIdentityPower (RS t a) a r (xS : Hilbert) ∈ secondPowerDomain (S t) ∧
     iteratedIdentityPower (RH t a) a r (xH : Hilbert) ∈ secondPowerDomain (H t)) ∧
    (‖iteratedIdentityPower (RH t a) a r (xH : Hilbert) - (xH : Hilbert)‖ ≤
       (r : ℝ) * a⁻¹ * ‖H t xH‖ ∧
     ‖iteratedIdentityPower (RH t a) a r (H t xH) - H t xH‖ ≤
       (r : ℝ) * a⁻¹ * ‖H t ⟨H t xH, hHx⟩‖ ∧
     ‖iteratedIdentityPower (RH t a) a r (H t ⟨H t xH, hHx⟩) - H t ⟨H t xH, hHx⟩‖ ≤
       (r : ℝ) * a⁻¹ * ‖H t ⟨H t ⟨H t xH, hHx⟩, hHHx⟩‖) ∧
    (Tendsto (fun n : ℕ =>
       (iteratedIdentityPower (RT (cutoff n)) (cutoff n) r (xT : Hilbert),
         (iteratedIdentityPower (RT (cutoff n)) (cutoff n) r (T xT),
           iteratedIdentityPower (RT (cutoff n)) (cutoff n) r (T ⟨T xT, hTx⟩))))
       atTop (𝓝 ((xT : Hilbert), (T xT, T ⟨T xT, hTx⟩))) ∧
     Tendsto (fun n : ℕ =>
       (iteratedIdentityPower (RP (cutoff n)) (cutoff n) r (xP : Hilbert),
         (iteratedIdentityPower (RP (cutoff n)) (cutoff n) r (P xP),
           iteratedIdentityPower (RP (cutoff n)) (cutoff n) r (P ⟨P xP, hPx⟩))))
       atTop (𝓝 ((xP : Hilbert), (P xP, P ⟨P xP, hPx⟩))) ∧
     Tendsto (fun n : ℕ =>
       (iteratedIdentityPower (RG (cutoff n)) (cutoff n) r (xG : Hilbert),
         (iteratedIdentityPower (RG (cutoff n)) (cutoff n) r (G xG),
           iteratedIdentityPower (RG (cutoff n)) (cutoff n) r (G ⟨G xG, hGx⟩))))
       atTop (𝓝 ((xG : Hilbert), (G xG, G ⟨G xG, hGx⟩))) ∧
     Tendsto (fun n : ℕ =>
       (iteratedIdentityPower (RS t (cutoff n)) (cutoff n) r (xS : Hilbert),
         (iteratedIdentityPower (RS t (cutoff n)) (cutoff n) r (S t xS),
           iteratedIdentityPower (RS t (cutoff n)) (cutoff n) r (S t ⟨S t xS, hSx⟩))))
       atTop (𝓝 ((xS : Hilbert), (S t xS, S t ⟨S t xS, hSx⟩))) ∧
     Tendsto (fun n : ℕ =>
       (iteratedIdentityPower (RH t (cutoff n)) (cutoff n) r (xH : Hilbert),
         (iteratedIdentityPower (RH t (cutoff n)) (cutoff n) r (H t xH),
           iteratedIdentityPower (RH t (cutoff n)) (cutoff n) r (H t ⟨H t xH, hHx⟩))))
       atTop (𝓝 ((xH : Hilbert), (H t xH, H t ⟨H t xH, hHx⟩)))) := by
  have hTP :=
    static_and_potential_iteratedIdentityPower_three_tier_tendsto
      ε hε h hh hb m g k r xT hTx xP hPx
  have hGS :=
    growing_and_residual_iteratedIdentityPower_three_tier_tendsto
      ε hε h hh hb m g k t r xG hGx xS hSx
  have hH :=
    hamiltonian_iteratedIdentityPower_three_tier_tendsto_and_twoTime_diff
      ε hε h hh hb m g k t t a ha r (xH : Hilbert) xH hHx
  exact ⟨⟨(static_iteratedIdentityPower_secondPower_comm_and_bounds
            ε hε h hh hb a ha r xT hTx).1,
          (potential_iteratedIdentityPower_secondPower_comm_and_bounds
            ε hε h hh hb m g k a ha r xP hPx).1,
          (growing_iteratedIdentityPower_secondPower_comm_and_bounds
            ε hε h hh hb m g k a ha r xG hGx).1,
          (residual_iteratedIdentityPower_secondPower_comm_and_bounds
            ε hε h hh hb m g k t a ha r xS hSx).1,
          (hamiltonian_iteratedIdentityPower_secondPower_comm_and_bounds
            ε hε h hh hb m g k t a ha r xH hHx).1⟩,
    hamiltonian_iteratedIdentityPower_thirdPower_rate_bounds
      ε hε h hh hb m g k t a ha r xH hHx hHHx,
    ⟨hTP.1, hTP.2, hGS.1, hGS.2, hH.2.1⟩⟩

#print axioms iteratedIdentityPower_mem_graph_of_mem_domain
#print axioms iteratedIdentityPower_mem_domain_of_mem_domain
#print axioms iteratedIdentityPower_commutes_with_operator
#print axioms iteratedIdentityPower_succ_mem_secondPowerGraph_of_mem_domain
#print axioms iteratedIdentityPower_mem_secondPowerGraph_of_secondPower
#print axioms iteratedIdentityPower_mem_secondPowerDomain_of_secondPower
#print axioms iteratedIdentityPower_mem_secondPowerDomain
#print axioms iteratedIdentityPower_commutes_with_second_power
#print axioms iteratedIdentityPower_second_power_defect_eq
#print axioms iteratedIdentityPower_three_tier_bounds_on_secondPower
#print axioms iteratedIdentityPower_three_tier_rate_bounds_on_thirdPower
#print axioms secondPowerGraphNormSq_nonneg
#print axioms secondPowerGraphNormSq_iteratedIdentityPower_contraction
#print axioms secondPowerGraphNormSq_defect_bound_on_secondPower
#print axioms secondPowerGraphNormSq_defect_rate_bound_on_thirdPower
#print axioms iteratedIdentityPower_sub_norm_le_mul
#print axioms iteratedIdentityPower_strong_limit_on_hilbert
#print axioms iteratedIdentityPower_three_tier_tendsto_on_secondPower
#print axioms iteratedIdentityPower_three_tier_tendsto_on_thirdPower
#print axioms static_iteratedIdentityPower_secondPower_comm_and_bounds
#print axioms potential_iteratedIdentityPower_secondPower_comm_and_bounds
#print axioms growing_iteratedIdentityPower_secondPower_comm_and_bounds
#print axioms residual_iteratedIdentityPower_secondPower_comm_and_bounds
#print axioms hamiltonian_iteratedIdentityPower_secondPower_comm_and_bounds
#print axioms static_iteratedIdentityPower_thirdPower_rate_bounds
#print axioms potential_iteratedIdentityPower_thirdPower_rate_bounds
#print axioms growing_iteratedIdentityPower_thirdPower_rate_bounds
#print axioms residual_iteratedIdentityPower_thirdPower_rate_bounds
#print axioms hamiltonian_iteratedIdentityPower_thirdPower_rate_bounds
#print axioms static_and_potential_iteratedIdentityPower_three_tier_tendsto
#print axioms growing_and_residual_iteratedIdentityPower_three_tier_tendsto
#print axioms hamiltonian_iteratedIdentityPower_three_tier_tendsto_and_twoTime_diff
#print axioms five_operators_higher_power_second_and_third_order_yosida_convergence_master

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerSecondOrderGraphConvergence
