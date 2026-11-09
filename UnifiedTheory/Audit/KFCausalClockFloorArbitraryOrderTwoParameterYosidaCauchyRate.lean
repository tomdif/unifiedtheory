/- Arbitrary-Order Operator-Power Linearity on `Dom(A^n)`, Two-Parameter Yosida Identity
Cauchy Rate Bounds on `Dom(A^{n+1})`, and `k`-th Power Graph-Norm Defect & Cauchy Convergence
Across All Five Clock-Floor Hamiltonians `T`, `P`, `G`, `S(t)`, and `H(t)`:
1. Proves by induction on `n : ℕ` that `iteratedOperatorPower A n` is additive and
   subtractive on `operatorPowerDomain A n`: for all `x, y ∈ operatorPowerDomain A n`,
   `x + y ∈ operatorPowerDomain A n`, `x - y ∈ operatorPowerDomain A n`,
   `iteratedOperatorPower A n (x + y) = iteratedOperatorPower A n x + iteratedOperatorPower A n y`,
   and `iteratedOperatorPower A n (x - y) = iteratedOperatorPower A n x - iteratedOperatorPower A n y`.
2. Establishes for any positive operator `A` with shifted resolvent family `R a` (`a > 0`):
   - Exact commutation of `iteratedOperatorPower A n` with the two-parameter Yosida
     identity difference `iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x`
     on `operatorPowerDomain A n`,
   - Uniform `2 * ‖iteratedOperatorPower A n x‖` and `4 * kthPowerGraphNormSq A n x`
     stability bounds on `operatorPowerDomain A n`,
   - Arbitrary-order two-parameter mutual Cauchy rate bound on `operatorPowerDomain A (n + 1)`:
     `‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x)‖ ≤ (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖`,
   - Full `n`-th order squared graph-norm Cauchy bound on `operatorPowerDomain A (n + 1)`:
     `kthPowerGraphNormSq A n (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x) ≤ ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq A (n + 1) x`,
   - Single-parameter `kthPowerGraphNormSq A n` defect bound and `O(a⁻²)` convergence to `0`
     along `a = (m : ℝ) + 1` on `operatorPowerDomain A (n + 1)`.
3. Instantiates arbitrary-order two-parameter Yosida Cauchy rates and `kthPowerGraphNormSq`
   Cauchy/defect bounds across all five clock-floor Hamiltonians `T`, `P`, `G`, `S(t)`, and `H(t)`. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderTwoParameterYosidaCauchyRate

noncomputable section

open Filter
open scoped Topology InnerProduct BigOperators
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalPositiveResolventBounds (Resolves)
open KFCausalClockFloorStaticResolventRadialCommutator
  (staticOperator_positive staticResolvent staticResolvent_resolves staticResolvent_left_inverse)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain operatorPowerDomain_le_of_le
   staticPowerDomain potentialPowerDomain growingPowerDomain
   residualPowerDomain hamiltonianPowerDomain)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedIdentityPower)
open KFCausalClockFloorFiveOperatorHigherPowerResolventDifference
  (iteratedIdentityPower_sub_mem_operatorPowerDomain
   iteratedIdentityPower_sub_norm_le_two
   iteratedIdentityPower_sub_domain_rate_bound)
open KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence
  (totalOperator totalOperator_of_mem_domain
   mem_operatorPowerDomain_succ_total_iff
   iteratedOperatorPower iteratedOperatorPower_zero_apply
   iteratedOperatorPower_succ_apply iteratedOperatorPower_succ_right_apply
   iteratedOperatorPower_mem_domain_of_mem_succ
   iteratedIdentityPower_maps_operatorPowerDomain_to_self
   iteratedOperatorPower_iteratedIdentityPower_comm
   kthPowerGraphNormSq kthPowerGraphNormSq_nonneg kthPowerGraphNormSq_succ
   iteratedOperatorPower_iteratedIdentityPower_rate_bound_on_succ
   iteratedOperatorPower_all_tiers_rate_bound_of_le)

/-! ### 1. Abstract Operator-Power Linearity and Two-Parameter Yosida Cauchy Rate Bounds -/

section AbstractArbitraryOrderCauchyRate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Additivity and subtractivity of `totalOperator A` on `A.domain`. -/
theorem totalOperator_add_and_sub_of_mem_domain
    (A : H →ₗ.[ℂ] H) {x y : H} (hx : x ∈ A.domain) (hy : y ∈ A.domain) :
    totalOperator A (x + y) = totalOperator A x + totalOperator A y ∧
    totalOperator A (x - y) = totalOperator A x - totalOperator A y := by
  have hadd : x + y ∈ A.domain := A.domain.add_mem hx hy
  have hsub : x - y ∈ A.domain := A.domain.sub_mem hx hy
  rw [totalOperator_of_mem_domain A hadd,
    totalOperator_of_mem_domain A hsub,
    totalOperator_of_mem_domain A hx,
    totalOperator_of_mem_domain A hy]
  exact ⟨A.map_add ⟨x, hx⟩ ⟨y, hy⟩, A.map_sub ⟨x, hx⟩ ⟨y, hy⟩⟩

/-- Inductive additivity and subtractivity of `iteratedOperatorPower A n` on
`operatorPowerDomain A n`: for all `x, y ∈ operatorPowerDomain A n`,
`iteratedOperatorPower A n (x + y) = iteratedOperatorPower A n x + iteratedOperatorPower A n y`
and `iteratedOperatorPower A n (x - y) = iteratedOperatorPower A n x - iteratedOperatorPower A n y`. -/
theorem iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain
    (A : H →ₗ.[ℂ] H) :
    ∀ n : ℕ, ∀ {x y : H},
      x ∈ operatorPowerDomain A n →
      y ∈ operatorPowerDomain A n →
        iteratedOperatorPower A n (x + y) =
          iteratedOperatorPower A n x + iteratedOperatorPower A n y ∧
        iteratedOperatorPower A n (x - y) =
          iteratedOperatorPower A n x - iteratedOperatorPower A n y
  | 0, _, _, _, _ => ⟨rfl, rfl⟩
  | n + 1, x, y, hx, hy => by
    rw [mem_operatorPowerDomain_succ_total_iff] at hx hy
    rcases hx with ⟨hx_dom, hAx⟩
    rcases hy with ⟨hy_dom, hAy⟩
    have htot := totalOperator_add_and_sub_of_mem_domain A hx_dom hy_dom
    have ih := iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain A n hAx hAy
    refine ⟨?_, ?_⟩
    · rw [iteratedOperatorPower_succ_right_apply A n (x + y), htot.1, ih.1,
        ← iteratedOperatorPower_succ_right_apply A n x,
        ← iteratedOperatorPower_succ_right_apply A n y]
    · rw [iteratedOperatorPower_succ_right_apply A n (x - y), htot.2, ih.2,
        ← iteratedOperatorPower_succ_right_apply A n x,
        ← iteratedOperatorPower_succ_right_apply A n y]

/-- Exact commutation of `iteratedOperatorPower A n` with the two-parameter Yosida identity
difference `iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x` on
`operatorPowerDomain A n`, together with `operatorPowerDomain A n` invariance of the difference. -/
theorem iteratedOperatorPower_iteratedIdentityPower_sub_comm
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (n r : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A n) :
    iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x ∈
      operatorPowerDomain A n ∧
    iteratedOperatorPower A n
      (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x) =
      iteratedOperatorPower A n (iteratedIdentityPower (R a) a r x) -
        iteratedOperatorPower A n (iteratedIdentityPower (R b) b r x) ∧
    iteratedOperatorPower A n
      (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x) =
      iteratedIdentityPower (R a) a r (iteratedOperatorPower A n x) -
        iteratedIdentityPower (R b) b r (iteratedOperatorPower A n x) := by
  have hxa : iteratedIdentityPower (R a) a r x ∈ operatorPowerDomain A n :=
    iteratedIdentityPower_maps_operatorPowerDomain_to_self A (R a) a (hr a ha) (hl a ha) n r hx
  have hxb : iteratedIdentityPower (R b) b r x ∈ operatorPowerDomain A n :=
    iteratedIdentityPower_maps_operatorPowerDomain_to_self A (R b) b (hr b hb) (hl b hb) n r hx
  have hsub := (iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain A n hxa hxb).2
  have hca := iteratedOperatorPower_iteratedIdentityPower_comm A (R a) a (hr a ha) (hl a ha) n r hx
  have hcb := iteratedOperatorPower_iteratedIdentityPower_comm A (R b) b (hr b hb) (hl b hb) n r hx
  exact ⟨(operatorPowerDomain A n).sub_mem hxa hxb, hsub, by rw [hsub, hca, hcb]⟩

/-- Uniform stability bound `2 * ‖iteratedOperatorPower A n x‖` for the `n`-th operator
power of the two-parameter Yosida identity difference on `operatorPowerDomain A n`. -/
theorem iteratedOperatorPower_iteratedIdentityPower_sub_norm_le_two
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (n r : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A n) :
    ‖iteratedOperatorPower A n
      (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x)‖ ≤
      2 * ‖iteratedOperatorPower A n x‖ := by
  rw [(iteratedOperatorPower_iteratedIdentityPower_sub_comm A R a b ha hb hr hl n r hx).2.2]
  exact iteratedIdentityPower_sub_norm_le_two A R a b ha hb hr hp r (iteratedOperatorPower A n x)

/-- Uniform `4 * kthPowerGraphNormSq A n x` bound on the `n`-th order squared graph norm
of the two-parameter Yosida identity difference on `operatorPowerDomain A n`. -/
theorem kthPowerGraphNormSq_iteratedIdentityPower_sub_le_four
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (n r : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A n) :
    kthPowerGraphNormSq A n
      (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x) ≤
      4 * kthPowerGraphNormSq A n x := by
  unfold kthPowerGraphNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hxj : x ∈ operatorPowerDomain A j := operatorPowerDomain_le_of_le A hjn hx
  have hnorm := iteratedOperatorPower_iteratedIdentityPower_sub_norm_le_two
    A R a b ha hb hr hp hl j r hxj
  have hsq : ‖iteratedOperatorPower A j
      (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x)‖ ^ 2 ≤
      (2 * ‖iteratedOperatorPower A j x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  linarith

/-- Arbitrary-order two-parameter mutual Cauchy rate bound on `operatorPowerDomain A (n + 1)`:
`‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x)‖ ≤ (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖`. -/
theorem iteratedOperatorPower_iteratedIdentityPower_cauchy_rate_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (n r : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    ‖iteratedOperatorPower A n
      (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖ := by
  have hxn : x ∈ operatorPowerDomain A n :=
    operatorPowerDomain_le_of_le A (Nat.le_succ n) hx
  have hx_dom : iteratedOperatorPower A n x ∈ A.domain :=
    iteratedOperatorPower_mem_domain_of_mem_succ A n hx
  rw [(iteratedOperatorPower_iteratedIdentityPower_sub_comm A R a b ha hb hr hl n r hxn).2.2,
    iteratedOperatorPower_succ_apply, totalOperator_of_mem_domain A hx_dom]
  exact iteratedIdentityPower_sub_domain_rate_bound A R a b ha hb hr hp hl r
    ⟨iteratedOperatorPower A n x, hx_dom⟩

/-- Simultaneous `j`-th power two-parameter Cauchy rate bounds for all `j ≤ n` when
`x ∈ operatorPowerDomain A (n + 1)`. -/
theorem iteratedOperatorPower_all_tiers_cauchy_rate_of_le
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (n j r : ℕ) (hjn : j ≤ n) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    ‖iteratedOperatorPower A j
      (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower A (j + 1) x‖ := by
  have hxj : x ∈ operatorPowerDomain A (j + 1) :=
    operatorPowerDomain_le_of_le A (Nat.succ_le_succ hjn) hx
  exact iteratedOperatorPower_iteratedIdentityPower_cauchy_rate_on_succ
    A R a b ha hb hr hp hl j r hxj

/-- Auxiliary bound comparing the shifted sum of squared operator powers
`∑ j ∈ Finset.range (n + 1), ‖iteratedOperatorPower A (j + 1) x‖ ^ 2` with
`kthPowerGraphNormSq A (n + 1) x`. -/
theorem sum_succ_iteratedOperatorPower_sq_le_kthPowerGraphNormSq_succ
    (A : H →ₗ.[ℂ] H) :
    ∀ n : ℕ, ∀ x : H,
      (∑ j ∈ Finset.range (n + 1), ‖iteratedOperatorPower A (j + 1) x‖ ^ 2) ≤
        kthPowerGraphNormSq A (n + 1) x
  | 0, x => by
    simp only [Finset.range_one, Finset.sum_singleton, zero_add]
    rw [kthPowerGraphNormSq_succ A 0 x]
    linarith [kthPowerGraphNormSq_nonneg A 0 x]
  | n + 1, x => by
    rw [Finset.sum_range_succ _ (n + 1), kthPowerGraphNormSq_succ A (n + 1) x]
    have ih := sum_succ_iteratedOperatorPower_sq_le_kthPowerGraphNormSq_succ A n x
    linarith

/-- Full `n`-th order squared graph-norm two-parameter Cauchy rate bound on
`operatorPowerDomain A (n + 1)`:
`kthPowerGraphNormSq A n (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x) ≤ ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq A (n + 1) x`. -/
theorem kthPowerGraphNormSq_iteratedIdentityPower_cauchy_rate_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (n r : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    kthPowerGraphNormSq A n
      (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x) ≤
      ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 *
        (∑ j ∈ Finset.range (n + 1), ‖iteratedOperatorPower A (j + 1) x‖ ^ 2) ∧
    kthPowerGraphNormSq A n
      (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x) ≤
      ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq A (n + 1) x := by
  have h1 :
      kthPowerGraphNormSq A n
        (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x) ≤
      ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 *
        (∑ j ∈ Finset.range (n + 1), ‖iteratedOperatorPower A (j + 1) x‖ ^ 2) := by
    unfold kthPowerGraphNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hbd := iteratedOperatorPower_all_tiers_cauchy_rate_of_le
      A R a b ha hb hr hp hl n j r hjn hx
    have hsq :
        ‖iteratedOperatorPower A j
          (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x)‖ ^ 2 ≤
        ((r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower A (j + 1) x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbd 2
    linarith [mul_pow ((r : ℝ) * (a⁻¹ + b⁻¹)) ‖iteratedOperatorPower A (j + 1) x‖ 2]
  have h2 := mul_le_mul_of_nonneg_left
    (sum_succ_iteratedOperatorPower_sq_le_kthPowerGraphNormSq_succ A n x)
    (sq_nonneg ((r : ℝ) * (a⁻¹ + b⁻¹)))
  exact ⟨h1, h1.trans h2⟩

/-- Single-parameter `kthPowerGraphNormSq A n` defect bound on `operatorPowerDomain A (n + 1)`:
`kthPowerGraphNormSq A n (iteratedIdentityPower (R a) a r x - x) ≤ ((r : ℝ) * a⁻¹) ^ 2 * kthPowerGraphNormSq A (n + 1) x`. -/
theorem kthPowerGraphNormSq_iteratedIdentityPower_defect_bound_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (n r : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    kthPowerGraphNormSq A n (iteratedIdentityPower (R a) a r x - x) ≤
      ((r : ℝ) * a⁻¹) ^ 2 * kthPowerGraphNormSq A (n + 1) x := by
  have h1 :
      kthPowerGraphNormSq A n (iteratedIdentityPower (R a) a r x - x) ≤
      ((r : ℝ) * a⁻¹) ^ 2 *
        (∑ j ∈ Finset.range (n + 1), ‖iteratedOperatorPower A (j + 1) x‖ ^ 2) := by
    unfold kthPowerGraphNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hxj : x ∈ operatorPowerDomain A j :=
      operatorPowerDomain_le_of_le A (le_trans hjn (Nat.le_succ n)) hx
    have hxa : iteratedIdentityPower (R a) a r x ∈ operatorPowerDomain A j :=
      iteratedIdentityPower_maps_operatorPowerDomain_to_self A (R a) a (hr a ha) (hl a ha) j r hxj
    have hsub := (iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain A j hxa hxj).2
    have hbd := iteratedOperatorPower_all_tiers_rate_bound_of_le
      A (R a) a ha (hr a ha) hp (hl a ha) n j r hjn hx
    rw [hsub]
    have hsq :
        ‖iteratedOperatorPower A j (iteratedIdentityPower (R a) a r x) -
          iteratedOperatorPower A j x‖ ^ 2 ≤
        ((r : ℝ) * a⁻¹ * ‖iteratedOperatorPower A (j + 1) x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbd 2
    linarith [mul_pow ((r : ℝ) * a⁻¹) ‖iteratedOperatorPower A (j + 1) x‖ 2]
  have h2 := mul_le_mul_of_nonneg_left
    (sum_succ_iteratedOperatorPower_sq_le_kthPowerGraphNormSq_succ A n x)
    (sq_nonneg ((r : ℝ) * a⁻¹))
  exact h1.trans h2

/-- Sequential convergence of the `n`-th order squared graph-norm defect
`kthPowerGraphNormSq A n (iteratedIdentityPower (R (m + 1)) (m + 1) r x - x) → 0`
as `m → ∞` for every `x ∈ operatorPowerDomain A (n + 1)`. -/
theorem tendsto_kthPowerGraphNormSq_iteratedIdentityPower_defect_zero_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (n r : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    Tendsto
      (fun m : ℕ =>
        kthPowerGraphNormSq A n
          (iteratedIdentityPower (R ((m : ℝ) + 1)) ((m : ℝ) + 1) r x - x))
      atTop (𝓝 0) := by
  have hpos : ∀ m : ℕ, 0 < (m : ℝ) + 1 := fun m => by positivity
  have hinv : Tendsto (fun m : ℕ => (((m : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hupper :
      Tendsto
        (fun m : ℕ =>
          ((r : ℝ) * (((m : ℝ) + 1))⁻¹) ^ 2 * kthPowerGraphNormSq A (n + 1) x)
        atTop (𝓝 0) := by
    have hmul : Tendsto (fun m : ℕ => (r : ℝ) * (((m : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
      simpa using hinv.const_mul (r : ℝ)
    have hsq : Tendsto (fun m : ℕ => ((r : ℝ) * (((m : ℝ) + 1))⁻¹) ^ 2) atTop (𝓝 0) := by
      simpa using hmul.pow 2
    simpa using hsq.mul_const (kthPowerGraphNormSq A (n + 1) x)
  exact squeeze_zero
    (fun m => kthPowerGraphNormSq_nonneg A n _)
    (fun m => kthPowerGraphNormSq_iteratedIdentityPower_defect_bound_on_succ
      A R ((m : ℝ) + 1) (hpos m) hr hp hl n r hx)
    hupper

end AbstractArbitraryOrderCauchyRate

/-! ### 2. Concrete Five-Operator Instantiations for `T`, `P`, `G`, `S(t)`, and `H(t)` -/

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => staticResolvent ε hε h hb hh
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k

/-- Arbitrary-order two-parameter Cauchy rate bound, `kthPowerGraphNormSq` Cauchy bound,
and sequential graph-norm defect convergence on `staticPowerDomain ε hε h (n + 1)` for `T`. -/
theorem static_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ staticPowerDomain ε hε h (n + 1)) :
    ‖iteratedOperatorPower T n
      (iteratedIdentityPower (RT a) a r x - iteratedIdentityPower (RT b) b r x)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower T (n + 1) x‖ ∧
    kthPowerGraphNormSq T n
      (iteratedIdentityPower (RT a) a r x - iteratedIdentityPower (RT b) b r x) ≤
      ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq T (n + 1) x ∧
    Tendsto
      (fun m : ℕ =>
        kthPowerGraphNormSq T n
          (iteratedIdentityPower (RT ((m : ℝ) + 1)) ((m : ℝ) + 1) r x - x))
      atTop (𝓝 0) :=
  ⟨iteratedOperatorPower_iteratedIdentityPower_cauchy_rate_on_succ T RT a b ha hb_pos
     (staticResolvent_resolves ε hε h hb hh)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh) n r hx,
   (kthPowerGraphNormSq_iteratedIdentityPower_cauchy_rate_on_succ T RT a b ha hb_pos
     (staticResolvent_resolves ε hε h hb hh)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh) n r hx).2,
   tendsto_kthPowerGraphNormSq_iteratedIdentityPower_defect_zero_on_succ T RT
     (staticResolvent_resolves ε hε h hb hh)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh) n r hx⟩

/-- Arbitrary-order two-parameter Cauchy rate bound, `kthPowerGraphNormSq` Cauchy bound,
and sequential graph-norm defect convergence on `potentialPowerDomain ε hε h hh hb m g k (n + 1)` for `P`. -/
theorem potential_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ potentialPowerDomain ε hε h hh hb m g k (n + 1)) :
    ‖iteratedOperatorPower P n
      (iteratedIdentityPower (RP a) a r x - iteratedIdentityPower (RP b) b r x)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower P (n + 1) x‖ ∧
    kthPowerGraphNormSq P n
      (iteratedIdentityPower (RP a) a r x - iteratedIdentityPower (RP b) b r x) ≤
      ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq P (n + 1) x ∧
    Tendsto
      (fun m : ℕ =>
        kthPowerGraphNormSq P n
          (iteratedIdentityPower (RP ((m : ℝ) + 1)) ((m : ℝ) + 1) r x - x))
      atTop (𝓝 0) :=
  ⟨iteratedOperatorPower_iteratedIdentityPower_cauchy_rate_on_succ P RP a b ha hb_pos
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k) n r hx,
   (kthPowerGraphNormSq_iteratedIdentityPower_cauchy_rate_on_succ P RP a b ha hb_pos
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k) n r hx).2,
   tendsto_kthPowerGraphNormSq_iteratedIdentityPower_defect_zero_on_succ P RP
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k) n r hx⟩

/-- Arbitrary-order two-parameter Cauchy rate bound, `kthPowerGraphNormSq` Cauchy bound,
and sequential graph-norm defect convergence on `growingPowerDomain ε hε h hh hb m g k (n + 1)` for `G`. -/
theorem growing_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ growingPowerDomain ε hε h hh hb m g k (n + 1)) :
    ‖iteratedOperatorPower G n
      (iteratedIdentityPower (RG a) a r x - iteratedIdentityPower (RG b) b r x)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower G (n + 1) x‖ ∧
    kthPowerGraphNormSq G n
      (iteratedIdentityPower (RG a) a r x - iteratedIdentityPower (RG b) b r x) ≤
      ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq G (n + 1) x ∧
    Tendsto
      (fun m : ℕ =>
        kthPowerGraphNormSq G n
          (iteratedIdentityPower (RG ((m : ℝ) + 1)) ((m : ℝ) + 1) r x - x))
      atTop (𝓝 0) :=
  ⟨iteratedOperatorPower_iteratedIdentityPower_cauchy_rate_on_succ G RG a b ha hb_pos
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) n r hx,
   (kthPowerGraphNormSq_iteratedIdentityPower_cauchy_rate_on_succ G RG a b ha hb_pos
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) n r hx).2,
   tendsto_kthPowerGraphNormSq_iteratedIdentityPower_defect_zero_on_succ G RG
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) n r hx⟩

/-- Arbitrary-order two-parameter Cauchy rate bound, `kthPowerGraphNormSq` Cauchy bound,
and sequential graph-norm defect convergence on `residualPowerDomain ε hε h hh hb m g k t (n + 1)` for `S t`. -/
theorem residual_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ residualPowerDomain ε hε h hh hb m g k t (n + 1)) :
    ‖iteratedOperatorPower (S t) n
      (iteratedIdentityPower (RS t a) a r x - iteratedIdentityPower (RS t b) b r x)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower (S t) (n + 1) x‖ ∧
    kthPowerGraphNormSq (S t) n
      (iteratedIdentityPower (RS t a) a r x - iteratedIdentityPower (RS t b) b r x) ≤
      ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq (S t) (n + 1) x ∧
    Tendsto
      (fun m : ℕ =>
        kthPowerGraphNormSq (S t) n
          (iteratedIdentityPower (RS t ((m : ℝ) + 1)) ((m : ℝ) + 1) r x - x))
      atTop (𝓝 0) :=
  ⟨iteratedOperatorPower_iteratedIdentityPower_cauchy_rate_on_succ (S t) (RS t) a b ha hb_pos
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t) n r hx,
   (kthPowerGraphNormSq_iteratedIdentityPower_cauchy_rate_on_succ (S t) (RS t) a b ha hb_pos
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t) n r hx).2,
   tendsto_kthPowerGraphNormSq_iteratedIdentityPower_defect_zero_on_succ (S t) (RS t)
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t) n r hx⟩

/-- Arbitrary-order two-parameter Cauchy rate bound, `kthPowerGraphNormSq` Cauchy bound,
and sequential graph-norm defect convergence on `hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)` for `H t`. -/
theorem hamiltonian_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)) :
    ‖iteratedOperatorPower (H t) n
      (iteratedIdentityPower (RH t a) a r x - iteratedIdentityPower (RH t b) b r x)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower (H t) (n + 1) x‖ ∧
    kthPowerGraphNormSq (H t) n
      (iteratedIdentityPower (RH t a) a r x - iteratedIdentityPower (RH t b) b r x) ≤
      ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq (H t) (n + 1) x ∧
    Tendsto
      (fun m : ℕ =>
        kthPowerGraphNormSq (H t) n
          (iteratedIdentityPower (RH t ((m : ℝ) + 1)) ((m : ℝ) + 1) r x - x))
      atTop (𝓝 0) :=
  ⟨iteratedOperatorPower_iteratedIdentityPower_cauchy_rate_on_succ (H t) (RH t) a b ha hb_pos
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) n r hx,
   (kthPowerGraphNormSq_iteratedIdentityPower_cauchy_rate_on_succ (H t) (RH t) a b ha hb_pos
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) n r hx).2,
   tendsto_kthPowerGraphNormSq_iteratedIdentityPower_defect_zero_on_succ (H t) (RH t)
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) n r hx⟩

/-- Master Five-Operator Arbitrary-Order Two-Parameter Yosida Cauchy Rate and
`kthPowerGraphNormSq` Defect Convergence Synthesis across `T`, `P`, `G`, `S(t)`, and `H(t)`. -/
theorem fiveOperator_arbitraryOrder_twoParameter_yosida_cauchy_rate_master_synthesis
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r : ℕ)
    {xT xP xG xS xH : Hilbert}
    (hxT : xT ∈ staticPowerDomain ε hε h (n + 1))
    (hxP : xP ∈ potentialPowerDomain ε hε h hh hb m g k (n + 1))
    (hxG : xG ∈ growingPowerDomain ε hε h hh hb m g k (n + 1))
    (hxS : xS ∈ residualPowerDomain ε hε h hh hb m g k t (n + 1))
    (hxH : xH ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)) :
    (kthPowerGraphNormSq T n
       (iteratedIdentityPower (RT a) a r xT - iteratedIdentityPower (RT b) b r xT) ≤
       ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq T (n + 1) xT ∧
     kthPowerGraphNormSq P n
       (iteratedIdentityPower (RP a) a r xP - iteratedIdentityPower (RP b) b r xP) ≤
       ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq P (n + 1) xP ∧
     kthPowerGraphNormSq G n
       (iteratedIdentityPower (RG a) a r xG - iteratedIdentityPower (RG b) b r xG) ≤
       ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq G (n + 1) xG ∧
     kthPowerGraphNormSq (S t) n
       (iteratedIdentityPower (RS t a) a r xS - iteratedIdentityPower (RS t b) b r xS) ≤
       ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq (S t) (n + 1) xS ∧
     kthPowerGraphNormSq (H t) n
       (iteratedIdentityPower (RH t a) a r xH - iteratedIdentityPower (RH t b) b r xH) ≤
       ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq (H t) (n + 1) xH) ∧
    (Tendsto
       (fun m : ℕ =>
         kthPowerGraphNormSq T n
           (iteratedIdentityPower (RT ((m : ℝ) + 1)) ((m : ℝ) + 1) r xT - xT))
       atTop (𝓝 0) ∧
     Tendsto
       (fun m : ℕ =>
         kthPowerGraphNormSq P n
           (iteratedIdentityPower (RP ((m : ℝ) + 1)) ((m : ℝ) + 1) r xP - xP))
       atTop (𝓝 0) ∧
     Tendsto
       (fun m : ℕ =>
         kthPowerGraphNormSq G n
           (iteratedIdentityPower (RG ((m : ℝ) + 1)) ((m : ℝ) + 1) r xG - xG))
       atTop (𝓝 0) ∧
     Tendsto
       (fun m : ℕ =>
         kthPowerGraphNormSq (S t) n
           (iteratedIdentityPower (RS t ((m : ℝ) + 1)) ((m : ℝ) + 1) r xS - xS))
       atTop (𝓝 0) ∧
     Tendsto
       (fun m : ℕ =>
         kthPowerGraphNormSq (H t) n
           (iteratedIdentityPower (RH t ((m : ℝ) + 1)) ((m : ℝ) + 1) r xH - xH))
       atTop (𝓝 0)) := by
  have hT := static_arbitraryOrder_twoParam_cauchy_and_defect_on_succ ε hε h hh hb a b ha hb_pos n r hxT
  have hP := potential_arbitraryOrder_twoParam_cauchy_and_defect_on_succ ε hε h hh hb m g k a b ha hb_pos n r hxP
  have hG := growing_arbitraryOrder_twoParam_cauchy_and_defect_on_succ ε hε h hh hb m g k a b ha hb_pos n r hxG
  have hS := residual_arbitraryOrder_twoParam_cauchy_and_defect_on_succ ε hε h hh hb m g k t a b ha hb_pos n r hxS
  have hH := hamiltonian_arbitraryOrder_twoParam_cauchy_and_defect_on_succ ε hε h hh hb m g k t a b ha hb_pos n r hxH
  exact ⟨⟨hT.2.1, hP.2.1, hG.2.1, hS.2.1, hH.2.1⟩,
    ⟨hT.2.2, hP.2.2, hG.2.2, hS.2.2, hH.2.2⟩⟩

#print axioms totalOperator_add_and_sub_of_mem_domain
#print axioms iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain
#print axioms iteratedOperatorPower_iteratedIdentityPower_sub_comm
#print axioms iteratedOperatorPower_iteratedIdentityPower_sub_norm_le_two
#print axioms kthPowerGraphNormSq_iteratedIdentityPower_sub_le_four
#print axioms iteratedOperatorPower_iteratedIdentityPower_cauchy_rate_on_succ
#print axioms iteratedOperatorPower_all_tiers_cauchy_rate_of_le
#print axioms sum_succ_iteratedOperatorPower_sq_le_kthPowerGraphNormSq_succ
#print axioms kthPowerGraphNormSq_iteratedIdentityPower_cauchy_rate_on_succ
#print axioms kthPowerGraphNormSq_iteratedIdentityPower_defect_bound_on_succ
#print axioms tendsto_kthPowerGraphNormSq_iteratedIdentityPower_defect_zero_on_succ
#print axioms static_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
#print axioms potential_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
#print axioms growing_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
#print axioms residual_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
#print axioms hamiltonian_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
#print axioms fiveOperator_arbitraryOrder_twoParameter_yosida_cauchy_rate_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderTwoParameterYosidaCauchyRate
