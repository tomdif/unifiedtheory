/- Arbitrary-Order Higher-Power Operator Action Towers, Graph-Norm Contraction,
and k-th Power Yosida Graph Convergence Across All Five Clock-Floor Hamiltonians
T, P, G, S(t), and H(t):
1. Defines the total extension `totalOperator A : H → H` and the arbitrary-order
   iterated operator power `iteratedOperatorPower A : ℕ → H → H` (`0 ↦ id`,
   `n + 1 ↦ totalOperator A ∘ iteratedOperatorPower A n`), together with the
   `n`-th order squared graph norm
   `kthPowerGraphNormSq A n x := ∑ j ∈ Finset.range (n + 1), ‖iteratedOperatorPower A j x‖ ^ 2`.
2. Proves by induction on `n : ℕ` for any positive operator `A` with shifted
   resolvent `R a` (`a > 0`):
   - `x ∈ operatorPowerDomain A (n + 1) ↔ x ∈ A.domain ∧ totalOperator A x ∈ operatorPowerDomain A n`,
   - Multi-step shift: `x ∈ operatorPowerDomain A (n + s) → iteratedOperatorPower A n x ∈ operatorPowerDomain A s`,
   - Invariance of `operatorPowerDomain A n` under `iteratedIdentityPower (R a) a r` for all `r, n : ℕ`:
     `x ∈ operatorPowerDomain A n → iteratedIdentityPower (R a) a r x ∈ operatorPowerDomain A n`,
   - Exact commutation on `operatorPowerDomain A n`:
     `iteratedOperatorPower A n (iteratedIdentityPower (R a) a r x) = iteratedIdentityPower (R a) a r (iteratedOperatorPower A n x)`,
   - Uniform contraction on `operatorPowerDomain A n`:
     `‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r x)‖ ≤ ‖iteratedOperatorPower A n x‖` and
     `kthPowerGraphNormSq A n (iteratedIdentityPower (R a) a r x) ≤ kthPowerGraphNormSq A n x`,
   - Explicit `O(r * a⁻¹)` rate bound on `operatorPowerDomain A (n + 1)`:
     `‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r x) - iteratedOperatorPower A n x‖ ≤ (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower A (n + 1) x‖`,
   - Strong sequential convergence of the `n`-th operator power along `a = (m : ℝ) + 1`
     on `operatorPowerDomain A (n + 1)` and along `cutoff m` on `operatorPowerDomain A n`.
3. Instantiates arbitrary-order higher-power Yosida commutation, graph-norm
   contraction, `O(r * a⁻¹)` rate bounds, and sequential convergence across all
   five clock-floor Hamiltonians `T`, `P`, `G`, `S t`, and `H t`. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerSecondOrderGraphConvergence
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorHigherPowerResolventDifference

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence

noncomputable section

open Filter
open scoped Topology InnerProduct BigOperators
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalPositiveResolventBounds (Resolves)
open KFCausalClockFloorPotentialClockApproximation (cutoff cutoff_pos)
open KFCausalClockFloorStaticResolventRadialCommutator
  (staticOperator_positive staticResolvent staticResolvent_resolves staticResolvent_left_inverse)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain mem_operatorPowerDomain_succ_iff
   operatorPowerDomain_one_eq_domain operatorPowerDomain_le_of_le
   iteratedResolventPower
   staticPowerDomain potentialPowerDomain growingPowerDomain
   residualPowerDomain hamiltonianPowerDomain)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedIdentityPower iteratedIdentityPower_norm_le
   iteratedIdentityPower_domain_rate_bound iteratedIdentityPower_tendsto_on_domain)
open KFCausalClockFloorHigherPowerSecondOrderGraphConvergence
  (iteratedIdentityPower_mem_domain_of_mem_domain
   iteratedIdentityPower_commutes_with_operator
   iteratedIdentityPower_strong_limit_on_hilbert)
open KFCausalClockFloorFiveOperatorHigherPowerResolventDifference
  (hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
   hamiltonianResolvent_iteratedIdentityPower_comm)

/-! ### 1. Abstract Arbitrary-Order Operator Powers and `Dom(A^n)` Yosida Convergence -/

section AbstractArbitraryOrderGraphConvergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Total extension of an unbounded linear operator `A : H →ₗ.[ℂ] H` to `H → H`,
agreeing with `A ⟨x, hx⟩` for `x ∈ A.domain` and returning `0` outside `A.domain`. -/
def totalOperator (A : H →ₗ.[ℂ] H) (x : H) : H := by
  classical
  exact if hx : x ∈ A.domain then A ⟨x, hx⟩ else 0

/-- On `x : A.domain`, `totalOperator A (x : H)` coincides with `A x`. -/
theorem totalOperator_coe (A : H →ₗ.[ℂ] H) (x : A.domain) :
    totalOperator A (x : H) = A x := by
  unfold totalOperator
  exact dif_pos x.property

/-- For any `x : H` with `hx : x ∈ A.domain`, `totalOperator A x = A ⟨x, hx⟩`. -/
theorem totalOperator_of_mem_domain (A : H →ₗ.[ℂ] H) {x : H} (hx : x ∈ A.domain) :
    totalOperator A x = A ⟨x, hx⟩ := by
  unfold totalOperator
  exact dif_pos hx

/-- Characterization of `operatorPowerDomain A (n + 1)` in terms of `totalOperator A`:
`x ∈ operatorPowerDomain A (n + 1) ↔ x ∈ A.domain ∧ totalOperator A x ∈ operatorPowerDomain A n`. -/
theorem mem_operatorPowerDomain_succ_total_iff (A : H →ₗ.[ℂ] H) (n : ℕ) (x : H) :
    x ∈ operatorPowerDomain A (n + 1) ↔
      x ∈ A.domain ∧ totalOperator A x ∈ operatorPowerDomain A n := by
  rw [mem_operatorPowerDomain_succ_iff]
  constructor
  · rintro ⟨hx, hAx⟩
    rw [← totalOperator_of_mem_domain A hx] at hAx
    exact ⟨hx, hAx⟩
  · rintro ⟨hx, hAx⟩
    rw [totalOperator_of_mem_domain A hx] at hAx
    exact ⟨hx, hAx⟩

/-- The `n`-th iterated operator action `A^n : H → H` defined via `totalOperator A`. -/
def iteratedOperatorPower (A : H →ₗ.[ℂ] H) : ℕ → H → H
  | 0 => fun x => x
  | n + 1 => fun x => totalOperator A (iteratedOperatorPower A n x)

/-- Base evaluation `iteratedOperatorPower A 0 x = x`. -/
theorem iteratedOperatorPower_zero_apply (A : H →ₗ.[ℂ] H) (x : H) :
    iteratedOperatorPower A 0 x = x :=
  rfl

/-- Left-step evaluation `iteratedOperatorPower A (n + 1) x = totalOperator A (iteratedOperatorPower A n x)`. -/
theorem iteratedOperatorPower_succ_apply (A : H →ₗ.[ℂ] H) (n : ℕ) (x : H) :
    iteratedOperatorPower A (n + 1) x = totalOperator A (iteratedOperatorPower A n x) :=
  rfl

/-- Right-step evaluation `iteratedOperatorPower A (n + 1) x = iteratedOperatorPower A n (totalOperator A x)`
for all `n : ℕ` and `x : H`. -/
theorem iteratedOperatorPower_succ_right_apply (A : H →ₗ.[ℂ] H) :
    ∀ n : ℕ, ∀ x : H,
      iteratedOperatorPower A (n + 1) x = iteratedOperatorPower A n (totalOperator A x)
  | 0, _ => rfl
  | n + 1, x => by
    rw [iteratedOperatorPower_succ_apply, iteratedOperatorPower_succ_right_apply A n x,
      ← iteratedOperatorPower_succ_apply]

/-- Multi-step domain shift: if `x ∈ operatorPowerDomain A (n + s)`, then
`iteratedOperatorPower A n x ∈ operatorPowerDomain A s` for all `n, s : ℕ`. -/
theorem iteratedOperatorPower_mem_operatorPowerDomain_of_add (A : H →ₗ.[ℂ] H) :
    ∀ n s : ℕ, ∀ {x : H},
      x ∈ operatorPowerDomain A (n + s) →
        iteratedOperatorPower A n x ∈ operatorPowerDomain A s
  | 0, s, _, hx => by
    rwa [Nat.zero_add] at hx
  | n + 1, s, x, hx => by
    rw [Nat.succ_add] at hx
    rw [mem_operatorPowerDomain_succ_total_iff] at hx
    rw [iteratedOperatorPower_succ_right_apply]
    exact iteratedOperatorPower_mem_operatorPowerDomain_of_add A n s hx.2

/-- For every `x ∈ operatorPowerDomain A (n + 1)`, `iteratedOperatorPower A n x ∈ A.domain`. -/
theorem iteratedOperatorPower_mem_domain_of_mem_succ (A : H →ₗ.[ℂ] H) (n : ℕ) {x : H}
    (hx : x ∈ operatorPowerDomain A (n + 1)) :
    iteratedOperatorPower A n x ∈ A.domain := by
  rw [← operatorPowerDomain_one_eq_domain]
  exact iteratedOperatorPower_mem_operatorPowerDomain_of_add A n 1 hx

/-- Commutation of `totalOperator A` and `iteratedIdentityPower R a r` on `A.domain`. -/
theorem totalOperator_iteratedIdentityPower_comm_of_mem_domain
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (r : ℕ) {x : H} (hx : x ∈ A.domain) :
    totalOperator A (iteratedIdentityPower R a r x) =
      iteratedIdentityPower R a r (totalOperator A x) := by
  have hx_iter : iteratedIdentityPower R a r x ∈ A.domain :=
    iteratedIdentityPower_mem_domain_of_mem_domain A R a hr hl r ⟨x, hx⟩
  rw [totalOperator_of_mem_domain A hx_iter, totalOperator_of_mem_domain A hx]
  exact iteratedIdentityPower_commutes_with_operator A R a hr hl r ⟨x, hx⟩

/-- Arbitrary-order domain invariance: for every `n, r : ℕ` and `x ∈ operatorPowerDomain A n`,
`iteratedIdentityPower R a r x ∈ operatorPowerDomain A n`. -/
theorem iteratedIdentityPower_maps_operatorPowerDomain_to_self
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H)) :
    ∀ n : ℕ, ∀ r : ℕ, ∀ {x : H},
      x ∈ operatorPowerDomain A n →
        iteratedIdentityPower R a r x ∈ operatorPowerDomain A n
  | 0, _, _, _ => Submodule.mem_top
  | n + 1, r, x, hx => by
    rw [mem_operatorPowerDomain_succ_total_iff] at hx ⊢
    rcases hx with ⟨hx_dom, hAx⟩
    refine ⟨iteratedIdentityPower_mem_domain_of_mem_domain A R a hr hl r ⟨x, hx_dom⟩, ?_⟩
    rw [totalOperator_iteratedIdentityPower_comm_of_mem_domain A R a hr hl r hx_dom]
    exact iteratedIdentityPower_maps_operatorPowerDomain_to_self A R a hr hl n r hAx

/-- Arbitrary-order operator-power commutation: for every `n, r : ℕ` and
`x ∈ operatorPowerDomain A n`,
`iteratedOperatorPower A n (iteratedIdentityPower R a r x) = iteratedIdentityPower R a r (iteratedOperatorPower A n x)`. -/
theorem iteratedOperatorPower_iteratedIdentityPower_comm
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H)) :
    ∀ n : ℕ, ∀ r : ℕ, ∀ {x : H},
      x ∈ operatorPowerDomain A n →
        iteratedOperatorPower A n (iteratedIdentityPower R a r x) =
          iteratedIdentityPower R a r (iteratedOperatorPower A n x)
  | 0, _, _, _ => rfl
  | n + 1, r, x, hx => by
    rw [mem_operatorPowerDomain_succ_total_iff] at hx
    rcases hx with ⟨hx_dom, hAx⟩
    rw [iteratedOperatorPower_succ_right_apply,
      totalOperator_iteratedIdentityPower_comm_of_mem_domain A R a hr hl r hx_dom,
      iteratedOperatorPower_iteratedIdentityPower_comm A R a hr hl n r hAx,
      ← iteratedOperatorPower_succ_right_apply]

/-- Uniform contraction of the `n`-th operator power under `iteratedIdentityPower R a r`
for every `x ∈ operatorPowerDomain A n`. -/
theorem iteratedOperatorPower_iteratedIdentityPower_norm_le
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (n r : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A n) :
    ‖iteratedOperatorPower A n (iteratedIdentityPower R a r x)‖ ≤
      ‖iteratedOperatorPower A n x‖ := by
  rw [iteratedOperatorPower_iteratedIdentityPower_comm A R a hr hl n r hx]
  exact iteratedIdentityPower_norm_le A R a ha hr hp r (iteratedOperatorPower A n x)

/-- The `n`-th order squared operator-power graph norm
`∑ j ∈ Finset.range (n + 1), ‖iteratedOperatorPower A j x‖ ^ 2`. -/
def kthPowerGraphNormSq (A : H →ₗ.[ℂ] H) (n : ℕ) (x : H) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), ‖iteratedOperatorPower A j x‖ ^ 2

/-- Base evaluation `kthPowerGraphNormSq A 0 x = ‖x‖ ^ 2`. -/
theorem kthPowerGraphNormSq_zero (A : H →ₗ.[ℂ] H) (x : H) :
    kthPowerGraphNormSq A 0 x = ‖x‖ ^ 2 := by
  unfold kthPowerGraphNormSq
  simp [iteratedOperatorPower_zero_apply]

/-- Nonnegativity of `kthPowerGraphNormSq A n x` for all `n : ℕ` and `x : H`. -/
theorem kthPowerGraphNormSq_nonneg (A : H →ₗ.[ℂ] H) (n : ℕ) (x : H) :
    0 ≤ kthPowerGraphNormSq A n x := by
  unfold kthPowerGraphNormSq
  exact Finset.sum_nonneg (fun j _ => sq_nonneg _)

/-- Step recurrence for `kthPowerGraphNormSq`:
`kthPowerGraphNormSq A (n + 1) x = kthPowerGraphNormSq A n x + ‖iteratedOperatorPower A (n + 1) x‖ ^ 2`. -/
theorem kthPowerGraphNormSq_succ (A : H →ₗ.[ℂ] H) (n : ℕ) (x : H) :
    kthPowerGraphNormSq A (n + 1) x =
      kthPowerGraphNormSq A n x + ‖iteratedOperatorPower A (n + 1) x‖ ^ 2 := by
  unfold kthPowerGraphNormSq
  exact Finset.sum_range_succ _ (n + 1)

/-- Uniform contraction of the `n`-th order squared graph norm `kthPowerGraphNormSq A n`
under `iteratedIdentityPower R a r` on `operatorPowerDomain A n`. -/
theorem kthPowerGraphNormSq_iteratedIdentityPower_contraction
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (n r : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A n) :
    kthPowerGraphNormSq A n (iteratedIdentityPower R a r x) ≤
      kthPowerGraphNormSq A n x := by
  unfold kthPowerGraphNormSq
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hxj : x ∈ operatorPowerDomain A j := operatorPowerDomain_le_of_le A hjn hx
  have hnorm := iteratedOperatorPower_iteratedIdentityPower_norm_le A R a ha hr hp hl j r hxj
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- Explicit `O(r * a⁻¹)` rate bound for the `n`-th operator power on `operatorPowerDomain A (n + 1)`:
`‖iteratedOperatorPower A n (iteratedIdentityPower R a r x) - iteratedOperatorPower A n x‖ ≤ (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower A (n + 1) x‖`. -/
theorem iteratedOperatorPower_iteratedIdentityPower_rate_bound_on_succ
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (n r : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    ‖iteratedOperatorPower A n (iteratedIdentityPower R a r x) -
      iteratedOperatorPower A n x‖ ≤
      (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower A (n + 1) x‖ := by
  have hxn : x ∈ operatorPowerDomain A n :=
    operatorPowerDomain_le_of_le A (Nat.le_succ n) hx
  have hx_dom : iteratedOperatorPower A n x ∈ A.domain :=
    iteratedOperatorPower_mem_domain_of_mem_succ A n hx
  rw [iteratedOperatorPower_iteratedIdentityPower_comm A R a hr hl n r hxn,
    iteratedOperatorPower_succ_apply, totalOperator_of_mem_domain A hx_dom]
  exact iteratedIdentityPower_domain_rate_bound A R a ha hr hp hl r
    ⟨iteratedOperatorPower A n x, hx_dom⟩

/-- Simultaneous `j`-th power rate bounds for all `j ≤ n` when `x ∈ operatorPowerDomain A (n + 1)`. -/
theorem iteratedOperatorPower_all_tiers_rate_bound_of_le
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (n j r : ℕ) (hjn : j ≤ n) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    ‖iteratedOperatorPower A j (iteratedIdentityPower R a r x) -
      iteratedOperatorPower A j x‖ ≤
      (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower A (j + 1) x‖ := by
  have hxj : x ∈ operatorPowerDomain A (j + 1) :=
    operatorPowerDomain_le_of_le A (Nat.succ_le_succ hjn) hx
  exact iteratedOperatorPower_iteratedIdentityPower_rate_bound_on_succ A R a ha hr hp hl j r hxj

/-- Strong sequential convergence of `iteratedOperatorPower A n (iteratedIdentityPower (R (m + 1)) (m + 1) r x)`
to `iteratedOperatorPower A n x` as `m → ∞` for every `x ∈ operatorPowerDomain A (n + 1)`. -/
theorem iteratedOperatorPower_iteratedIdentityPower_tendsto_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hr : ∀ a : ℝ, 0 < a → Resolves A (R a) a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ a : ℝ, 0 < a → ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H))
    (n r : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    (∀ m : ℕ,
      iteratedIdentityPower (R ((m : ℝ) + 1)) ((m : ℝ) + 1) r x ∈
        operatorPowerDomain A (n + 1)) ∧
    Tendsto
      (fun m : ℕ =>
        iteratedOperatorPower A n
          (iteratedIdentityPower (R ((m : ℝ) + 1)) ((m : ℝ) + 1) r x))
      atTop (𝓝 (iteratedOperatorPower A n x)) := by
  have hpos : ∀ m : ℕ, 0 < (m : ℝ) + 1 := fun m => by positivity
  have hxn : x ∈ operatorPowerDomain A n :=
    operatorPowerDomain_le_of_le A (Nat.le_succ n) hx
  have hx_dom : iteratedOperatorPower A n x ∈ A.domain :=
    iteratedOperatorPower_mem_domain_of_mem_succ A n hx
  refine ⟨fun m =>
    iteratedIdentityPower_maps_operatorPowerDomain_to_self A (R ((m : ℝ) + 1)) ((m : ℝ) + 1)
      (hr ((m : ℝ) + 1) (hpos m)) (hl ((m : ℝ) + 1) (hpos m)) (n + 1) r hx, ?_⟩
  have hcomm :
      (fun m : ℕ =>
        iteratedOperatorPower A n
          (iteratedIdentityPower (R ((m : ℝ) + 1)) ((m : ℝ) + 1) r x)) =
      (fun m : ℕ =>
        iteratedIdentityPower (R ((m : ℝ) + 1)) ((m : ℝ) + 1) r
          (iteratedOperatorPower A n x)) := by
    ext m
    exact iteratedOperatorPower_iteratedIdentityPower_comm A (R ((m : ℝ) + 1)) ((m : ℝ) + 1)
      (hr ((m : ℝ) + 1) (hpos m)) (hl ((m : ℝ) + 1) (hpos m)) n r hxn
  rw [hcomm]
  exact (iteratedIdentityPower_tendsto_on_domain A R hr hp hl r
    ⟨iteratedOperatorPower A n x, hx_dom⟩).2

/-- Strong sequential convergence along `cutoff m` on `operatorPowerDomain A n` when `A.domain`
is dense in `H`. -/
theorem iteratedOperatorPower_iteratedIdentityPower_tendsto_cutoff_on_powerDomain
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hd : Dense (A.domain : Set H))
    (hr : ∀ a : ℝ, 0 < a → Resolves A (R a) a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ a : ℝ, 0 < a → ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H))
    (n r : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A n) :
    Tendsto
      (fun m : ℕ =>
        iteratedOperatorPower A n
          (iteratedIdentityPower (R (cutoff m)) (cutoff m) r x))
      atTop (𝓝 (iteratedOperatorPower A n x)) := by
  have hcomm :
      (fun m : ℕ =>
        iteratedOperatorPower A n
          (iteratedIdentityPower (R (cutoff m)) (cutoff m) r x)) =
      (fun m : ℕ =>
        iteratedIdentityPower (R (cutoff m)) (cutoff m) r
          (iteratedOperatorPower A n x)) := by
    ext m
    exact iteratedOperatorPower_iteratedIdentityPower_comm A (R (cutoff m)) (cutoff m)
      (hr (cutoff m) (cutoff_pos m)) (hl (cutoff m) (cutoff_pos m)) n r hx
  rw [hcomm]
  exact iteratedIdentityPower_strong_limit_on_hilbert A R hd hr hp hl r
    (iteratedOperatorPower A n x)

end AbstractArbitraryOrderGraphConvergence

/-! ### 2. Concrete Arbitrary-Order `Dom(A^n)` Convergence for `T`, `P`, `G`, `S(t)`, and `H(t)` -/

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

/-- Arbitrary-order `staticPowerDomain` invariance, commutation, and `kthPowerGraphNormSq`
contraction for the static clock-floor operator `T`. -/
theorem static_arbitraryOrder_comm_and_graphNorm_contraction
    (a : ℝ) (ha : 0 < a) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ staticPowerDomain ε hε h n) :
    iteratedIdentityPower (RT a) a r x ∈ staticPowerDomain ε hε h n ∧
    iteratedOperatorPower T n (iteratedIdentityPower (RT a) a r x) =
      iteratedIdentityPower (RT a) a r (iteratedOperatorPower T n x) ∧
    ‖iteratedOperatorPower T n (iteratedIdentityPower (RT a) a r x)‖ ≤
      ‖iteratedOperatorPower T n x‖ ∧
    kthPowerGraphNormSq T n (iteratedIdentityPower (RT a) a r x) ≤
      kthPowerGraphNormSq T n x :=
  ⟨iteratedIdentityPower_maps_operatorPowerDomain_to_self T (RT a) a
     (staticResolvent_resolves ε hε h hb hh a ha)
     (staticResolvent_left_inverse ε hε h hb hh a ha) n r hx,
   iteratedOperatorPower_iteratedIdentityPower_comm T (RT a) a
     (staticResolvent_resolves ε hε h hb hh a ha)
     (staticResolvent_left_inverse ε hε h hb hh a ha) n r hx,
   iteratedOperatorPower_iteratedIdentityPower_norm_le T (RT a) a ha
     (staticResolvent_resolves ε hε h hb hh a ha)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh a ha) n r hx,
   kthPowerGraphNormSq_iteratedIdentityPower_contraction T (RT a) a ha
     (staticResolvent_resolves ε hε h hb hh a ha)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh a ha) n r hx⟩

/-- Arbitrary-order `O(r * a⁻¹)` rate bound and sequential convergence on
`staticPowerDomain ε hε h (n + 1)` for `T`. -/
theorem static_arbitraryOrder_rate_and_tendsto_on_succ
    (a : ℝ) (ha : 0 < a) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ staticPowerDomain ε hε h (n + 1)) :
    ‖iteratedOperatorPower T n (iteratedIdentityPower (RT a) a r x) -
      iteratedOperatorPower T n x‖ ≤
      (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower T (n + 1) x‖ ∧
    Tendsto
      (fun m : ℕ =>
        iteratedOperatorPower T n
          (iteratedIdentityPower (RT ((m : ℝ) + 1)) ((m : ℝ) + 1) r x))
      atTop (𝓝 (iteratedOperatorPower T n x)) :=
  ⟨iteratedOperatorPower_iteratedIdentityPower_rate_bound_on_succ T (RT a) a ha
     (staticResolvent_resolves ε hε h hb hh a ha)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh a ha) n r hx,
   (iteratedOperatorPower_iteratedIdentityPower_tendsto_on_succ T RT
     (staticResolvent_resolves ε hε h hb hh)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh) n r hx).2⟩

/-- Arbitrary-order `potentialPowerDomain` invariance, commutation, and `kthPowerGraphNormSq`
contraction for the potential clock-floor Hamiltonian `P`. -/
theorem potential_arbitraryOrder_comm_and_graphNorm_contraction
    (a : ℝ) (ha : 0 < a) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ potentialPowerDomain ε hε h hh hb m g k n) :
    iteratedIdentityPower (RP a) a r x ∈ potentialPowerDomain ε hε h hh hb m g k n ∧
    iteratedOperatorPower P n (iteratedIdentityPower (RP a) a r x) =
      iteratedIdentityPower (RP a) a r (iteratedOperatorPower P n x) ∧
    ‖iteratedOperatorPower P n (iteratedIdentityPower (RP a) a r x)‖ ≤
      ‖iteratedOperatorPower P n x‖ ∧
    kthPowerGraphNormSq P n (iteratedIdentityPower (RP a) a r x) ≤
      kthPowerGraphNormSq P n x :=
  ⟨iteratedIdentityPower_maps_operatorPowerDomain_to_self P (RP a) a
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) n r hx,
   iteratedOperatorPower_iteratedIdentityPower_comm P (RP a) a
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) n r hx,
   iteratedOperatorPower_iteratedIdentityPower_norm_le P (RP a) a ha
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) n r hx,
   kthPowerGraphNormSq_iteratedIdentityPower_contraction P (RP a) a ha
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) n r hx⟩

/-- Arbitrary-order `O(r * a⁻¹)` rate bound and sequential convergence on
`potentialPowerDomain ε hε h hh hb m g k (n + 1)` for `P`. -/
theorem potential_arbitraryOrder_rate_and_tendsto_on_succ
    (a : ℝ) (ha : 0 < a) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ potentialPowerDomain ε hε h hh hb m g k (n + 1)) :
    ‖iteratedOperatorPower P n (iteratedIdentityPower (RP a) a r x) -
      iteratedOperatorPower P n x‖ ≤
      (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower P (n + 1) x‖ ∧
    Tendsto
      (fun j : ℕ =>
        iteratedOperatorPower P n
          (iteratedIdentityPower (RP ((j : ℝ) + 1)) ((j : ℝ) + 1) r x))
      atTop (𝓝 (iteratedOperatorPower P n x)) :=
  ⟨iteratedOperatorPower_iteratedIdentityPower_rate_bound_on_succ P (RP a) a ha
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) n r hx,
   (iteratedOperatorPower_iteratedIdentityPower_tendsto_on_succ P RP
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k) n r hx).2⟩

/-- Arbitrary-order `growingPowerDomain` invariance, commutation, and `kthPowerGraphNormSq`
contraction for the growing clock-floor Hamiltonian `G`. -/
theorem growing_arbitraryOrder_comm_and_graphNorm_contraction
    (a : ℝ) (ha : 0 < a) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ growingPowerDomain ε hε h hh hb m g k n) :
    iteratedIdentityPower (RG a) a r x ∈ growingPowerDomain ε hε h hh hb m g k n ∧
    iteratedOperatorPower G n (iteratedIdentityPower (RG a) a r x) =
      iteratedIdentityPower (RG a) a r (iteratedOperatorPower G n x) ∧
    ‖iteratedOperatorPower G n (iteratedIdentityPower (RG a) a r x)‖ ≤
      ‖iteratedOperatorPower G n x‖ ∧
    kthPowerGraphNormSq G n (iteratedIdentityPower (RG a) a r x) ≤
      kthPowerGraphNormSq G n x :=
  ⟨iteratedIdentityPower_maps_operatorPowerDomain_to_self G (RG a) a
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) n r hx,
   iteratedOperatorPower_iteratedIdentityPower_comm G (RG a) a
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) n r hx,
   iteratedOperatorPower_iteratedIdentityPower_norm_le G (RG a) a ha
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) n r hx,
   kthPowerGraphNormSq_iteratedIdentityPower_contraction G (RG a) a ha
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) n r hx⟩

/-- Arbitrary-order `O(r * a⁻¹)` rate bound and sequential convergence on
`growingPowerDomain ε hε h hh hb m g k (n + 1)` for `G`. -/
theorem growing_arbitraryOrder_rate_and_tendsto_on_succ
    (a : ℝ) (ha : 0 < a) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ growingPowerDomain ε hε h hh hb m g k (n + 1)) :
    ‖iteratedOperatorPower G n (iteratedIdentityPower (RG a) a r x) -
      iteratedOperatorPower G n x‖ ≤
      (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower G (n + 1) x‖ ∧
    Tendsto
      (fun j : ℕ =>
        iteratedOperatorPower G n
          (iteratedIdentityPower (RG ((j : ℝ) + 1)) ((j : ℝ) + 1) r x))
      atTop (𝓝 (iteratedOperatorPower G n x)) :=
  ⟨iteratedOperatorPower_iteratedIdentityPower_rate_bound_on_succ G (RG a) a ha
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) n r hx,
   (iteratedOperatorPower_iteratedIdentityPower_tendsto_on_succ G RG
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) n r hx).2⟩

/-- Arbitrary-order `residualPowerDomain` invariance, commutation, and `kthPowerGraphNormSq`
contraction for the residual clock-floor Hamiltonian `S t`. -/
theorem residual_arbitraryOrder_comm_and_graphNorm_contraction
    (t a : ℝ) (ha : 0 < a) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ residualPowerDomain ε hε h hh hb m g k t n) :
    iteratedIdentityPower (RS t a) a r x ∈ residualPowerDomain ε hε h hh hb m g k t n ∧
    iteratedOperatorPower (S t) n (iteratedIdentityPower (RS t a) a r x) =
      iteratedIdentityPower (RS t a) a r (iteratedOperatorPower (S t) n x) ∧
    ‖iteratedOperatorPower (S t) n (iteratedIdentityPower (RS t a) a r x)‖ ≤
      ‖iteratedOperatorPower (S t) n x‖ ∧
    kthPowerGraphNormSq (S t) n (iteratedIdentityPower (RS t a) a r x) ≤
      kthPowerGraphNormSq (S t) n x :=
  ⟨iteratedIdentityPower_maps_operatorPowerDomain_to_self (S t) (RS t a) a
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) n r hx,
   iteratedOperatorPower_iteratedIdentityPower_comm (S t) (RS t a) a
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) n r hx,
   iteratedOperatorPower_iteratedIdentityPower_norm_le (S t) (RS t a) a ha
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) n r hx,
   kthPowerGraphNormSq_iteratedIdentityPower_contraction (S t) (RS t a) a ha
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) n r hx⟩

/-- Arbitrary-order `O(r * a⁻¹)` rate bound and sequential convergence on
`residualPowerDomain ε hε h hh hb m g k t (n + 1)` for `S t`. -/
theorem residual_arbitraryOrder_rate_and_tendsto_on_succ
    (t a : ℝ) (ha : 0 < a) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ residualPowerDomain ε hε h hh hb m g k t (n + 1)) :
    ‖iteratedOperatorPower (S t) n (iteratedIdentityPower (RS t a) a r x) -
      iteratedOperatorPower (S t) n x‖ ≤
      (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower (S t) (n + 1) x‖ ∧
    Tendsto
      (fun j : ℕ =>
        iteratedOperatorPower (S t) n
          (iteratedIdentityPower (RS t ((j : ℝ) + 1)) ((j : ℝ) + 1) r x))
      atTop (𝓝 (iteratedOperatorPower (S t) n x)) :=
  ⟨iteratedOperatorPower_iteratedIdentityPower_rate_bound_on_succ (S t) (RS t a) a ha
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) n r hx,
   (iteratedOperatorPower_iteratedIdentityPower_tendsto_on_succ (S t) (RS t)
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t) n r hx).2⟩

/-- Arbitrary-order `hamiltonianPowerDomain` invariance, commutation, and `kthPowerGraphNormSq`
contraction for the full clock-floor Hamiltonian `H t`. -/
theorem hamiltonian_arbitraryOrder_comm_and_graphNorm_contraction
    (t a : ℝ) (ha : 0 < a) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t n) :
    iteratedIdentityPower (RH t a) a r x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t n ∧
    iteratedOperatorPower (H t) n (iteratedIdentityPower (RH t a) a r x) =
      iteratedIdentityPower (RH t a) a r (iteratedOperatorPower (H t) n x) ∧
    ‖iteratedOperatorPower (H t) n (iteratedIdentityPower (RH t a) a r x)‖ ≤
      ‖iteratedOperatorPower (H t) n x‖ ∧
    kthPowerGraphNormSq (H t) n (iteratedIdentityPower (RH t a) a r x) ≤
      kthPowerGraphNormSq (H t) n x :=
  ⟨iteratedIdentityPower_maps_operatorPowerDomain_to_self (H t) (RH t a) a
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) n r hx,
   iteratedOperatorPower_iteratedIdentityPower_comm (H t) (RH t a) a
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) n r hx,
   iteratedOperatorPower_iteratedIdentityPower_norm_le (H t) (RH t a) a ha
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) n r hx,
   kthPowerGraphNormSq_iteratedIdentityPower_contraction (H t) (RH t a) a ha
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) n r hx⟩

/-- Arbitrary-order `O(r * a⁻¹)` rate bound and sequential convergence on
`hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)` for `H t`. -/
theorem hamiltonian_arbitraryOrder_rate_and_tendsto_on_succ
    (t a : ℝ) (ha : 0 < a) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)) :
    ‖iteratedOperatorPower (H t) n (iteratedIdentityPower (RH t a) a r x) -
      iteratedOperatorPower (H t) n x‖ ≤
      (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower (H t) (n + 1) x‖ ∧
    Tendsto
      (fun j : ℕ =>
        iteratedOperatorPower (H t) n
          (iteratedIdentityPower (RH t ((j : ℝ) + 1)) ((j : ℝ) + 1) r x))
      atTop (𝓝 (iteratedOperatorPower (H t) n x)) :=
  ⟨iteratedOperatorPower_iteratedIdentityPower_rate_bound_on_succ (H t) (RH t a) a ha
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) n r hx,
   (iteratedOperatorPower_iteratedIdentityPower_tendsto_on_succ (H t) (RH t)
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) n r hx).2⟩

/-- Unconditionally for EVERY `f : Hilbert`, `a > 0`, `b > 0`, and `n, r : ℕ`, the
`(n + 1)`-fold full-Hamiltonian resolvent difference
`d := iteratedResolventPower (RH t a) (n + 1) f - iteratedResolventPower (RH t b) (n + 1) f`
lies in `hamiltonianPowerDomain t (n + 2)` and therefore satisfies `(n + 1)`-th order
operator-power Yosida commutation, graph-norm contraction, `O(r * c⁻¹)` rate bound, and
sequential convergence! -/
theorem hamiltonian_resolvent_diff_arbitraryOrder_rate_and_tendsto
    (t a b c : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c)
    (n r : ℕ) (f : Hilbert) :
    let d : Hilbert :=
      iteratedResolventPower (RH t a) (n + 1) f - iteratedResolventPower (RH t b) (n + 1) f
    d ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 2) ∧
    kthPowerGraphNormSq (H t) (n + 1) (iteratedIdentityPower (RH t c) c r d) ≤
      kthPowerGraphNormSq (H t) (n + 1) d ∧
    ‖iteratedOperatorPower (H t) (n + 1) (iteratedIdentityPower (RH t c) c r d) -
      iteratedOperatorPower (H t) (n + 1) d‖ ≤
      (r : ℝ) * c⁻¹ * ‖iteratedOperatorPower (H t) (n + 2) d‖ ∧
    Tendsto
      (fun j : ℕ =>
        iteratedOperatorPower (H t) (n + 1)
          (iteratedIdentityPower (RH t ((j : ℝ) + 1)) ((j : ℝ) + 1) r d))
      atTop (𝓝 (iteratedOperatorPower (H t) (n + 1) d)) := by
  intro d
  have hd : d ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 2) :=
    hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
      ε hε h hh hb m g k t a b ha hb_pos n f
  have hd_n1 : d ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1) :=
    operatorPowerDomain_le_of_le (H t) (Nat.le_succ (n + 1)) hd
  have hcg :=
    hamiltonian_arbitraryOrder_comm_and_graphNorm_contraction
      ε hε h hh hb m g k t c hc (n + 1) r hd_n1
  have hrt :=
    hamiltonian_arbitraryOrder_rate_and_tendsto_on_succ
      ε hε h hh hb m g k t c hc (n + 1) r hd
  exact ⟨hd, hcg.2.2.2, hrt.1, hrt.2⟩

/-- Unconditionally for EVERY `f : Hilbert`, `a > 0`, `c > 0`, and `n, r : ℕ`, the
`(n + 1)`-fold full-Hamiltonian iterated resolvent `g_vec := iteratedResolventPower (RH t a) (n + 1) f`
lies in `hamiltonianPowerDomain t (n + 1)` and satisfies `n`-th order operator-power
Yosida commutation, graph-norm contraction, `O(r * c⁻¹)` rate bound, and sequential convergence. -/
theorem hamiltonian_iteratedResolventPower_succ_arbitraryOrder_rate_and_tendsto
    (t a c : ℝ) (ha : 0 < a) (hc : 0 < c) (n r : ℕ) (f : Hilbert) :
    let g_vec : Hilbert := iteratedResolventPower (RH t a) (n + 1) f
    g_vec ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1) ∧
    kthPowerGraphNormSq (H t) n (iteratedIdentityPower (RH t c) c r g_vec) ≤
      kthPowerGraphNormSq (H t) n g_vec ∧
    ‖iteratedOperatorPower (H t) n (iteratedIdentityPower (RH t c) c r g_vec) -
      iteratedOperatorPower (H t) n g_vec‖ ≤
      (r : ℝ) * c⁻¹ * ‖iteratedOperatorPower (H t) (n + 1) g_vec‖ ∧
    Tendsto
      (fun j : ℕ =>
        iteratedOperatorPower (H t) n
          (iteratedIdentityPower (RH t ((j : ℝ) + 1)) ((j : ℝ) + 1) r g_vec))
      atTop (𝓝 (iteratedOperatorPower (H t) n g_vec)) := by
  intro g_vec
  have hg : g_vec ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1) :=
    (KFCausalClockFloorHigherPowerOperatorCores.hamiltonian_iteratedResolventPower_regularity
      ε hε h hh hb m g k t a ha (n + 1) f).1
  have hg_n : g_vec ∈ hamiltonianPowerDomain ε hε h hh hb m g k t n :=
    operatorPowerDomain_le_of_le (H t) (Nat.le_succ n) hg
  have hcg :=
    hamiltonian_arbitraryOrder_comm_and_graphNorm_contraction
      ε hε h hh hb m g k t c hc n r hg_n
  have hrt :=
    hamiltonian_arbitraryOrder_rate_and_tendsto_on_succ
      ε hε h hh hb m g k t c hc n r hg
  exact ⟨hg, hcg.2.2.2, hrt.1, hrt.2⟩

/-- Master 5-Operator Arbitrary-Order Higher-Power Yosida Graph Convergence Synthesis
across `T`, `P`, `G`, `S(t)`, and `H(t)` for every `n, r : ℕ`. -/
theorem five_operators_arbitraryOrder_higher_power_yosida_convergence_master
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r s : ℕ) (f : Hilbert)
    {xT : Hilbert} (hxT : xT ∈ staticPowerDomain ε hε h (n + 1))
    {xP : Hilbert} (hxP : xP ∈ potentialPowerDomain ε hε h hh hb m g k (n + 1))
    {xG : Hilbert} (hxG : xG ∈ growingPowerDomain ε hε h hh hb m g k (n + 1))
    {xS : Hilbert} (hxS : xS ∈ residualPowerDomain ε hε h hh hb m g k t (n + 1))
    {xH : Hilbert} (hxH : xH ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)) :
    (kthPowerGraphNormSq T n (iteratedIdentityPower (RT a) a r xT) ≤
       kthPowerGraphNormSq T n xT ∧
     kthPowerGraphNormSq P n (iteratedIdentityPower (RP a) a r xP) ≤
       kthPowerGraphNormSq P n xP ∧
     kthPowerGraphNormSq G n (iteratedIdentityPower (RG a) a r xG) ≤
       kthPowerGraphNormSq G n xG ∧
     kthPowerGraphNormSq (S t) n (iteratedIdentityPower (RS t a) a r xS) ≤
       kthPowerGraphNormSq (S t) n xS ∧
     kthPowerGraphNormSq (H t) n (iteratedIdentityPower (RH t a) a r xH) ≤
       kthPowerGraphNormSq (H t) n xH) ∧
    (‖iteratedOperatorPower (H t) n (iteratedIdentityPower (RH t a) a r xH) -
        iteratedOperatorPower (H t) n xH‖ ≤
       (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower (H t) (n + 1) xH‖ ∧
     iteratedIdentityPower (RH t a) a r (iteratedIdentityPower (RH t b) b s f) =
       iteratedIdentityPower (RH t b) b s (iteratedIdentityPower (RH t a) a r f)) ∧
    (Tendsto
       (fun j : ℕ =>
         iteratedOperatorPower T n
           (iteratedIdentityPower (RT ((j : ℝ) + 1)) ((j : ℝ) + 1) r xT))
       atTop (𝓝 (iteratedOperatorPower T n xT)) ∧
     Tendsto
       (fun j : ℕ =>
         iteratedOperatorPower P n
           (iteratedIdentityPower (RP ((j : ℝ) + 1)) ((j : ℝ) + 1) r xP))
       atTop (𝓝 (iteratedOperatorPower P n xP)) ∧
     Tendsto
       (fun j : ℕ =>
         iteratedOperatorPower G n
           (iteratedIdentityPower (RG ((j : ℝ) + 1)) ((j : ℝ) + 1) r xG))
       atTop (𝓝 (iteratedOperatorPower G n xG)) ∧
     Tendsto
       (fun j : ℕ =>
         iteratedOperatorPower (S t) n
           (iteratedIdentityPower (RS t ((j : ℝ) + 1)) ((j : ℝ) + 1) r xS))
       atTop (𝓝 (iteratedOperatorPower (S t) n xS)) ∧
     Tendsto
       (fun j : ℕ =>
         iteratedOperatorPower (H t) n
           (iteratedIdentityPower (RH t ((j : ℝ) + 1)) ((j : ℝ) + 1) r xH))
       atTop (𝓝 (iteratedOperatorPower (H t) n xH))) := by
  have hxTn := operatorPowerDomain_le_of_le T (Nat.le_succ n) hxT
  have hxPn := operatorPowerDomain_le_of_le P (Nat.le_succ n) hxP
  have hxGn := operatorPowerDomain_le_of_le G (Nat.le_succ n) hxG
  have hxSn := operatorPowerDomain_le_of_le (S t) (Nat.le_succ n) hxS
  have hxHn := operatorPowerDomain_le_of_le (H t) (Nat.le_succ n) hxH
  exact ⟨⟨(static_arbitraryOrder_comm_and_graphNorm_contraction
            ε hε h hh hb a ha n r hxTn).2.2.2,
          (potential_arbitraryOrder_comm_and_graphNorm_contraction
            ε hε h hh hb m g k a ha n r hxPn).2.2.2,
          (growing_arbitraryOrder_comm_and_graphNorm_contraction
            ε hε h hh hb m g k a ha n r hxGn).2.2.2,
          (residual_arbitraryOrder_comm_and_graphNorm_contraction
            ε hε h hh hb m g k t a ha n r hxSn).2.2.2,
          (hamiltonian_arbitraryOrder_comm_and_graphNorm_contraction
            ε hε h hh hb m g k t a ha n r hxHn).2.2.2⟩,
    ⟨(hamiltonian_arbitraryOrder_rate_and_tendsto_on_succ
        ε hε h hh hb m g k t a ha n r hxH).1,
     hamiltonianResolvent_iteratedIdentityPower_comm ε hε h hh hb m g k t a b ha hb_pos r s f⟩,
    ⟨(static_arbitraryOrder_rate_and_tendsto_on_succ ε hε h hh hb a ha n r hxT).2,
     (potential_arbitraryOrder_rate_and_tendsto_on_succ ε hε h hh hb m g k a ha n r hxP).2,
     (growing_arbitraryOrder_rate_and_tendsto_on_succ ε hε h hh hb m g k a ha n r hxG).2,
     (residual_arbitraryOrder_rate_and_tendsto_on_succ ε hε h hh hb m g k t a ha n r hxS).2,
     (hamiltonian_arbitraryOrder_rate_and_tendsto_on_succ ε hε h hh hb m g k t a ha n r hxH).2⟩⟩

#print axioms totalOperator_coe
#print axioms totalOperator_of_mem_domain
#print axioms mem_operatorPowerDomain_succ_total_iff
#print axioms iteratedOperatorPower_zero_apply
#print axioms iteratedOperatorPower_succ_apply
#print axioms iteratedOperatorPower_succ_right_apply
#print axioms iteratedOperatorPower_mem_operatorPowerDomain_of_add
#print axioms iteratedOperatorPower_mem_domain_of_mem_succ
#print axioms totalOperator_iteratedIdentityPower_comm_of_mem_domain
#print axioms iteratedIdentityPower_maps_operatorPowerDomain_to_self
#print axioms iteratedOperatorPower_iteratedIdentityPower_comm
#print axioms iteratedOperatorPower_iteratedIdentityPower_norm_le
#print axioms kthPowerGraphNormSq_zero
#print axioms kthPowerGraphNormSq_nonneg
#print axioms kthPowerGraphNormSq_succ
#print axioms kthPowerGraphNormSq_iteratedIdentityPower_contraction
#print axioms iteratedOperatorPower_iteratedIdentityPower_rate_bound_on_succ
#print axioms iteratedOperatorPower_all_tiers_rate_bound_of_le
#print axioms iteratedOperatorPower_iteratedIdentityPower_tendsto_on_succ
#print axioms iteratedOperatorPower_iteratedIdentityPower_tendsto_cutoff_on_powerDomain
#print axioms static_arbitraryOrder_comm_and_graphNorm_contraction
#print axioms static_arbitraryOrder_rate_and_tendsto_on_succ
#print axioms potential_arbitraryOrder_comm_and_graphNorm_contraction
#print axioms potential_arbitraryOrder_rate_and_tendsto_on_succ
#print axioms growing_arbitraryOrder_comm_and_graphNorm_contraction
#print axioms growing_arbitraryOrder_rate_and_tendsto_on_succ
#print axioms residual_arbitraryOrder_comm_and_graphNorm_contraction
#print axioms residual_arbitraryOrder_rate_and_tendsto_on_succ
#print axioms hamiltonian_arbitraryOrder_comm_and_graphNorm_contraction
#print axioms hamiltonian_arbitraryOrder_rate_and_tendsto_on_succ
#print axioms hamiltonian_resolvent_diff_arbitraryOrder_rate_and_tendsto
#print axioms hamiltonian_iteratedResolventPower_succ_arbitraryOrder_rate_and_tendsto
#print axioms five_operators_arbitraryOrder_higher_power_yosida_convergence_master

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence
