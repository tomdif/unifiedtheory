/- Arbitrary-Order Higher-Power Potential-Resolvent Radial-Yosida Tier Smoothers,
Two-Scale Defect Decompositions, and `Dom(P^m)` / `Dom(P^{m+1})` Graph Convergence:
1. Defines the arbitrary-order `j`-th tier potential-resolvent radial-Yosida state
   `arbitraryOrderPotentialResolventYosidaTierState P R J r j x := iteratedResolventPower R r (J (iteratedOperatorPower P j x))`,
   the `j`-th tier Yosida-scaled identity state
   `arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x := iteratedIdentityPower R a r (J (iteratedOperatorPower P j x))`,
   the `j`-th tier `(r + 1)`-fold shifted smoother
   `arbitraryOrderShiftedPotentialResolventYosidaTierApprox P R J a r j x`,
   and the `m`-th order squared radial-Yosida graph norms
   `arbitraryOrderPotentialYosidaGraphNormSq`,
   `arbitraryOrderPotentialYosidaDefectGraphNormSq`, and
   `arbitraryOrderPotentialYosidaRegularizerGraphNormSq`.
2. Proves by induction and across all tiers `j ≤ m`:
   - Exact base and step recurrences in both the operator tier `j` and the resolvent power `r`,
   - Unconditional `operatorPowerDomain P r` regularity at every tier `j : ℕ`,
   - Geometric tier norm decay `‖arbitraryOrderPotentialResolventYosidaTierState P R J r j x‖ ≤ (a⁻¹) ^ r * ‖J (iteratedOperatorPower P j x)‖`
     and uniform contractive stability `‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x‖ ≤ ‖J (iteratedOperatorPower P j x)‖`,
   - Uniform `m`-tier graph-norm contraction
     `arbitraryOrderPotentialYosidaGraphNormSq P R J a r m x ≤ kthPowerGraphNormSq P m x`
     for any contractive regularizer `‖J g‖ ≤ ‖g‖`,
   - Radial-Yosida defect domination
     `arbitraryOrderPotentialYosidaDefectGraphNormSq P R J a r m x ≤ arbitraryOrderPotentialYosidaRegularizerGraphNormSq P J m x`,
   - Two-scale `j`-th tier approximation rate bound on `operatorPowerDomain P (j + 1)`
     and simultaneous `(m + 1)`-tier rate bounds on `operatorPowerDomain P (m + 1)`:
     `‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x - iteratedOperatorPower P j x‖ ≤ ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ + (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower P (j + 1) x‖`,
   - Exact collapse and quantitative defect bounds for `arbitraryOrderShiftedPotentialResolventYosidaTierApprox`
     on `operatorPowerDomain P (j + 1)`.
3. Proves strong sequential convergence as `n → ∞` along any strongly convergent regularizer
   family `J n → id` across all tiers `j ≤ m` to the commuting operator-power state
   `iteratedOperatorPower P j (iteratedIdentityPower R a r x)` on `operatorPowerDomain P m`,
   together with concrete instantiations for closed-graph-form self-adjoint positive Hamiltonians
   `KFCausalClosedGraphForm.hamiltonian D` and the clock-floor potential Hamiltonian `P` with
   the radial-Yosida regularizer `action ε hε h (cutoff n)`. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaArbitraryOrderConvergence

noncomputable section

open Filter
open scoped Topology InnerProduct BigOperators
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer
  (action action_norm sequence_tendsto)
open KFCausalClockFloorPotentialClockApproximation (cutoff cutoff_pos)
open KFCausalPositiveResolventBounds
  (Resolves point point_value resolvent_apply_norm_bound)
open KFCausalClosedGraphForm
  (Data hamiltonian hamiltonian_selfAdjoint hamiltonian_positive hamiltonian_energy)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain mem_operatorPowerDomain_succ_iff
   operatorPowerDomain_one_eq_domain operatorPowerDomain_le_of_le
   resolvent_mem_operatorPowerDomain_succ
   iteratedResolventPower iteratedResolventPower_zero_apply iteratedResolventPower_succ_apply
   iteratedResolventPower_mem_operatorPowerDomain
   iteratedResolventPower_norm_bound
   potentialPowerDomain)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedResolventPower_add_apply iteratedResolventPower_succ_right_apply
   iteratedIdentityPower iteratedIdentityPower_zero iteratedIdentityPower_one
   iteratedIdentityPower_succ iteratedIdentityPower_sub
   iteratedIdentityPower_mem_operatorPowerDomain
   iteratedIdentityPower_norm_le
   iteratedIdentityPower_domain_rate_bound)
open KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence
  (totalOperator totalOperator_coe totalOperator_of_mem_domain
   mem_operatorPowerDomain_succ_total_iff
   iteratedOperatorPower iteratedOperatorPower_zero_apply
   iteratedOperatorPower_succ_apply iteratedOperatorPower_succ_right_apply
   iteratedOperatorPower_mem_operatorPowerDomain_of_add
   iteratedOperatorPower_mem_domain_of_mem_succ
   iteratedIdentityPower_maps_operatorPowerDomain_to_self
   iteratedOperatorPower_iteratedIdentityPower_comm
   iteratedOperatorPower_iteratedIdentityPower_norm_le
   kthPowerGraphNormSq kthPowerGraphNormSq_zero
   kthPowerGraphNormSq_nonneg kthPowerGraphNormSq_succ
   kthPowerGraphNormSq_iteratedIdentityPower_contraction
   iteratedOperatorPower_iteratedIdentityPower_rate_bound_on_succ
   iteratedOperatorPower_all_tiers_rate_bound_of_le
   potential_arbitraryOrder_comm_and_graphNorm_contraction
   potential_arbitraryOrder_rate_and_tendsto_on_succ)

/-! ### 1. Arbitrary-Order Potential-Resolvent Radial-Yosida Tier States and Graph Norms -/

section AbstractArbitraryOrderPotentialYosida

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The `j`-th tier `r`-fold potential-resolvent radial-Yosida state
`R^r (J (P^j x))` for an unbounded operator `P : H →ₗ.[ℂ] H`, resolvent `R : H →L[ℂ] H`,
and bounded regularizer `J : H →L[ℂ] H`. -/
def arbitraryOrderPotentialResolventYosidaTierState
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (r j : ℕ) (x : H) : H :=
  iteratedResolventPower R r (J (iteratedOperatorPower P j x))

/-- The `j`-th tier `r`-th power Yosida-scaled identity radial-Yosida state
`(a • R)^r (J (P^j x))`. -/
def arbitraryOrderPotentialIdentityYosidaTierState
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (r j : ℕ) (x : H) : H :=
  iteratedIdentityPower R a r (J (iteratedOperatorPower P j x))

/-- The `j`-th tier `(r + 1)`-fold shifted potential-resolvent radial-Yosida smoother
`R^{r+1} (J (P^{j+1} x + a • P^j x))`. -/
def arbitraryOrderShiftedPotentialResolventYosidaTierApprox
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (r j : ℕ) (x : H) : H :=
  iteratedResolventPower R (r + 1)
    (J (iteratedOperatorPower P (j + 1) x + (a : ℂ) • iteratedOperatorPower P j x))

/-- The `m`-th order squared radial-Yosida graph norm across tiers `0 ≤ j ≤ m`:
`∑ j ∈ Finset.range (m + 1), ‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x‖ ^ 2`. -/
def arbitraryOrderPotentialYosidaGraphNormSq
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (r m : ℕ) (x : H) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    ‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x‖ ^ 2

/-- The `m`-th order squared radial-Yosida defect graph norm comparing
`arbitraryOrderPotentialIdentityYosidaTierState` against `iteratedIdentityPower R a r (P^j x)`
across tiers `0 ≤ j ≤ m`. -/
def arbitraryOrderPotentialYosidaDefectGraphNormSq
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (r m : ℕ) (x : H) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    ‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x -
      iteratedIdentityPower R a r (iteratedOperatorPower P j x)‖ ^ 2

/-- The `m`-th order squared regularizer defect graph norm across tiers `0 ≤ j ≤ m`:
`∑ j ∈ Finset.range (m + 1), ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ ^ 2`. -/
def arbitraryOrderPotentialYosidaRegularizerGraphNormSq
    (P : H →ₗ.[ℂ] H) (J : H →L[ℂ] H) (m : ℕ) (x : H) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ ^ 2

/-- At tier `j = 0`, `arbitraryOrderPotentialResolventYosidaTierState P R J r 0 x = iteratedResolventPower R r (J x)`
and `arbitraryOrderPotentialIdentityYosidaTierState P R J a r 0 x = iteratedIdentityPower R a r (J x)`. -/
theorem arbitraryOrderPotentialYosidaTierState_zero_tier
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (r : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierState P R J r 0 x =
      iteratedResolventPower R r (J x) ∧
    arbitraryOrderPotentialIdentityYosidaTierState P R J a r 0 x =
      iteratedIdentityPower R a r (J x) :=
  ⟨rfl, rfl⟩

/-- At resolvent power `r = 0`, both `arbitraryOrderPotentialResolventYosidaTierState` and
`arbitraryOrderPotentialIdentityYosidaTierState` reduce to `J (iteratedOperatorPower P j x)`. -/
theorem arbitraryOrderPotentialYosidaTierState_zero_power
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierState P R J 0 j x =
      J (iteratedOperatorPower P j x) ∧
    arbitraryOrderPotentialIdentityYosidaTierState P R J a 0 j x =
      J (iteratedOperatorPower P j x) :=
  ⟨rfl, iteratedIdentityPower_zero R a (J (iteratedOperatorPower P j x))⟩

/-- Step recurrences in the resolvent power `r + 1` for
`arbitraryOrderPotentialResolventYosidaTierState` and
`arbitraryOrderPotentialIdentityYosidaTierState`. -/
theorem arbitraryOrderPotentialYosidaTierState_succ_power
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierState P R J (r + 1) j x =
      R (arbitraryOrderPotentialResolventYosidaTierState P R J r j x) ∧
    arbitraryOrderPotentialIdentityYosidaTierState P R J a (r + 1) j x =
      (a : ℂ) • R (arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x) :=
  ⟨rfl, iteratedIdentityPower_succ R a r (J (iteratedOperatorPower P j x))⟩

/-- Step recurrences in the operator tier `j + 1`: advancing from tier `j` to tier `j + 1`
coincides with evaluating tier `j` at `totalOperator P x`. -/
theorem arbitraryOrderPotentialYosidaTierState_succ_tier
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierState P R J r (j + 1) x =
      arbitraryOrderPotentialResolventYosidaTierState P R J r j (totalOperator P x) ∧
    arbitraryOrderPotentialIdentityYosidaTierState P R J a r (j + 1) x =
      arbitraryOrderPotentialIdentityYosidaTierState P R J a r j (totalOperator P x) := by
  unfold arbitraryOrderPotentialResolventYosidaTierState
    arbitraryOrderPotentialIdentityYosidaTierState
  rw [iteratedOperatorPower_succ_right_apply P j x]
  exact ⟨rfl, rfl⟩

/-- Scaling relation between `arbitraryOrderPotentialIdentityYosidaTierState` and
`arbitraryOrderPotentialResolventYosidaTierState` for all `r, j : ℕ`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierState_eq_smul
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (r j : ℕ) (x : H) :
    arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x =
      ((a ^ r : ℝ) : ℂ) • arbitraryOrderPotentialResolventYosidaTierState P R J r j x :=
  rfl

/-- Unconditional `operatorPowerDomain P r` regularity of every tier `j : ℕ` for both
`arbitraryOrderPotentialResolventYosidaTierState` and
`arbitraryOrderPotentialIdentityYosidaTierState`, and `operatorPowerDomain P (r + 1)`
regularity of `arbitraryOrderShiftedPotentialResolventYosidaTierApprox`. -/
theorem arbitraryOrderPotentialYosidaTierState_mem_operatorPowerDomain
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (hr : Resolves P R a)
    (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierState P R J r j x ∈
      operatorPowerDomain P r ∧
    arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x ∈
      operatorPowerDomain P r ∧
    arbitraryOrderShiftedPotentialResolventYosidaTierApprox P R J a r j x ∈
      operatorPowerDomain P (r + 1) :=
  ⟨iteratedResolventPower_mem_operatorPowerDomain P R a hr r
     (J (iteratedOperatorPower P j x)),
   iteratedIdentityPower_mem_operatorPowerDomain P R a hr r
     (J (iteratedOperatorPower P j x)),
   iteratedResolventPower_mem_operatorPowerDomain P R a hr (r + 1)
     (J (iteratedOperatorPower P (j + 1) x + (a : ℂ) • iteratedOperatorPower P j x))⟩

/-- First-order operator action identity on `arbitraryOrderPotentialIdentityYosidaTierState P R J a (r + 1) j x`:
`totalOperator P (arbitraryOrderPotentialIdentityYosidaTierState P R J a (r + 1) j x) = (a : ℂ) • (arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x - arbitraryOrderPotentialIdentityYosidaTierState P R J a (r + 1) j x)`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierState_first_order_action_eq
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (hr : Resolves P R a)
    (r j : ℕ) (x : H) :
    totalOperator P (arbitraryOrderPotentialIdentityYosidaTierState P R J a (r + 1) j x) =
      (a : ℂ) • (arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P R J a (r + 1) j x) := by
  let u := arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x
  have hrec :
      arbitraryOrderPotentialIdentityYosidaTierState P R J a (r + 1) j x = (a : ℂ) • R u :=
    (arbitraryOrderPotentialYosidaTierState_succ_power P R J a r j x).2
  have hdom : arbitraryOrderPotentialIdentityYosidaTierState P R J a (r + 1) j x ∈ P.domain := by
    rw [hrec]
    exact P.domain.smul_mem (a : ℂ) (point P R a hr u).property
  rw [totalOperator_of_mem_domain P hdom]
  have hsub :
      (⟨arbitraryOrderPotentialIdentityYosidaTierState P R J a (r + 1) j x, hdom⟩ : P.domain) =
        (a : ℂ) • point P R a hr u := by
    ext
    exact hrec
  rw [hsub, P.map_smul, point_value P R a hr u]
  simp only [hrec]
  rfl

/-- When `J = ContinuousLinearMap.id ℂ H` and `x ∈ operatorPowerDomain P m`, for every tier
`j ≤ m`, `arbitraryOrderPotentialIdentityYosidaTierState P R id a r j x` coincides with
the `j`-th operator power `iteratedOperatorPower P j (iteratedIdentityPower R a r x)`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierState_id_eq_iteratedOperatorPower
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves P R a)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (m r j : ℕ) (hjm : j ≤ m) {x : H} (hx : x ∈ operatorPowerDomain P m) :
    arbitraryOrderPotentialIdentityYosidaTierState P R (ContinuousLinearMap.id ℂ H) a r j x =
      iteratedOperatorPower P j (iteratedIdentityPower R a r x) := by
  have hxj : x ∈ operatorPowerDomain P j := operatorPowerDomain_le_of_le P hjm hx
  unfold arbitraryOrderPotentialIdentityYosidaTierState
  change iteratedIdentityPower R a r (iteratedOperatorPower P j x) =
    iteratedOperatorPower P j (iteratedIdentityPower R a r x)
  exact (iteratedOperatorPower_iteratedIdentityPower_comm P R a hr hl j r hxj).symm

/-! ### 2. Tier Norm Decay, Contraction, and Two-Scale Approximation Rate Bounds -/

/-- Pointwise geometric norm bound on `arbitraryOrderPotentialResolventYosidaTierState`
and uniform contractive bound on `arbitraryOrderPotentialIdentityYosidaTierState`. -/
theorem arbitraryOrderPotentialYosidaTierState_norm_bounds
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    ‖arbitraryOrderPotentialResolventYosidaTierState P R J r j x‖ ≤
      (a⁻¹) ^ r * ‖J (iteratedOperatorPower P j x)‖ ∧
    ‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x‖ ≤
      ‖J (iteratedOperatorPower P j x)‖ :=
  ⟨iteratedResolventPower_norm_bound P R a ha hr hp r (J (iteratedOperatorPower P j x)),
   iteratedIdentityPower_norm_le P R a ha hr hp r (J (iteratedOperatorPower P j x))⟩

/-- If `J` is contractive (`∀ g, ‖J g‖ ≤ ‖g‖`), then every tier `j` satisfies
`‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x‖ ≤ ‖iteratedOperatorPower P j x‖`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierState_norm_le_of_contractive
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hJ : ∀ g : H, ‖J g‖ ≤ ‖g‖) (r j : ℕ) (x : H) :
    ‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x‖ ≤
      ‖iteratedOperatorPower P j x‖ :=
  (arbitraryOrderPotentialYosidaTierState_norm_bounds P R J a ha hr hp r j x).2.trans
    (hJ (iteratedOperatorPower P j x))

/-- Nonnegativity and base-case evaluation (`m = 0`) of `arbitraryOrderPotentialYosidaGraphNormSq`,
`arbitraryOrderPotentialYosidaDefectGraphNormSq`, and
`arbitraryOrderPotentialYosidaRegularizerGraphNormSq`. -/
theorem arbitraryOrderPotentialYosidaGraphNormSq_nonneg_and_zero
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (r m : ℕ) (x : H) :
    0 ≤ arbitraryOrderPotentialYosidaGraphNormSq P R J a r m x ∧
    0 ≤ arbitraryOrderPotentialYosidaDefectGraphNormSq P R J a r m x ∧
    0 ≤ arbitraryOrderPotentialYosidaRegularizerGraphNormSq P J m x ∧
    arbitraryOrderPotentialYosidaGraphNormSq P R J a r 0 x =
      ‖iteratedIdentityPower R a r (J x)‖ ^ 2 := by
  refine ⟨Finset.sum_nonneg (fun _ _ => sq_nonneg _),
    Finset.sum_nonneg (fun _ _ => sq_nonneg _),
    Finset.sum_nonneg (fun _ _ => sq_nonneg _), ?_⟩
  unfold arbitraryOrderPotentialYosidaGraphNormSq
    arbitraryOrderPotentialIdentityYosidaTierState
  simp [iteratedOperatorPower_zero_apply]

/-- Step recurrence in `m + 1` for `arbitraryOrderPotentialYosidaGraphNormSq` and
`arbitraryOrderPotentialYosidaDefectGraphNormSq`. -/
theorem arbitraryOrderPotentialYosidaGraphNormSq_succ
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (r m : ℕ) (x : H) :
    arbitraryOrderPotentialYosidaGraphNormSq P R J a r (m + 1) x =
      arbitraryOrderPotentialYosidaGraphNormSq P R J a r m x +
        ‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r (m + 1) x‖ ^ 2 ∧
    arbitraryOrderPotentialYosidaDefectGraphNormSq P R J a r (m + 1) x =
      arbitraryOrderPotentialYosidaDefectGraphNormSq P R J a r m x +
        ‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r (m + 1) x -
          iteratedIdentityPower R a r (iteratedOperatorPower P (m + 1) x)‖ ^ 2 :=
  ⟨Finset.sum_range_succ _ (m + 1), Finset.sum_range_succ _ (m + 1)⟩

/-- Uniform `m`-tier graph-norm contraction:
`arbitraryOrderPotentialYosidaGraphNormSq P R J a r m x ≤ ∑ j ∈ Finset.range (m + 1), ‖J (iteratedOperatorPower P j x)‖ ^ 2`,
and when `∀ g, ‖J g‖ ≤ ‖g‖`,
`arbitraryOrderPotentialYosidaGraphNormSq P R J a r m x ≤ kthPowerGraphNormSq P m x`. -/
theorem arbitraryOrderPotentialYosidaGraphNormSq_contraction
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hJ : ∀ g : H, ‖J g‖ ≤ ‖g‖) (r m : ℕ) (x : H) :
    arbitraryOrderPotentialYosidaGraphNormSq P R J a r m x ≤
      ∑ j ∈ Finset.range (m + 1), ‖J (iteratedOperatorPower P j x)‖ ^ 2 ∧
    arbitraryOrderPotentialYosidaGraphNormSq P R J a r m x ≤
      kthPowerGraphNormSq P m x := by
  constructor
  · unfold arbitraryOrderPotentialYosidaGraphNormSq
    apply Finset.sum_le_sum
    intro j _
    exact pow_le_pow_left₀ (norm_nonneg _)
      (arbitraryOrderPotentialYosidaTierState_norm_bounds P R J a ha hr hp r j x).2 2
  · unfold arbitraryOrderPotentialYosidaGraphNormSq kthPowerGraphNormSq
    apply Finset.sum_le_sum
    intro j _
    exact pow_le_pow_left₀ (norm_nonneg _)
      (arbitraryOrderPotentialIdentityYosidaTierState_norm_le_of_contractive
        P R J a ha hr hp hJ r j x) 2

/-- Pointwise and `m`-tier summed radial-Yosida defect domination:
for every tier `j`,
`‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x - iteratedIdentityPower R a r (iteratedOperatorPower P j x)‖ ≤ ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖`,
and across all tiers `0 ≤ j ≤ m`,
`arbitraryOrderPotentialYosidaDefectGraphNormSq P R J a r m x ≤ arbitraryOrderPotentialYosidaRegularizerGraphNormSq P J m x`. -/
theorem arbitraryOrderPotentialYosidaDefect_bounds
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r m j : ℕ) (x : H) :
    ‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x -
        iteratedIdentityPower R a r (iteratedOperatorPower P j x)‖ ≤
      ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ ∧
    arbitraryOrderPotentialYosidaDefectGraphNormSq P R J a r m x ≤
      arbitraryOrderPotentialYosidaRegularizerGraphNormSq P J m x := by
  have hpt : ∀ k : ℕ,
      ‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r k x -
          iteratedIdentityPower R a r (iteratedOperatorPower P k x)‖ ≤
        ‖J (iteratedOperatorPower P k x) - iteratedOperatorPower P k x‖ := by
    intro k
    unfold arbitraryOrderPotentialIdentityYosidaTierState
    rw [← iteratedIdentityPower_sub]
    exact iteratedIdentityPower_norm_le P R a ha hr hp r
      (J (iteratedOperatorPower P k x) - iteratedOperatorPower P k x)
  refine ⟨hpt j, ?_⟩
  unfold arbitraryOrderPotentialYosidaDefectGraphNormSq
    arbitraryOrderPotentialYosidaRegularizerGraphNormSq
  apply Finset.sum_le_sum
  intro k _
  exact pow_le_pow_left₀ (norm_nonneg _) (hpt k) 2

/-- Two-scale defect splitting at tier `j`:
`arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x - iteratedOperatorPower P j x`
splits into the radial-Yosida regularizer defect plus the `r`-th power Yosida identity defect. -/
theorem arbitraryOrderPotentialIdentityYosidaTierState_two_scale_sub_eq
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (r j : ℕ) (x : H) :
    arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x -
        iteratedOperatorPower P j x =
      (arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x -
        iteratedIdentityPower R a r (iteratedOperatorPower P j x)) +
      (iteratedIdentityPower R a r (iteratedOperatorPower P j x) -
        iteratedOperatorPower P j x) := by
  abel

/-- Quantitative two-scale approximation rate bound at tier `j` for any
`x ∈ operatorPowerDomain P (j + 1)`:
`‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x - iteratedOperatorPower P j x‖ ≤ ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ + (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower P (j + 1) x‖`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierState_rate_bound_on_succ
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r j : ℕ) {x : H} (hx : x ∈ operatorPowerDomain P (j + 1)) :
    ‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x -
        iteratedOperatorPower P j x‖ ≤
      ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower P (j + 1) x‖ := by
  rw [arbitraryOrderPotentialIdentityYosidaTierState_two_scale_sub_eq P R J a r j x]
  have htri := norm_add_le
    (arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x -
      iteratedIdentityPower R a r (iteratedOperatorPower P j x))
    (iteratedIdentityPower R a r (iteratedOperatorPower P j x) -
      iteratedOperatorPower P j x)
  have h1 := (arbitraryOrderPotentialYosidaDefect_bounds P R J a ha hr hp r 0 j x).1
  have hx_dom : iteratedOperatorPower P j x ∈ P.domain :=
    iteratedOperatorPower_mem_domain_of_mem_succ P j hx
  have h2 :
      ‖iteratedIdentityPower R a r (iteratedOperatorPower P j x) -
          iteratedOperatorPower P j x‖ ≤
        (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower P (j + 1) x‖ := by
    rw [iteratedOperatorPower_succ_apply, totalOperator_of_mem_domain P hx_dom]
    exact iteratedIdentityPower_domain_rate_bound P R a ha hr hp hl r
      ⟨iteratedOperatorPower P j x, hx_dom⟩
  linarith

/-- Simultaneous two-scale rate bounds across all tiers `j ≤ m` whenever
`x ∈ operatorPowerDomain P (m + 1)`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierState_all_tiers_rate_bound_of_le
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (m j r : ℕ) (hjm : j ≤ m) {x : H} (hx : x ∈ operatorPowerDomain P (m + 1)) :
    ‖arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x -
        iteratedOperatorPower P j x‖ ≤
      ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hxj : x ∈ operatorPowerDomain P (j + 1) :=
    operatorPowerDomain_le_of_le P (Nat.succ_le_succ hjm) hx
  exact arbitraryOrderPotentialIdentityYosidaTierState_rate_bound_on_succ
    P R J a ha hr hp hl r j hxj

/-! ### 3. Arbitrary-Order Shifted Potential-Resolvent Smoother Collapse and Defect Bounds -/

/-- Exact left-inverse collapse of the `j`-th tier shifted smoother when `J = id`
for any `x ∈ operatorPowerDomain P (j + 1)`:
`iteratedResolventPower R (r + 1) (iteratedOperatorPower P (j + 1) x + (a : ℂ) • iteratedOperatorPower P j x) = iteratedResolventPower R r (iteratedOperatorPower P j x)`. -/
theorem arbitraryOrderShifted_left_inverse_eq_on_succ
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r j : ℕ) {x : H} (hx : x ∈ operatorPowerDomain P (j + 1)) :
    iteratedResolventPower R (r + 1)
        (iteratedOperatorPower P (j + 1) x + (a : ℂ) • iteratedOperatorPower P j x) =
      iteratedResolventPower R r (iteratedOperatorPower P j x) := by
  have hx_dom : iteratedOperatorPower P j x ∈ P.domain :=
    iteratedOperatorPower_mem_domain_of_mem_succ P j hx
  let u : P.domain := ⟨iteratedOperatorPower P j x, hx_dom⟩
  have hstep : iteratedOperatorPower P (j + 1) x = P u := by
    rw [iteratedOperatorPower_succ_apply, totalOperator_of_mem_domain P hx_dom]
  rw [hstep, iteratedResolventPower_succ_right_apply]
  have hl_u : R (P u + (a : ℂ) • (u : H)) = (u : H) := by
    simpa only [Complex.real_smul] using hl u
  rw [hl_u]

/-- Quantitative defect bound for `arbitraryOrderShiftedPotentialResolventYosidaTierApprox`
on `operatorPowerDomain P (j + 1)` against `iteratedResolventPower R r (iteratedOperatorPower P j x)`. -/
theorem arbitraryOrderShifted_defect_bound_on_succ
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r j : ℕ) {x : H} (hx : x ∈ operatorPowerDomain P (j + 1)) :
    let src := iteratedOperatorPower P (j + 1) x + (a : ℂ) • iteratedOperatorPower P j x
    ‖arbitraryOrderShiftedPotentialResolventYosidaTierApprox P R J a r j x -
        iteratedResolventPower R r (iteratedOperatorPower P j x)‖ ≤
      (a⁻¹) ^ (r + 1) * ‖J src - src‖ := by
  intro src
  unfold arbitraryOrderShiftedPotentialResolventYosidaTierApprox
  rw [← arbitraryOrderShifted_left_inverse_eq_on_succ P R a hl r j hx, ← map_sub]
  exact iteratedResolventPower_norm_bound P R a ha hr hp (r + 1) (J src - src)

/-- Scaled `j`-th tier shifted smoother defect bound against
`iteratedIdentityPower R a r (iteratedOperatorPower P j x)` and against
`arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x` on `operatorPowerDomain P (j + 1)`. -/
theorem arbitraryOrderScaledShifted_sub_identity_bounds_on_succ
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r j : ℕ) {x : H} (hx : x ∈ operatorPowerDomain P (j + 1)) :
    let src := iteratedOperatorPower P (j + 1) x + (a : ℂ) • iteratedOperatorPower P j x
    ‖((a ^ r : ℝ) : ℂ) • arbitraryOrderShiftedPotentialResolventYosidaTierApprox P R J a r j x -
        iteratedIdentityPower R a r (iteratedOperatorPower P j x)‖ ≤
      a⁻¹ * ‖J src - src‖ ∧
    ‖((a ^ r : ℝ) : ℂ) • arbitraryOrderShiftedPotentialResolventYosidaTierApprox P R J a r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x‖ ≤
      a⁻¹ * ‖J src - src‖ + ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ := by
  intro src
  have h1 :
      ‖((a ^ r : ℝ) : ℂ) • arbitraryOrderShiftedPotentialResolventYosidaTierApprox P R J a r j x -
          iteratedIdentityPower R a r (iteratedOperatorPower P j x)‖ ≤
        a⁻¹ * ‖J src - src‖ := by
    unfold iteratedIdentityPower
    rw [← smul_sub, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg ha.le r)]
    have hdef := arbitraryOrderShifted_defect_bound_on_succ P R J a ha hr hp hl r j hx
    calc
      a ^ r * ‖arbitraryOrderShiftedPotentialResolventYosidaTierApprox P R J a r j x -
          iteratedResolventPower R r (iteratedOperatorPower P j x)‖ ≤
        a ^ r * ((a⁻¹) ^ (r + 1) * ‖J src - src‖) :=
        mul_le_mul_of_nonneg_left hdef (pow_nonneg ha.le r)
      _ = (a * a⁻¹) ^ r * a⁻¹ * ‖J src - src‖ := by
        rw [pow_succ, ← mul_assoc, ← mul_assoc, ← mul_pow]
      _ = a⁻¹ * ‖J src - src‖ := by
        rw [mul_inv_cancel₀ ha.ne', one_pow, one_mul]
  refine ⟨h1, ?_⟩
  have hsplit :
      ((a ^ r : ℝ) : ℂ) • arbitraryOrderShiftedPotentialResolventYosidaTierApprox P R J a r j x -
          arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x =
        (((a ^ r : ℝ) : ℂ) • arbitraryOrderShiftedPotentialResolventYosidaTierApprox P R J a r j x -
          iteratedIdentityPower R a r (iteratedOperatorPower P j x)) -
        (arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x -
          iteratedIdentityPower R a r (iteratedOperatorPower P j x)) := by
    abel
  rw [hsplit]
  have htri := norm_sub_le
    (((a ^ r : ℝ) : ℂ) • arbitraryOrderShiftedPotentialResolventYosidaTierApprox P R J a r j x -
      iteratedIdentityPower R a r (iteratedOperatorPower P j x))
    (arbitraryOrderPotentialIdentityYosidaTierState P R J a r j x -
      iteratedIdentityPower R a r (iteratedOperatorPower P j x))
  have h2 := (arbitraryOrderPotentialYosidaDefect_bounds P R J a ha hr hp r 0 j x).1
  linarith

/-! ### 4. Strong Sequential Convergence Across All `m` Tiers -/

/-- Along any strongly convergent regularizer family `J n → id`, for every `r, j : ℕ` and `x : H`,
`arbitraryOrderPotentialResolventYosidaTierState P R (J n) r j x` converges to
`iteratedResolventPower R r (iteratedOperatorPower P j x)` and
`arbitraryOrderPotentialIdentityYosidaTierState P R (J n) a r j x` converges to
`iteratedIdentityPower R a r (iteratedOperatorPower P j x)`. -/
theorem tendsto_arbitraryOrderPotentialYosidaTierState_of_tendsto
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (J : ℕ → H →L[ℂ] H)
    (hJ : ∀ g : H, Tendsto (fun n => J n g) atTop (𝓝 g))
    (a : ℝ) (r j : ℕ) (x : H) :
    Tendsto (fun n => arbitraryOrderPotentialResolventYosidaTierState P R (J n) r j x)
      atTop (𝓝 (iteratedResolventPower R r (iteratedOperatorPower P j x))) ∧
    Tendsto (fun n => arbitraryOrderPotentialIdentityYosidaTierState P R (J n) a r j x)
      atTop (𝓝 (iteratedIdentityPower R a r (iteratedOperatorPower P j x))) := by
  have h1 : Tendsto (fun n => arbitraryOrderPotentialResolventYosidaTierState P R (J n) r j x)
      atTop (𝓝 (iteratedResolventPower R r (iteratedOperatorPower P j x))) :=
    ((iteratedResolventPower R r).continuous.tendsto (iteratedOperatorPower P j x)).comp
      (hJ (iteratedOperatorPower P j x))
  refine ⟨h1, ?_⟩
  unfold arbitraryOrderPotentialIdentityYosidaTierState iteratedIdentityPower
  exact (tendsto_const_nhds.smul h1)

/-- Along any strongly convergent regularizer family `J n → id`, for any
`x ∈ operatorPowerDomain P m` and any tier `j ≤ m`,
`arbitraryOrderPotentialIdentityYosidaTierState P R (J n) a r j x` converges in norm to the
commuting operator-power state `iteratedOperatorPower P j (iteratedIdentityPower R a r x)`. -/
theorem tendsto_arbitraryOrderPotentialIdentityYosidaTierState_commuting_on_powerDomain
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (J : ℕ → H →L[ℂ] H)
    (hJ : ∀ g : H, Tendsto (fun n => J n g) atTop (𝓝 g))
    (a : ℝ) (hr : Resolves P R a)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (m r j : ℕ) (hjm : j ≤ m) {x : H} (hx : x ∈ operatorPowerDomain P m) :
    Tendsto (fun n => arbitraryOrderPotentialIdentityYosidaTierState P R (J n) a r j x)
      atTop (𝓝 (iteratedOperatorPower P j (iteratedIdentityPower R a r x))) := by
  have hxj : x ∈ operatorPowerDomain P j := operatorPowerDomain_le_of_le P hjm hx
  rw [iteratedOperatorPower_iteratedIdentityPower_comm P R a hr hl j r hxj]
  exact (tendsto_arbitraryOrderPotentialYosidaTierState_of_tendsto P R J hJ a r j x).2

/-- Along any strongly convergent regularizer family `J n → id`, for any
`x ∈ operatorPowerDomain P (j + 1)`, the `j`-th tier shifted smoother
`arbitraryOrderShiftedPotentialResolventYosidaTierApprox P R (J n) a r j x` converges to
`iteratedResolventPower R r (iteratedOperatorPower P j x)`. -/
theorem tendsto_arbitraryOrderShifted_on_succ
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (J : ℕ → H →L[ℂ] H)
    (hJ : ∀ g : H, Tendsto (fun n => J n g) atTop (𝓝 g))
    (a : ℝ) (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r j : ℕ) {x : H} (hx : x ∈ operatorPowerDomain P (j + 1)) :
    Tendsto (fun n => arbitraryOrderShiftedPotentialResolventYosidaTierApprox P R (J n) a r j x)
      atTop (𝓝 (iteratedResolventPower R r (iteratedOperatorPower P j x))) := by
  rw [← arbitraryOrderShifted_left_inverse_eq_on_succ P R a hl r j hx]
  exact ((iteratedResolventPower R (r + 1)).continuous.tendsto _).comp
    (hJ (iteratedOperatorPower P (j + 1) x + (a : ℂ) • iteratedOperatorPower P j x))

/-- Along any strongly convergent regularizer family `J n → id`, for every `m, r : ℕ` and `x : H`,
both `arbitraryOrderPotentialYosidaRegularizerGraphNormSq P (J n) m x` and
`arbitraryOrderPotentialYosidaDefectGraphNormSq P R (J n) a r m x` converge to `0` as `n → ∞`,
and `arbitraryOrderPotentialYosidaGraphNormSq P R (J n) a r m x` converges to
`kthPowerGraphNormSq P m (iteratedIdentityPower R a r x)` whenever `x ∈ operatorPowerDomain P m`. -/
theorem tendsto_arbitraryOrderPotentialYosidaDefectGraphNormSq_zero
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (J : ℕ → H →L[ℂ] H)
    (hJ : ∀ g : H, Tendsto (fun n => J n g) atTop (𝓝 g))
    (a : ℝ) (r m : ℕ) (x : H) :
    Tendsto (fun n => arbitraryOrderPotentialYosidaRegularizerGraphNormSq P (J n) m x)
      atTop (𝓝 0) ∧
    Tendsto (fun n => arbitraryOrderPotentialYosidaDefectGraphNormSq P R (J n) a r m x)
      atTop (𝓝 0) := by
  constructor
  · unfold arbitraryOrderPotentialYosidaRegularizerGraphNormSq
    rw [show (0 : ℝ) = ∑ j ∈ Finset.range (m + 1), 0 by simp]
    apply tendsto_finset_sum
    intro j _
    simpa using ((tendsto_iff_norm_sub_tendsto_zero.mp
      (hJ (iteratedOperatorPower P j x))).pow 2)
  · unfold arbitraryOrderPotentialYosidaDefectGraphNormSq
    rw [show (0 : ℝ) = ∑ j ∈ Finset.range (m + 1), 0 by simp]
    apply tendsto_finset_sum
    intro j _
    have hj := (tendsto_arbitraryOrderPotentialYosidaTierState_of_tendsto P R J hJ a r j x).2
    simpa using ((tendsto_iff_norm_sub_tendsto_zero.mp hj).pow 2)

/-- Along any strongly convergent regularizer family `J n → id`, for any
`x ∈ operatorPowerDomain P m`, `arbitraryOrderPotentialYosidaGraphNormSq P R (J n) a r m x`
converges as `n → ∞` to `kthPowerGraphNormSq P m (iteratedIdentityPower R a r x)`. -/
theorem tendsto_arbitraryOrderPotentialYosidaGraphNormSq_on_powerDomain
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (J : ℕ → H →L[ℂ] H)
    (hJ : ∀ g : H, Tendsto (fun n => J n g) atTop (𝓝 g))
    (a : ℝ) (hr : Resolves P R a)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (m r : ℕ) {x : H} (hx : x ∈ operatorPowerDomain P m) :
    Tendsto (fun n => arbitraryOrderPotentialYosidaGraphNormSq P R (J n) a r m x)
      atTop (𝓝 (kthPowerGraphNormSq P m (iteratedIdentityPower R a r x))) := by
  unfold arbitraryOrderPotentialYosidaGraphNormSq kthPowerGraphNormSq
  apply tendsto_finset_sum
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hcomm :=
    tendsto_arbitraryOrderPotentialIdentityYosidaTierState_commuting_on_powerDomain
      P R J hJ a hr hl m r j hjm hx
  exact (hcomm.norm).pow 2

end AbstractArbitraryOrderPotentialYosida

/-! ### 5. Closed-Graph-Form and Clock-Floor Potential Hamiltonian Instantiations -/

section ClosedGraphFormArbitraryOrderInstantiation

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable [CompleteSpace H] [CompleteSpace K]

/-- Arbitrary-order `m`-tier radial-Yosida convergence and two-scale rate package for
any closed-graph-form self-adjoint positive Hamiltonian `hamiltonian D`. -/
theorem closedGraphForm_hamiltonian_arbitraryOrder_yosida_synthesis
    (D : Data H K) (R : H →L[ℂ] H) (J : ℕ → H →L[ℂ] H)
    (hJ_contr : ∀ n g, ‖J n g‖ ≤ ‖g‖)
    (hJ_tendsto : ∀ g : H, Tendsto (fun n => J n g) atTop (𝓝 g))
    (a : ℝ) (ha : 0 < a)
    (hr : Resolves (hamiltonian D) R a)
    (hl : ∀ z : (hamiltonian D).domain, R (hamiltonian D z + a • (z : H)) = (z : H))
    (m j r n : ℕ) (hjm : j ≤ m) {x : H}
    (hx : x ∈ operatorPowerDomain (hamiltonian D) (m + 1)) :
    IsSelfAdjoint (hamiltonian D) ∧
    arbitraryOrderPotentialYosidaGraphNormSq (hamiltonian D) R (J n) a r m x ≤
      kthPowerGraphNormSq (hamiltonian D) m x ∧
    ‖arbitraryOrderPotentialIdentityYosidaTierState (hamiltonian D) R (J n) a r j x -
        iteratedOperatorPower (hamiltonian D) j x‖ ≤
      ‖J n (iteratedOperatorPower (hamiltonian D) j x) -
          iteratedOperatorPower (hamiltonian D) j x‖ +
        (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower (hamiltonian D) (j + 1) x‖ ∧
    Tendsto
      (fun k =>
        arbitraryOrderPotentialIdentityYosidaTierState (hamiltonian D) R (J k) a r j x)
      atTop (𝓝 (iteratedOperatorPower (hamiltonian D) j (iteratedIdentityPower R a r x))) ∧
    Tendsto
      (fun k =>
        arbitraryOrderPotentialYosidaDefectGraphNormSq (hamiltonian D) R (J k) a r m x)
      atTop (𝓝 0) := by
  have hxm : x ∈ operatorPowerDomain (hamiltonian D) m :=
    operatorPowerDomain_le_of_le (hamiltonian D) (Nat.le_succ m) hx
  exact ⟨hamiltonian_selfAdjoint D,
    (arbitraryOrderPotentialYosidaGraphNormSq_contraction
      (hamiltonian D) R (J n) a ha hr (hamiltonian_positive D) (hJ_contr n) r m x).2,
    arbitraryOrderPotentialIdentityYosidaTierState_all_tiers_rate_bound_of_le
      (hamiltonian D) R (J n) a ha hr (hamiltonian_positive D) hl m j r hjm hx,
    tendsto_arbitraryOrderPotentialIdentityYosidaTierState_commuting_on_powerDomain
      (hamiltonian D) R J hJ_tendsto a hr hl m r j hjm hxm,
    (tendsto_arbitraryOrderPotentialYosidaDefectGraphNormSq_zero
      (hamiltonian D) R J hJ_tendsto a r m x).2⟩

end ClosedGraphFormArbitraryOrderInstantiation

section ClockFloorPotentialArbitraryOrderInstantiation

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m_mass g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m_mass g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m_mass g k
local notation "Jcut" => fun n : ℕ => action ε hε h (cutoff n) (cutoff_pos n)

/-- Concrete `j`-th tier `r`-fold potential-resolvent radial-Yosida state on `Hilbert`
for the clock-floor potential Hamiltonian `P` and radial-Yosida regularizer `action ε hε h (cutoff n)`. -/
def clockFloorPotentialResolventYosidaTierState
    (a : ℝ) (n r j : ℕ) (x : Hilbert) : Hilbert :=
  arbitraryOrderPotentialResolventYosidaTierState P (RP a) (Jcut n) r j x

/-- Concrete `j`-th tier `r`-th power Yosida-scaled identity radial-Yosida state on `Hilbert`
for the clock-floor potential Hamiltonian `P` and radial-Yosida regularizer `action ε hε h (cutoff n)`. -/
def clockFloorPotentialIdentityYosidaTierState
    (a : ℝ) (n r j : ℕ) (x : Hilbert) : Hilbert :=
  arbitraryOrderPotentialIdentityYosidaTierState P (RP a) (Jcut n) a r j x

/-- Unconditional `potentialPowerDomain` regularity and contractive `kthPowerGraphNormSq`
stability for `clockFloorPotentialResolventYosidaTierState` and
`clockFloorPotentialIdentityYosidaTierState`. -/
theorem clockFloorPotentialYosidaTierState_regularity_and_contraction
    (a : ℝ) (ha : 0 < a) (n r m j : ℕ) (x : Hilbert) :
    clockFloorPotentialResolventYosidaTierState ε hε h hh hb m_mass g k a n r j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k r ∧
    clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k a n r j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k r ∧
    ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k a n r j x‖ ≤
      ‖iteratedOperatorPower P j x‖ ∧
    arbitraryOrderPotentialYosidaGraphNormSq P (RP a) (Jcut n) a r m x ≤
      kthPowerGraphNormSq P m x := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k a ha
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have hcontr : ∀ v : Hilbert, ‖Jcut n v‖ ≤ ‖v‖ :=
    fun v => action_norm ε hε h (cutoff n) (cutoff_pos n) v
  have hmem :=
    arbitraryOrderPotentialYosidaTierState_mem_operatorPowerDomain P (RP a) (Jcut n) a hres r j x
  exact ⟨hmem.1, hmem.2.1,
    arbitraryOrderPotentialIdentityYosidaTierState_norm_le_of_contractive
      P (RP a) (Jcut n) a ha hres hpos hcontr r j x,
    (arbitraryOrderPotentialYosidaGraphNormSq_contraction
      P (RP a) (Jcut n) a ha hres hpos hcontr r m x).2⟩

/-- Simultaneous `(m + 1)`-tier two-scale approximation rate bound for
`clockFloorPotentialIdentityYosidaTierState` on `potentialPowerDomain (m + 1)`. -/
theorem clockFloorPotentialIdentityYosidaTierState_all_tiers_rate_bound
    (a : ℝ) (ha : 0 < a) (n m j r : ℕ) (hjm : j ≤ m) {x : Hilbert}
    (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k a n r j x -
        iteratedOperatorPower P j x‖ ≤
      ‖Jcut n (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower P (j + 1) x‖ :=
  arbitraryOrderPotentialIdentityYosidaTierState_all_tiers_rate_bound_of_le
    P (RP a) (Jcut n) a ha
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k a ha)
    (KFCausalClosedGraphForm.hamiltonian_positive PD)
    (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k a ha)
    m j r hjm hx

/-- Strong sequential convergence as `n → ∞` along `cutoff n` of
`clockFloorPotentialResolventYosidaTierState`, `clockFloorPotentialIdentityYosidaTierState`,
and the `m`-tier radial-Yosida defect and graph norms on `potentialPowerDomain m`. -/
theorem clockFloorPotentialYosidaTierState_arbitraryOrder_convergence_master
    (a : ℝ) (ha : 0 < a) (m j r : ℕ) (hjm : j ≤ m) {x : Hilbert}
    (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k m) :
    Tendsto
      (fun n => clockFloorPotentialResolventYosidaTierState ε hε h hh hb m_mass g k a n r j x)
      atTop (𝓝 (iteratedResolventPower (RP a) r (iteratedOperatorPower P j x))) ∧
    Tendsto
      (fun n => clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k a n r j x)
      atTop (𝓝 (iteratedOperatorPower P j (iteratedIdentityPower (RP a) a r x))) ∧
    Tendsto
      (fun n => arbitraryOrderPotentialYosidaDefectGraphNormSq P (RP a) (Jcut n) a r m x)
      atTop (𝓝 0) ∧
    Tendsto
      (fun n => arbitraryOrderPotentialYosidaGraphNormSq P (RP a) (Jcut n) a r m x)
      atTop (𝓝 (kthPowerGraphNormSq P m (iteratedIdentityPower (RP a) a r x))) := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k a ha
  have hlinv :=
    KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k a ha
  have hJ : ∀ v : Hilbert, Tendsto (fun n => Jcut n v) atTop (𝓝 v) :=
    fun v => sequence_tendsto ε hε h v
  exact ⟨(tendsto_arbitraryOrderPotentialYosidaTierState_of_tendsto P (RP a) Jcut hJ a r j x).1,
    tendsto_arbitraryOrderPotentialIdentityYosidaTierState_commuting_on_powerDomain
      P (RP a) Jcut hJ a hres hlinv m r j hjm hx,
    (tendsto_arbitraryOrderPotentialYosidaDefectGraphNormSq_zero P (RP a) Jcut hJ a r m x).2,
    tendsto_arbitraryOrderPotentialYosidaGraphNormSq_on_powerDomain
      P (RP a) Jcut hJ a hres hlinv m r hx⟩

/-- Double-limit synthesis on `potentialPowerDomain (m + 1)`: combines the radial-Yosida
cutoff limit `n → ∞` (`action ε hε h (cutoff n) → id`) with the Yosida resolvent-parameter
limit `a = (q : ℝ) + 1 → ∞` across all tiers `j ≤ m`. -/
theorem clockFloorPotentialYosidaTierState_two_scale_double_limit_synthesis
    (a : ℝ) (ha : 0 < a) (n m j r : ℕ) (hjm : j ≤ m) {x : Hilbert}
    (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    (arbitraryOrderPotentialYosidaGraphNormSq P (RP a) (Jcut n) a r m x ≤
       kthPowerGraphNormSq P m x ∧
     kthPowerGraphNormSq P m (iteratedIdentityPower (RP a) a r x) ≤
       kthPowerGraphNormSq P m x) ∧
    ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k a n r j x -
        iteratedOperatorPower P j x‖ ≤
      ‖Jcut n (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower P (j + 1) x‖ ∧
    Tendsto
      (fun q => clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k a q r j x)
      atTop (𝓝 (iteratedOperatorPower P j (iteratedIdentityPower (RP a) a r x))) ∧
    Tendsto
      (fun q : ℕ =>
        iteratedOperatorPower P j
          (iteratedIdentityPower (RP ((q : ℝ) + 1)) ((q : ℝ) + 1) r x))
      atTop (𝓝 (iteratedOperatorPower P j x)) := by
  have hxm : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k m :=
    operatorPowerDomain_le_of_le P (Nat.le_succ m) hx
  have hxj1 : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (j + 1) :=
    operatorPowerDomain_le_of_le P (Nat.succ_le_succ hjm) hx
  have h1 :=
    (clockFloorPotentialYosidaTierState_regularity_and_contraction
      ε hε h hh hb m_mass g k a ha n r m j x).2.2.2
  have h2 :=
    (potential_arbitraryOrder_comm_and_graphNorm_contraction
      ε hε h hh hb m_mass g k a ha m r hxm).2.2.2
  have h3 :=
    clockFloorPotentialIdentityYosidaTierState_all_tiers_rate_bound
      ε hε h hh hb m_mass g k a ha n m j r hjm hx
  have h4 :=
    (clockFloorPotentialYosidaTierState_arbitraryOrder_convergence_master
      ε hε h hh hb m_mass g k a ha m j r hjm hxm).2.1
  have h5 :=
    (potential_arbitraryOrder_rate_and_tendsto_on_succ
      ε hε h hh hb m_mass g k a ha j r hxj1).2
  exact ⟨⟨h1, h2⟩, h3, h4, h5⟩

end ClockFloorPotentialArbitraryOrderInstantiation

#print axioms arbitraryOrderPotentialYosidaTierState_zero_tier
#print axioms arbitraryOrderPotentialYosidaTierState_zero_power
#print axioms arbitraryOrderPotentialYosidaTierState_succ_power
#print axioms arbitraryOrderPotentialYosidaTierState_succ_tier
#print axioms arbitraryOrderPotentialIdentityYosidaTierState_eq_smul
#print axioms arbitraryOrderPotentialYosidaTierState_mem_operatorPowerDomain
#print axioms arbitraryOrderPotentialIdentityYosidaTierState_first_order_action_eq
#print axioms arbitraryOrderPotentialIdentityYosidaTierState_id_eq_iteratedOperatorPower
#print axioms arbitraryOrderPotentialYosidaTierState_norm_bounds
#print axioms arbitraryOrderPotentialIdentityYosidaTierState_norm_le_of_contractive
#print axioms arbitraryOrderPotentialYosidaGraphNormSq_nonneg_and_zero
#print axioms arbitraryOrderPotentialYosidaGraphNormSq_succ
#print axioms arbitraryOrderPotentialYosidaGraphNormSq_contraction
#print axioms arbitraryOrderPotentialYosidaDefect_bounds
#print axioms arbitraryOrderPotentialIdentityYosidaTierState_two_scale_sub_eq
#print axioms arbitraryOrderPotentialIdentityYosidaTierState_rate_bound_on_succ
#print axioms arbitraryOrderPotentialIdentityYosidaTierState_all_tiers_rate_bound_of_le
#print axioms arbitraryOrderShifted_left_inverse_eq_on_succ
#print axioms arbitraryOrderShifted_defect_bound_on_succ
#print axioms arbitraryOrderScaledShifted_sub_identity_bounds_on_succ
#print axioms tendsto_arbitraryOrderPotentialYosidaTierState_of_tendsto
#print axioms tendsto_arbitraryOrderPotentialIdentityYosidaTierState_commuting_on_powerDomain
#print axioms tendsto_arbitraryOrderShifted_on_succ
#print axioms tendsto_arbitraryOrderPotentialYosidaDefectGraphNormSq_zero
#print axioms tendsto_arbitraryOrderPotentialYosidaGraphNormSq_on_powerDomain
#print axioms closedGraphForm_hamiltonian_arbitraryOrder_yosida_synthesis
#print axioms clockFloorPotentialYosidaTierState_regularity_and_contraction
#print axioms clockFloorPotentialIdentityYosidaTierState_all_tiers_rate_bound
#print axioms clockFloorPotentialYosidaTierState_arbitraryOrder_convergence_master
#print axioms clockFloorPotentialYosidaTierState_two_scale_double_limit_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaArbitraryOrderConvergence
