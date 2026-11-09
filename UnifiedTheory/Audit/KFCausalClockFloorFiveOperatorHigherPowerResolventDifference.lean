/- Higher-Power Iterated Resolvent Difference Calculus, `(r + 2)`-th Power Domain
Regularity, Two-Parameter Yosida Identity Commutativity, and Domain Rate Bounds
Across All Five Clock-Floor Hamiltonians T, P, G, S(t), and H(t):
1. Proves for any positive operator A with positive shifted resolvents R(a):
   - Exact step telescoping identity for `(r + 1)`-fold iterated resolvent differences:
     `R(a)^{r+1} f - R(b)^{r+1} f = ((b - a : ℝ) : ℂ) • R(a)(R(b)(R(a)^r f)) + R(b)(R(a)^r f - R(b)^r f)`,
   - Inductive higher-power domain regularity lift: for EVERY `r : ℕ` and `f : H`,
     `iteratedResolventPower (R a) (r + 1) f - iteratedResolventPower (R b) (r + 1) f ∈ operatorPowerDomain A (r + 2)`,
     gaining a full extra power of operator regularity over the individual summands,
   - Two-parameter commutativity of Yosida-scaled identity towers `iteratedIdentityPower (R a) a r`
     and `iteratedIdentityPower (R b) b s` for all `r, s : ℕ`,
   - Mutual Cauchy rate bound on `A.domain`:
     `‖iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x‖ ≤ (r : ℝ) * (a⁻¹ + b⁻¹) * ‖A x‖`,
   - First-order Yosida identity difference formula on `A.domain`:
     `(a : ℂ) • R a x - (b : ℂ) • R b x = ((a - b : ℝ) : ℂ) • R a (R b (A x)) ∈ operatorPowerDomain A 2`.
2. Instantiates all higher-power resolvent difference identities, `operatorPowerDomain A (r + 2)`
   memberships, two-parameter Yosida identity commutativity, and domain Cauchy bounds across all
   five clock-floor Hamiltonians `T`, `P`, `G`, `S(t)`, and `H(t)`, including simultaneous
   10-domain regularity for `R_{H(t)}(a)^{r+1} f - R_{H(t)}(b)^{r+1} f`. -/
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorIteratedResolventCommutativity
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerYosidaGraphConvergence

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorHigherPowerResolventDifference

noncomputable section

open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalPositiveResolventBounds
  (Resolves point resolvent_apply_norm_bound)
open KFCausalClockFloorSecondPowerOperatorCores
  (secondPowerDomain hamiltonian_domain_mem_ten_domains)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (iterated_resolvent_norm_bound)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain operatorPowerDomain_succ_le_domain
   operatorPowerDomain_add_two_le_secondPowerDomain
   resolvent_mem_operatorPowerDomain_succ
   iteratedResolventPower iteratedResolventPower_zero_apply iteratedResolventPower_succ_apply
   iteratedResolventPower_mem_operatorPowerDomain iteratedResolventPower_norm_bound
   staticPowerDomain potentialPowerDomain growingPowerDomain
   residualPowerDomain hamiltonianPowerDomain
   hamiltonianPowerDomain_succ_mem_ten_domains)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedIdentityPower iteratedIdentityPower_mem_operatorPowerDomain
   iteratedIdentityPower_norm_le single_yosida_defect_on_domain
   iteratedIdentityPower_domain_rate_bound)
open KFCausalClockFloorGrowingPotentialSecondResolventIdentity
  (potential_resolvent_left_inverse)
open KFCausalClockFloorHamiltonianResidualSecondResolventIdentity
  (residual_resolvent_left_inverse)
open KFCausalClockFloorStaticResidualSecondResolventIdentity
  (static_resolvent_left_inverse)
open KFCausalClockFloorFiveOperatorFirstResolventIdentity
  (first_resolvent_identity resolvent_apply_comm)
open KFCausalClockFloorFiveOperatorIteratedResolventCommutativity
  (iteratedResolventPower_comm)

/-! ### 1. Abstract Higher-Power Resolvent Difference Calculus and Yosida Cauchy Bounds -/

section AbstractHigherPowerDifference

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Algebraic step decomposition for the difference of `(r + 1)`-fold iterated resolvents. -/
theorem iteratedResolventPower_sub_succ_split
    (Ra Rb : H →L[ℂ] H) (r : ℕ) (f : H) :
    iteratedResolventPower Ra (r + 1) f - iteratedResolventPower Rb (r + 1) f =
      (Ra (iteratedResolventPower Ra r f) - Rb (iteratedResolventPower Ra r f)) +
        Rb (iteratedResolventPower Ra r f - iteratedResolventPower Rb r f) := by
  rw [iteratedResolventPower_succ_apply, iteratedResolventPower_succ_apply, map_sub]
  abel

/-- Exact step recurrence for the difference of `(r + 1)`-fold iterated resolvents using
the first resolvent identity on the leading term. -/
theorem iteratedResolventPower_sub_succ_eq
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (r : ℕ) (f : H) :
    iteratedResolventPower (R a) (r + 1) f - iteratedResolventPower (R b) (r + 1) f =
      ((b - a : ℝ) : ℂ) • R a (R b (iteratedResolventPower (R a) r f)) +
        R b (iteratedResolventPower (R a) r f - iteratedResolventPower (R b) r f) := by
  rw [iteratedResolventPower_sub_succ_split (R a) (R b) r f,
    first_resolvent_identity A (R a) (R b) a b (hr b hb) (hl a ha)
      (iteratedResolventPower (R a) r f)]

/-- Base case `r = 1` of the iterated resolvent difference identity. -/
theorem iteratedResolventPower_sub_one_eq
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (f : H) :
    iteratedResolventPower (R a) 1 f - iteratedResolventPower (R b) 1 f =
      ((b - a : ℝ) : ℂ) • R a (R b f) := by
  simpa [iteratedResolventPower_zero_apply] using
    iteratedResolventPower_sub_succ_eq A R a b ha hb hr hl 0 f

/-- Inductive higher-power domain regularity lift: for EVERY `r : ℕ` and `f : H`,
while `iteratedResolventPower (R a) (r + 1) f` and `iteratedResolventPower (R b) (r + 1) f`
individually lie in `operatorPowerDomain A (r + 1)`, their difference lies in
`operatorPowerDomain A (r + 2)`. -/
theorem iteratedResolventPower_sub_succ_mem_operatorPowerDomain
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H)) :
    ∀ r : ℕ, ∀ f : H,
      iteratedResolventPower (R a) (r + 1) f - iteratedResolventPower (R b) (r + 1) f ∈
        operatorPowerDomain A (r + 2)
  | 0, f => by
    rw [iteratedResolventPower_sub_one_eq A R a b ha hb hr hl f]
    exact (operatorPowerDomain A 2).smul_mem ((b - a : ℝ) : ℂ)
      (resolvent_mem_operatorPowerDomain_succ A (R a) a (hr a ha) 1
        (resolvent_mem_operatorPowerDomain_succ A (R b) b (hr b hb) 0 Submodule.mem_top))
  | r + 1, f => by
    rw [iteratedResolventPower_sub_succ_eq A R a b ha hb hr hl (r + 1) f]
    have hlead :
        ((b - a : ℝ) : ℂ) • R a (R b (iteratedResolventPower (R a) (r + 1) f)) ∈
          operatorPowerDomain A (r + 3) :=
      (operatorPowerDomain A (r + 3)).smul_mem ((b - a : ℝ) : ℂ)
        (resolvent_mem_operatorPowerDomain_succ A (R a) a (hr a ha) (r + 2)
          (resolvent_mem_operatorPowerDomain_succ A (R b) b (hr b hb) (r + 1)
            (iteratedResolventPower_mem_operatorPowerDomain A (R a) a (hr a ha) (r + 1) f)))
    have hstep :
        R b (iteratedResolventPower (R a) (r + 1) f - iteratedResolventPower (R b) (r + 1) f) ∈
          operatorPowerDomain A (r + 3) :=
      resolvent_mem_operatorPowerDomain_succ A (R b) b (hr b hb) (r + 2)
        (iteratedResolventPower_sub_succ_mem_operatorPowerDomain A R a b ha hb hr hl r f)
    exact (operatorPowerDomain A (r + 3)).add_mem hlead hstep

/-- Every positive-power resolvent difference lies in `A.domain`. -/
theorem iteratedResolventPower_sub_succ_mem_domain
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (r : ℕ) (f : H) :
    iteratedResolventPower (R a) (r + 1) f - iteratedResolventPower (R b) (r + 1) f ∈
      A.domain :=
  operatorPowerDomain_succ_le_domain A (r + 1)
    (iteratedResolventPower_sub_succ_mem_operatorPowerDomain A R a b ha hb hr hl r f)

/-- Every positive-power resolvent difference lies in `secondPowerDomain A`. -/
theorem iteratedResolventPower_sub_succ_mem_secondPowerDomain
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (r : ℕ) (f : H) :
    iteratedResolventPower (R a) (r + 1) f - iteratedResolventPower (R b) (r + 1) f ∈
      secondPowerDomain A :=
  operatorPowerDomain_add_two_le_secondPowerDomain A r
    (iteratedResolventPower_sub_succ_mem_operatorPowerDomain A R a b ha hb hr hl r f)

/-- Unconditional geometric norm bound on the difference of `r`-fold iterated resolvents:
`‖iteratedResolventPower (R a) r f - iteratedResolventPower (R b) r f‖ ≤ ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖`. -/
theorem iteratedResolventPower_sub_norm_bound
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (r : ℕ) (f : H) :
    ‖iteratedResolventPower (R a) r f - iteratedResolventPower (R b) r f‖ ≤
      ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖f‖ := by
  have htri := norm_sub_le (iteratedResolventPower (R a) r f) (iteratedResolventPower (R b) r f)
  have ha_bd := iteratedResolventPower_norm_bound A (R a) a ha (hr a ha) hp r f
  have hb_bd := iteratedResolventPower_norm_bound A (R b) b hb (hr b hb) hp r f
  linarith [add_mul ((a⁻¹) ^ r) ((b⁻¹) ^ r) ‖f‖]

/-- Two-parameter `(a, b)` and two-order `(r, s)` commutativity for Yosida-scaled
identity approximants `iteratedIdentityPower`. -/
theorem iteratedIdentityPower_two_param_comm
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (r s : ℕ) (f : H) :
    iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s f) =
      iteratedIdentityPower (R b) b s (iteratedIdentityPower (R a) a r f) := by
  unfold iteratedIdentityPower
  rw [map_smul, map_smul, smul_smul, smul_smul, mul_comm,
    iteratedResolventPower_comm A R a b ha hb hr hl r s f]

/-- The difference of `r`-th order Yosida identity approximants at scales `a` and `b`
lies in `operatorPowerDomain A r`. -/
theorem iteratedIdentityPower_sub_mem_operatorPowerDomain
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d) (r : ℕ) (f : H) :
    iteratedIdentityPower (R a) a r f - iteratedIdentityPower (R b) b r f ∈
      operatorPowerDomain A r :=
  (operatorPowerDomain A r).sub_mem
    (iteratedIdentityPower_mem_operatorPowerDomain A (R a) a (hr a ha) r f)
    (iteratedIdentityPower_mem_operatorPowerDomain A (R b) b (hr b hb) r f)

/-- Uniform stability bound `‖iteratedIdentityPower (R a) a r f - iteratedIdentityPower (R b) b r f‖ ≤ 2 * ‖f‖`. -/
theorem iteratedIdentityPower_sub_norm_le_two
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (r : ℕ) (f : H) :
    ‖iteratedIdentityPower (R a) a r f - iteratedIdentityPower (R b) b r f‖ ≤ 2 * ‖f‖ := by
  have htri := norm_sub_le (iteratedIdentityPower (R a) a r f) (iteratedIdentityPower (R b) b r f)
  have ha_bd := iteratedIdentityPower_norm_le A (R a) a ha (hr a ha) hp r f
  have hb_bd := iteratedIdentityPower_norm_le A (R b) b hb (hr b hb) hp r f
  linarith

/-- Decomposition of the mutual Yosida identity difference on `A.domain` through `(x : H)`. -/
theorem iteratedIdentityPower_sub_eq_defect_sub_on_domain
    {A : H →ₗ.[ℂ] H} (R : ℝ → H →L[ℂ] H) (a b : ℝ) (r : ℕ) (x : A.domain) :
    iteratedIdentityPower (R a) a r (x : H) - iteratedIdentityPower (R b) b r (x : H) =
      (iteratedIdentityPower (R a) a r (x : H) - (x : H)) -
        (iteratedIdentityPower (R b) b r (x : H) - (x : H)) := by
  abel

/-- Mutual Cauchy rate bound on `A.domain` for `r`-th order Yosida identity approximants:
`‖iteratedIdentityPower (R a) a r (x : H) - iteratedIdentityPower (R b) b r (x : H)‖ ≤ (r : ℝ) * (a⁻¹ + b⁻¹) * ‖A x‖`. -/
theorem iteratedIdentityPower_sub_domain_rate_bound
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) :
    ‖iteratedIdentityPower (R a) a r (x : H) - iteratedIdentityPower (R b) b r (x : H)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖A x‖ := by
  rw [iteratedIdentityPower_sub_eq_defect_sub_on_domain R a b r x]
  have htri :=
    norm_sub_le
      (iteratedIdentityPower (R a) a r (x : H) - (x : H))
      (iteratedIdentityPower (R b) b r (x : H) - (x : H))
  have ha_bd := iteratedIdentityPower_domain_rate_bound A (R a) a ha (hr a ha) hp (hl a ha) r x
  have hb_bd := iteratedIdentityPower_domain_rate_bound A (R b) b hb (hr b hb) hp (hl b hb) r x
  have hring :
      (r : ℝ) * a⁻¹ * ‖A x‖ + (r : ℝ) * b⁻¹ * ‖A x‖ =
        (r : ℝ) * (a⁻¹ + b⁻¹) * ‖A x‖ := by
    ring
  linarith

/-- Exact first-order Yosida identity difference on `A.domain`:
`(a : ℂ) • R a x - (b : ℂ) • R b x = R b (A x) - R a (A x) = ((a - b : ℝ) : ℂ) • R a (R b (A x))`. -/
theorem single_yosida_sub_eq_on_domain
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (x : A.domain) :
    (a : ℂ) • R a (x : H) - (b : ℂ) • R b (x : H) = R b (A x) - R a (A x) ∧
    (a : ℂ) • R a (x : H) - (b : ℂ) • R b (x : H) =
      ((a - b : ℝ) : ℂ) • R a (R b (A x)) := by
  have hda := (single_yosida_defect_on_domain A (R a) a ha (hr a ha) hp (hl a ha) x).1
  have hdb := (single_yosida_defect_on_domain A (R b) b hb (hr b hb) hp (hl b hb) x).1
  have h1 : (a : ℂ) • R a (x : H) - (b : ℂ) • R b (x : H) = R b (A x) - R a (A x) := by
    calc (a : ℂ) • R a (x : H) - (b : ℂ) • R b (x : H)
        = ((a : ℂ) • R a (x : H) - (x : H)) - ((b : ℂ) • R b (x : H) - (x : H)) := by abel
      _ = -R a (A x) - (-R b (A x)) := by rw [hda, hdb]
      _ = R b (A x) - R a (A x) := by abel
  refine ⟨h1, ?_⟩
  rw [h1, first_resolvent_identity A (R b) (R a) b a (hr a ha) (hl b hb) (A x),
    resolvent_apply_comm A R b a hb ha hr hl (A x)]

/-- Second-power domain membership and quadratic-decay norm bound for the first-order
Yosida identity difference on `A.domain`:
`(a : ℂ) • R a x - (b : ℂ) • R b x ∈ operatorPowerDomain A 2` and
`‖(a : ℂ) • R a x - (b : ℂ) • R b x‖ ≤ |a - b| * (a⁻¹ * (b⁻¹ * ‖A x‖))`. -/
theorem single_yosida_sub_mem_secondPowerDomain_and_norm_on_domain
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (x : A.domain) :
    (a : ℂ) • R a (x : H) - (b : ℂ) • R b (x : H) ∈ operatorPowerDomain A 2 ∧
    ‖(a : ℂ) • R a (x : H) - (b : ℂ) • R b (x : H)‖ ≤
      |a - b| * (a⁻¹ * (b⁻¹ * ‖A x‖)) := by
  have heq := (single_yosida_sub_eq_on_domain A R a b ha hb hr hp hl x).2
  rw [heq]
  refine ⟨(operatorPowerDomain A 2).smul_mem ((a - b : ℝ) : ℂ)
    (resolvent_mem_operatorPowerDomain_succ A (R a) a (hr a ha) 1
      (resolvent_mem_operatorPowerDomain_succ A (R b) b (hr b hb) 0 Submodule.mem_top)), ?_⟩
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (iterated_resolvent_norm_bound A (R a) (R b) a b ha hb (hr a ha) (hr b hb) hp (A x))
    (abs_nonneg (a - b))

end AbstractHigherPowerDifference

/-! ### 2. Concrete Five-Operator Instantiations for `T`, `P`, `G`, `S(t)`, and `H(t)` -/

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k t : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => KFCausalClockFloorStaticClockCore.resolvent ε hε h hh hw m g k 0
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

/-- Step recurrence for `(r + 1)`-fold static resolvent differences. -/
theorem staticResolvent_iteratedResolventPower_sub_succ_eq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RT a) (r + 1) f - iteratedResolventPower (RT b) (r + 1) f =
      ((b - a : ℝ) : ℂ) • RT a (RT b (iteratedResolventPower (RT a) r f)) +
        RT b (iteratedResolventPower (RT a) r f - iteratedResolventPower (RT b) r f) :=
  iteratedResolventPower_sub_succ_eq T RT a b ha hb_pos
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves ε hε h hh hb m g k)
    (static_resolvent_left_inverse ε hε h hh hb m g k) r f

/-- Membership of `iteratedResolventPower (RT a) (r + 1) f - iteratedResolventPower (RT b) (r + 1) f`
in `staticPowerDomain ε hε h (r + 2)`. -/
theorem staticResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RT a) (r + 1) f - iteratedResolventPower (RT b) (r + 1) f ∈
      staticPowerDomain ε hε h (r + 2) :=
  iteratedResolventPower_sub_succ_mem_operatorPowerDomain T RT a b ha hb_pos
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves ε hε h hh hb m g k)
    (static_resolvent_left_inverse ε hε h hh hb m g k) r f

/-- Two-parameter commutativity of static Yosida identity approximants. -/
theorem staticResolvent_iteratedIdentityPower_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r s : ℕ) (f : Hilbert) :
    iteratedIdentityPower (RT a) a r (iteratedIdentityPower (RT b) b s f) =
      iteratedIdentityPower (RT b) b s (iteratedIdentityPower (RT a) a r f) :=
  iteratedIdentityPower_two_param_comm T RT a b ha hb_pos
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves ε hε h hh hb m g k)
    (static_resolvent_left_inverse ε hε h hh hb m g k) r s f

/-- Mutual Cauchy rate bound on `(T).domain` for static Yosida identity approximants. -/
theorem staticResolvent_iteratedIdentityPower_sub_domain_rate_bound
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (x : (T).domain) :
    ‖iteratedIdentityPower (RT a) a r (x : Hilbert) -
      iteratedIdentityPower (RT b) b r (x : Hilbert)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖T x‖ :=
  iteratedIdentityPower_sub_domain_rate_bound T RT a b ha hb_pos
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves ε hε h hh hb m g k)
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_operator_positive ε hε h)
    (static_resolvent_left_inverse ε hε h hh hb m g k) r x

/-- Step recurrence for `(r + 1)`-fold potential resolvent differences. -/
theorem potentialResolvent_iteratedResolventPower_sub_succ_eq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RP a) (r + 1) f - iteratedResolventPower (RP b) (r + 1) f =
      ((b - a : ℝ) : ℂ) • RP a (RP b (iteratedResolventPower (RP a) r f)) +
        RP b (iteratedResolventPower (RP a) r f - iteratedResolventPower (RP b) r f) :=
  iteratedResolventPower_sub_succ_eq P RP a b ha hb_pos
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (potential_resolvent_left_inverse ε hε h hh hb m g k) r f

/-- Membership of `iteratedResolventPower (RP a) (r + 1) f - iteratedResolventPower (RP b) (r + 1) f`
in `potentialPowerDomain ε hε h hh hb m g k (r + 2)`. -/
theorem potentialResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RP a) (r + 1) f - iteratedResolventPower (RP b) (r + 1) f ∈
      potentialPowerDomain ε hε h hh hb m g k (r + 2) :=
  iteratedResolventPower_sub_succ_mem_operatorPowerDomain P RP a b ha hb_pos
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (potential_resolvent_left_inverse ε hε h hh hb m g k) r f

/-- Two-parameter commutativity of potential Yosida identity approximants. -/
theorem potentialResolvent_iteratedIdentityPower_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r s : ℕ) (f : Hilbert) :
    iteratedIdentityPower (RP a) a r (iteratedIdentityPower (RP b) b s f) =
      iteratedIdentityPower (RP b) b s (iteratedIdentityPower (RP a) a r f) :=
  iteratedIdentityPower_two_param_comm P RP a b ha hb_pos
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (potential_resolvent_left_inverse ε hε h hh hb m g k) r s f

/-- Mutual Cauchy rate bound on `(P).domain` for potential Yosida identity approximants. -/
theorem potentialResolvent_iteratedIdentityPower_sub_domain_rate_bound
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (x : (P).domain) :
    ‖iteratedIdentityPower (RP a) a r (x : Hilbert) -
      iteratedIdentityPower (RP b) b r (x : Hilbert)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖P x‖ :=
  iteratedIdentityPower_sub_domain_rate_bound P RP a b ha hb_pos
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (KFCausalClosedGraphForm.hamiltonian_positive PD)
    (potential_resolvent_left_inverse ε hε h hh hb m g k) r x

/-- Step recurrence for `(r + 1)`-fold growing resolvent differences. -/
theorem growingResolvent_iteratedResolventPower_sub_succ_eq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RG a) (r + 1) f - iteratedResolventPower (RG b) (r + 1) f =
      ((b - a : ℝ) : ℂ) • RG a (RG b (iteratedResolventPower (RG a) r f)) +
        RG b (iteratedResolventPower (RG a) r f - iteratedResolventPower (RG b) r f) :=
  iteratedResolventPower_sub_succ_eq G RG a b ha hb_pos
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) r f

/-- Membership of `iteratedResolventPower (RG a) (r + 1) f - iteratedResolventPower (RG b) (r + 1) f`
in `growingPowerDomain ε hε h hh hb m g k (r + 2)`. -/
theorem growingResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RG a) (r + 1) f - iteratedResolventPower (RG b) (r + 1) f ∈
      growingPowerDomain ε hε h hh hb m g k (r + 2) :=
  iteratedResolventPower_sub_succ_mem_operatorPowerDomain G RG a b ha hb_pos
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) r f

/-- Two-parameter commutativity of growing Yosida identity approximants. -/
theorem growingResolvent_iteratedIdentityPower_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r s : ℕ) (f : Hilbert) :
    iteratedIdentityPower (RG a) a r (iteratedIdentityPower (RG b) b s f) =
      iteratedIdentityPower (RG b) b s (iteratedIdentityPower (RG a) a r f) :=
  iteratedIdentityPower_two_param_comm G RG a b ha hb_pos
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) r s f

/-- Mutual Cauchy rate bound on `(G).domain` for growing Yosida identity approximants. -/
theorem growingResolvent_iteratedIdentityPower_sub_domain_rate_bound
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (x : (G).domain) :
    ‖iteratedIdentityPower (RG a) a r (x : Hilbert) -
      iteratedIdentityPower (RG b) b r (x : Hilbert)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖G x‖ :=
  iteratedIdentityPower_sub_domain_rate_bound G RG a b ha hb_pos
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) r x

/-- Step recurrence for `(r + 1)`-fold residual resolvent differences. -/
theorem residualResolvent_iteratedResolventPower_sub_succ_eq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RS t a) (r + 1) f - iteratedResolventPower (RS t b) (r + 1) f =
      ((b - a : ℝ) : ℂ) • RS t a (RS t b (iteratedResolventPower (RS t a) r f)) +
        RS t b (iteratedResolventPower (RS t a) r f - iteratedResolventPower (RS t b) r f) :=
  iteratedResolventPower_sub_succ_eq (S t) (RS t) a b ha hb_pos
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (residual_resolvent_left_inverse ε hε h hh hb m g k t) r f

/-- Membership of `iteratedResolventPower (RS t a) (r + 1) f - iteratedResolventPower (RS t b) (r + 1) f`
in `residualPowerDomain ε hε h hh hb m g k t (r + 2)`. -/
theorem residualResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RS t a) (r + 1) f - iteratedResolventPower (RS t b) (r + 1) f ∈
      residualPowerDomain ε hε h hh hb m g k t (r + 2) :=
  iteratedResolventPower_sub_succ_mem_operatorPowerDomain (S t) (RS t) a b ha hb_pos
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (residual_resolvent_left_inverse ε hε h hh hb m g k t) r f

/-- Two-parameter commutativity of residual Yosida identity approximants. -/
theorem residualResolvent_iteratedIdentityPower_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r s : ℕ) (f : Hilbert) :
    iteratedIdentityPower (RS t a) a r (iteratedIdentityPower (RS t b) b s f) =
      iteratedIdentityPower (RS t b) b s (iteratedIdentityPower (RS t a) a r f) :=
  iteratedIdentityPower_two_param_comm (S t) (RS t) a b ha hb_pos
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (residual_resolvent_left_inverse ε hε h hh hb m g k t) r s f

/-- Mutual Cauchy rate bound on `(S t).domain` for residual Yosida identity approximants. -/
theorem residualResolvent_iteratedIdentityPower_sub_domain_rate_bound
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (x : (S t).domain) :
    ‖iteratedIdentityPower (RS t a) a r (x : Hilbert) -
      iteratedIdentityPower (RS t b) b r (x : Hilbert)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖S t x‖ :=
  iteratedIdentityPower_sub_domain_rate_bound (S t) (RS t) a b ha hb_pos
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
    (residual_resolvent_left_inverse ε hε h hh hb m g k t) r x

/-- Step recurrence for `(r + 1)`-fold full Hamiltonian resolvent differences. -/
theorem hamiltonianResolvent_iteratedResolventPower_sub_succ_eq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RH t a) (r + 1) f - iteratedResolventPower (RH t b) (r + 1) f =
      ((b - a : ℝ) : ℂ) • RH t a (RH t b (iteratedResolventPower (RH t a) r f)) +
        RH t b (iteratedResolventPower (RH t a) r f - iteratedResolventPower (RH t b) r f) :=
  iteratedResolventPower_sub_succ_eq (H t) (RH t) a b ha hb_pos
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) r f

/-- Membership of `iteratedResolventPower (RH t a) (r + 1) f - iteratedResolventPower (RH t b) (r + 1) f`
in `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`. -/
theorem hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RH t a) (r + 1) f - iteratedResolventPower (RH t b) (r + 1) f ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) :=
  iteratedResolventPower_sub_succ_mem_operatorPowerDomain (H t) (RH t) a b ha hb_pos
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) r f

/-- Two-parameter commutativity of full Hamiltonian Yosida identity approximants. -/
theorem hamiltonianResolvent_iteratedIdentityPower_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r s : ℕ) (f : Hilbert) :
    iteratedIdentityPower (RH t a) a r (iteratedIdentityPower (RH t b) b s f) =
      iteratedIdentityPower (RH t b) b s (iteratedIdentityPower (RH t a) a r f) :=
  iteratedIdentityPower_two_param_comm (H t) (RH t) a b ha hb_pos
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) r s f

/-- Mutual Cauchy rate bound on `(H t).domain` for full Hamiltonian Yosida identity approximants. -/
theorem hamiltonianResolvent_iteratedIdentityPower_sub_domain_rate_bound
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (x : (H t).domain) :
    ‖iteratedIdentityPower (RH t a) a r (x : Hilbert) -
      iteratedIdentityPower (RH t b) b r (x : Hilbert)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖H t x‖ :=
  iteratedIdentityPower_sub_domain_rate_bound (H t) (RH t) a b ha hb_pos
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) r x

/-- Simultaneous `(r + 2)`-th power domain and 10-domain membership for the `(r + 1)`-fold
full Hamiltonian resolvent difference across all `r : ℕ` and observation times `s : ℝ`. -/
theorem hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_ten_domains
    (s a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let d : Hilbert :=
      iteratedResolventPower (RH t a) (r + 1) f - iteratedResolventPower (RH t b) (r + 1) f
    d ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    d ∈ (H t).domain ∧
    d ∈ (K).domain ∧
    d ∈ (S t).domain ∧
    d ∈ (Eavg s).domain ∧
    d ∈ (Tstat).domain ∧
    d ∈ (Kroot).domain ∧
    d ∈ (Tpot).domain ∧
    d ∈ (Tgrow).domain ∧
    d ∈ (Tres s).domain ∧
    d ∈ (clockHalf ε).domain := by
  intro d
  have hmem := hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
    ε hε h hh hb m g k t a b ha hb_pos r f
  exact ⟨hmem, hamiltonianPowerDomain_succ_mem_ten_domains ε hε h hh hb m g k t s (r + 1) hmem⟩

/-- Master Five-Operator Higher-Power Resolvent Difference and Yosida Commutativity Synthesis. -/
theorem five_operator_higher_power_resolvent_difference_master_synthesis
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r s : ℕ) (f : Hilbert) :
    (iteratedResolventPower (RT a) (r + 1) f - iteratedResolventPower (RT b) (r + 1) f ∈
       staticPowerDomain ε hε h (r + 2) ∧
     iteratedResolventPower (RP a) (r + 1) f - iteratedResolventPower (RP b) (r + 1) f ∈
       potentialPowerDomain ε hε h hh hb m g k (r + 2) ∧
     iteratedResolventPower (RG a) (r + 1) f - iteratedResolventPower (RG b) (r + 1) f ∈
       growingPowerDomain ε hε h hh hb m g k (r + 2) ∧
     iteratedResolventPower (RS t a) (r + 1) f - iteratedResolventPower (RS t b) (r + 1) f ∈
       residualPowerDomain ε hε h hh hb m g k t (r + 2) ∧
     iteratedResolventPower (RH t a) (r + 1) f - iteratedResolventPower (RH t b) (r + 1) f ∈
       hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)) ∧
    (iteratedIdentityPower (RT a) a r (iteratedIdentityPower (RT b) b s f) =
       iteratedIdentityPower (RT b) b s (iteratedIdentityPower (RT a) a r f) ∧
     iteratedIdentityPower (RP a) a r (iteratedIdentityPower (RP b) b s f) =
       iteratedIdentityPower (RP b) b s (iteratedIdentityPower (RP a) a r f) ∧
     iteratedIdentityPower (RG a) a r (iteratedIdentityPower (RG b) b s f) =
       iteratedIdentityPower (RG b) b s (iteratedIdentityPower (RG a) a r f) ∧
     iteratedIdentityPower (RS t a) a r (iteratedIdentityPower (RS t b) b s f) =
       iteratedIdentityPower (RS t b) b s (iteratedIdentityPower (RS t a) a r f) ∧
     iteratedIdentityPower (RH t a) a r (iteratedIdentityPower (RH t b) b s f) =
       iteratedIdentityPower (RH t b) b s (iteratedIdentityPower (RH t a) a r f)) :=
  ⟨⟨staticResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
      ε hε h hh hb m g k a b ha hb_pos r f,
    potentialResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
      ε hε h hh hb m g k a b ha hb_pos r f,
    growingResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
      ε hε h hh hb m g k a b ha hb_pos r f,
    residualResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
      ε hε h hh hb m g k t a b ha hb_pos r f,
    hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
      ε hε h hh hb m g k t a b ha hb_pos r f⟩,
   ⟨staticResolvent_iteratedIdentityPower_comm ε hε h hh hb m g k a b ha hb_pos r s f,
    potentialResolvent_iteratedIdentityPower_comm ε hε h hh hb m g k a b ha hb_pos r s f,
    growingResolvent_iteratedIdentityPower_comm ε hε h hh hb m g k a b ha hb_pos r s f,
    residualResolvent_iteratedIdentityPower_comm ε hε h hh hb m g k t a b ha hb_pos r s f,
    hamiltonianResolvent_iteratedIdentityPower_comm ε hε h hh hb m g k t a b ha hb_pos r s f⟩⟩

#print axioms iteratedResolventPower_sub_succ_split
#print axioms iteratedResolventPower_sub_succ_eq
#print axioms iteratedResolventPower_sub_one_eq
#print axioms iteratedResolventPower_sub_succ_mem_operatorPowerDomain
#print axioms iteratedResolventPower_sub_succ_mem_domain
#print axioms iteratedResolventPower_sub_succ_mem_secondPowerDomain
#print axioms iteratedResolventPower_sub_norm_bound
#print axioms iteratedIdentityPower_two_param_comm
#print axioms iteratedIdentityPower_sub_mem_operatorPowerDomain
#print axioms iteratedIdentityPower_sub_norm_le_two
#print axioms iteratedIdentityPower_sub_eq_defect_sub_on_domain
#print axioms iteratedIdentityPower_sub_domain_rate_bound
#print axioms single_yosida_sub_eq_on_domain
#print axioms single_yosida_sub_mem_secondPowerDomain_and_norm_on_domain
#print axioms staticResolvent_iteratedResolventPower_sub_succ_eq
#print axioms staticResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
#print axioms staticResolvent_iteratedIdentityPower_comm
#print axioms staticResolvent_iteratedIdentityPower_sub_domain_rate_bound
#print axioms potentialResolvent_iteratedResolventPower_sub_succ_eq
#print axioms potentialResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
#print axioms potentialResolvent_iteratedIdentityPower_comm
#print axioms potentialResolvent_iteratedIdentityPower_sub_domain_rate_bound
#print axioms growingResolvent_iteratedResolventPower_sub_succ_eq
#print axioms growingResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
#print axioms growingResolvent_iteratedIdentityPower_comm
#print axioms growingResolvent_iteratedIdentityPower_sub_domain_rate_bound
#print axioms residualResolvent_iteratedResolventPower_sub_succ_eq
#print axioms residualResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
#print axioms residualResolvent_iteratedIdentityPower_comm
#print axioms residualResolvent_iteratedIdentityPower_sub_domain_rate_bound
#print axioms hamiltonianResolvent_iteratedResolventPower_sub_succ_eq
#print axioms hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
#print axioms hamiltonianResolvent_iteratedIdentityPower_comm
#print axioms hamiltonianResolvent_iteratedIdentityPower_sub_domain_rate_bound
#print axioms hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_ten_domains
#print axioms five_operator_higher_power_resolvent_difference_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorHigherPowerResolventDifference
