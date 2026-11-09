/- Arbitrary-Order Multi-Power `(r, s)` and Two-Parameter `(a, b)` Yosida Difference and
Composition Defect Calculus on `Dom(A^n)` and `Dom(A^{n+1})` Across All Five Clock-Floor
Hamiltonians `T`, `P`, `G`, `S(t)`, and `H(t)`:
1. Generalizes `KFCausalClockFloorArbitraryOrderTwoParameterYosidaCauchyRate` from equal
   Yosida power `(r, r)` to arbitrary distinct orders `(r, s)` and shifts `(a, b)`:
   - Exact commutation of `iteratedOperatorPower A n` with the multi-order Yosida difference
     `iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b s x` on `operatorPowerDomain A n`,
   - Arbitrary-order multi-power Cauchy rate bound on `operatorPowerDomain A (n + 1)`:
     `‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b s x)‖ ≤ ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖`,
   - Squared `n`-th order graph-norm bound
     `kthPowerGraphNormSq A n (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b s x) ≤ ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq A (n + 1) x`.
2. Establishes the arbitrary-order composed Yosida smoother
   `iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s x)` on `operatorPowerDomain A n`:
   - `operatorPowerDomain A n` invariance and commutation with `iteratedOperatorPower A n`,
   - Uniform `kthPowerGraphNormSq A n` contractivity,
   - Composed defect rate bound on `operatorPowerDomain A (n + 1)`:
     `‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s x) - x)‖ ≤ ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖`,
   - Squared `n`-th order graph-norm composed defect bound
     `kthPowerGraphNormSq A n (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s x) - x) ≤ ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq A (n + 1) x`.
3. Instantiates the multi-power `(r, s)` Yosida difference and composition defect hierarchy
   across all five clock-floor Hamiltonians `T`, `P`, `G`, `S(t)`, and `H(t)`. -/
import UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderTwoParameterYosidaCauchyRate

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderMultiPowerYosidaCompositionDefect

noncomputable section

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
  (iteratedIdentityPower iteratedIdentityPower_sub
   iteratedIdentityPower_norm_le iteratedIdentityPower_domain_rate_bound)
open KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence
  (totalOperator totalOperator_of_mem_domain
   iteratedOperatorPower iteratedOperatorPower_succ_apply
   iteratedOperatorPower_mem_domain_of_mem_succ
   iteratedIdentityPower_maps_operatorPowerDomain_to_self
   iteratedOperatorPower_iteratedIdentityPower_comm
   kthPowerGraphNormSq
   kthPowerGraphNormSq_iteratedIdentityPower_contraction)
open KFCausalClockFloorArbitraryOrderTwoParameterYosidaCauchyRate
  (iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain
   sum_succ_iteratedOperatorPower_sq_le_kthPowerGraphNormSq_succ)

/-! ### 1. Abstract Multi-Order `(r, s)` Yosida Difference and Composition Defect Calculus -/

section AbstractMultiPowerYosida

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact commutation of `iteratedOperatorPower A n` with the multi-order `(r, s)` Yosida
identity difference `iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b s x`
on `operatorPowerDomain A n`. -/
theorem iteratedOperatorPower_iteratedIdentityPower_multiOrder_sub_comm
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (n r s : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A n) :
    iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b s x ∈
      operatorPowerDomain A n ∧
    iteratedOperatorPower A n
      (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b s x) =
      iteratedIdentityPower (R a) a r (iteratedOperatorPower A n x) -
        iteratedIdentityPower (R b) b s (iteratedOperatorPower A n x) := by
  have hxa : iteratedIdentityPower (R a) a r x ∈ operatorPowerDomain A n :=
    iteratedIdentityPower_maps_operatorPowerDomain_to_self A (R a) a (hr a ha) (hl a ha) n r hx
  have hxb : iteratedIdentityPower (R b) b s x ∈ operatorPowerDomain A n :=
    iteratedIdentityPower_maps_operatorPowerDomain_to_self A (R b) b (hr b hb) (hl b hb) n s hx
  have hsub := (iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain A n hxa hxb).2
  have hca := iteratedOperatorPower_iteratedIdentityPower_comm A (R a) a (hr a ha) (hl a ha) n r hx
  have hcb := iteratedOperatorPower_iteratedIdentityPower_comm A (R b) b (hr b hb) (hl b hb) n s hx
  exact ⟨(operatorPowerDomain A n).sub_mem hxa hxb, by rw [hsub, hca, hcb]⟩

/-- Multi-order `(r, s)` Yosida Cauchy rate bound on `operatorPowerDomain A (n + 1)`:
`‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b s x)‖ ≤ ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖`. -/
theorem iteratedOperatorPower_iteratedIdentityPower_multiOrder_rate_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (n r s : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    ‖iteratedOperatorPower A n
      (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b s x)‖ ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖ := by
  have hxn : x ∈ operatorPowerDomain A n :=
    operatorPowerDomain_le_of_le A (Nat.le_succ n) hx
  have hx_dom : iteratedOperatorPower A n x ∈ A.domain :=
    iteratedOperatorPower_mem_domain_of_mem_succ A n hx
  let y := iteratedOperatorPower A n x
  rw [(iteratedOperatorPower_iteratedIdentityPower_multiOrder_sub_comm
    A R a b ha hb hr hl n r s hxn).2]
  have hsplit :
      iteratedIdentityPower (R a) a r y - iteratedIdentityPower (R b) b s y =
        (iteratedIdentityPower (R a) a r y - y) -
          (iteratedIdentityPower (R b) b s y - y) := by abel
  rw [hsplit, iteratedOperatorPower_succ_apply, totalOperator_of_mem_domain A hx_dom]
  have htri := norm_sub_le
    (iteratedIdentityPower (R a) a r y - y)
    (iteratedIdentityPower (R b) b s y - y)
  have hba := iteratedIdentityPower_domain_rate_bound
    A (R a) a ha (hr a ha) hp (hl a ha) r ⟨y, hx_dom⟩
  have hbb := iteratedIdentityPower_domain_rate_bound
    A (R b) b hb (hr b hb) hp (hl b hb) s ⟨y, hx_dom⟩
  linarith [add_mul ((r : ℝ) * a⁻¹) ((s : ℝ) * b⁻¹) ‖A ⟨y, hx_dom⟩‖]

/-- Squared `n`-th order graph-norm multi-order `(r, s)` Yosida Cauchy rate bound on
`operatorPowerDomain A (n + 1)`. -/
theorem kthPowerGraphNormSq_iteratedIdentityPower_multiOrder_rate_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (n r s : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    kthPowerGraphNormSq A n
      (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b s x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq A (n + 1) x := by
  have h1 :
      kthPowerGraphNormSq A n
        (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b s x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 *
        (∑ j ∈ Finset.range (n + 1), ‖iteratedOperatorPower A (j + 1) x‖ ^ 2) := by
    unfold kthPowerGraphNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hxj : x ∈ operatorPowerDomain A (j + 1) :=
      operatorPowerDomain_le_of_le A (Nat.succ_le_succ hjn) hx
    have hbd := iteratedOperatorPower_iteratedIdentityPower_multiOrder_rate_on_succ
      A R a b ha hb hr hp hl j r s hxj
    have hsq :
        ‖iteratedOperatorPower A j
          (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b s x)‖ ^ 2 ≤
        (((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) * ‖iteratedOperatorPower A (j + 1) x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbd 2
    linarith [mul_pow ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ‖iteratedOperatorPower A (j + 1) x‖ 2]
  have h2 := mul_le_mul_of_nonneg_left
    (sum_succ_iteratedOperatorPower_sq_le_kthPowerGraphNormSq_succ A n x)
    (sq_nonneg ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹))
  exact h1.trans h2

/-- `operatorPowerDomain A n` invariance, commutation with `iteratedOperatorPower A n`,
and `kthPowerGraphNormSq A n` contractivity for the composed Yosida smoother
`iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s x)`. -/
theorem iteratedIdentityPower_comp_mem_comm_and_contraction
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (n r s : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A n) :
    iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s x) ∈
      operatorPowerDomain A n ∧
    iteratedOperatorPower A n
      (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s x)) =
      iteratedIdentityPower (R a) a r
        (iteratedIdentityPower (R b) b s (iteratedOperatorPower A n x)) ∧
    kthPowerGraphNormSq A n
      (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s x)) ≤
      kthPowerGraphNormSq A n x := by
  have hxb : iteratedIdentityPower (R b) b s x ∈ operatorPowerDomain A n :=
    iteratedIdentityPower_maps_operatorPowerDomain_to_self A (R b) b (hr b hb) (hl b hb) n s hx
  have hxab :
      iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s x) ∈
        operatorPowerDomain A n :=
    iteratedIdentityPower_maps_operatorPowerDomain_to_self A (R a) a (hr a ha) (hl a ha) n r hxb
  have hca :=
    iteratedOperatorPower_iteratedIdentityPower_comm A (R a) a (hr a ha) (hl a ha) n r hxb
  have hcb :=
    iteratedOperatorPower_iteratedIdentityPower_comm A (R b) b (hr b hb) (hl b hb) n s hx
  have hcontr_a := kthPowerGraphNormSq_iteratedIdentityPower_contraction
    A (R a) a ha (hr a ha) hp (hl a ha) n r hxb
  have hcontr_b := kthPowerGraphNormSq_iteratedIdentityPower_contraction
    A (R b) b hb (hr b hb) hp (hl b hb) n s hx
  exact ⟨hxab, by rw [hca, hcb], hcontr_a.trans hcontr_b⟩

/-- Composed two-parameter multi-order `(r, s)` Yosida defect rate bound on
`operatorPowerDomain A (n + 1)`:
`‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s x) - x)‖ ≤ ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖`. -/
theorem iteratedOperatorPower_iteratedIdentityPower_comp_defect_rate_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (n r s : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    ‖iteratedOperatorPower A n
      (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s x) - x)‖ ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖ := by
  have hxn : x ∈ operatorPowerDomain A n :=
    operatorPowerDomain_le_of_le A (Nat.le_succ n) hx
  have hx_dom : iteratedOperatorPower A n x ∈ A.domain :=
    iteratedOperatorPower_mem_domain_of_mem_succ A n hx
  have hcomp := iteratedIdentityPower_comp_mem_comm_and_contraction
    A R a b ha hb hr hp hl n r s hxn
  have hsub := (iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain
    A n hcomp.1 hxn).2
  let y := iteratedOperatorPower A n x
  rw [hsub, hcomp.2.1]
  have hsplit :
      iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s y) - y =
        iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s y - y) +
          (iteratedIdentityPower (R a) a r y - y) := by
    rw [iteratedIdentityPower_sub (R a) a r (iteratedIdentityPower (R b) b s y) y]
    abel
  rw [hsplit, iteratedOperatorPower_succ_apply, totalOperator_of_mem_domain A hx_dom]
  have htri := norm_add_le
    (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s y - y))
    (iteratedIdentityPower (R a) a r y - y)
  have hcontr := iteratedIdentityPower_norm_le
    A (R a) a ha (hr a ha) hp r (iteratedIdentityPower (R b) b s y - y)
  have hba := iteratedIdentityPower_domain_rate_bound
    A (R a) a ha (hr a ha) hp (hl a ha) r ⟨y, hx_dom⟩
  have hbb := iteratedIdentityPower_domain_rate_bound
    A (R b) b hb (hr b hb) hp (hl b hb) s ⟨y, hx_dom⟩
  linarith [add_mul ((r : ℝ) * a⁻¹) ((s : ℝ) * b⁻¹) ‖A ⟨y, hx_dom⟩‖]

/-- Squared `n`-th order graph-norm composed defect bound on `operatorPowerDomain A (n + 1)`:
`kthPowerGraphNormSq A n (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s x) - x) ≤ ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq A (n + 1) x`. -/
theorem kthPowerGraphNormSq_iteratedIdentityPower_comp_defect_bound_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (n r s : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    kthPowerGraphNormSq A n
      (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s x) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq A (n + 1) x := by
  have h1 :
      kthPowerGraphNormSq A n
        (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s x) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 *
        (∑ j ∈ Finset.range (n + 1), ‖iteratedOperatorPower A (j + 1) x‖ ^ 2) := by
    unfold kthPowerGraphNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hxj : x ∈ operatorPowerDomain A (j + 1) :=
      operatorPowerDomain_le_of_le A (Nat.succ_le_succ hjn) hx
    have hbd := iteratedOperatorPower_iteratedIdentityPower_comp_defect_rate_on_succ
      A R a b ha hb hr hp hl j r s hxj
    have hsq :
        ‖iteratedOperatorPower A j
          (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s x) - x)‖ ^ 2 ≤
        (((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) * ‖iteratedOperatorPower A (j + 1) x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbd 2
    linarith [mul_pow ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ‖iteratedOperatorPower A (j + 1) x‖ 2]
  have h2 := mul_le_mul_of_nonneg_left
    (sum_succ_iteratedOperatorPower_sq_le_kthPowerGraphNormSq_succ A n x)
    (sq_nonneg ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹))
  exact h1.trans h2

end AbstractMultiPowerYosida

/-! ### 2. Concrete Five-Operator Instantiations Across `T`, `P`, `G`, `S(t)`, and `H(t)` -/

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

/-- Multi-order `(r, s)` Yosida difference and composed defect bounds on
`staticPowerDomain ε hε h (n + 1)` for `T`. -/
theorem static_arbitraryOrder_multiPower_yosida_package
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r s : ℕ) {x : Hilbert}
    (hx : x ∈ staticPowerDomain ε hε h (n + 1)) :
    kthPowerGraphNormSq T n
      (iteratedIdentityPower (RT a) a r x - iteratedIdentityPower (RT b) b s x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq T (n + 1) x ∧
    kthPowerGraphNormSq T n
      (iteratedIdentityPower (RT a) a r (iteratedIdentityPower (RT b) b s x) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq T (n + 1) x :=
  ⟨kthPowerGraphNormSq_iteratedIdentityPower_multiOrder_rate_on_succ T RT a b ha hb_pos
     (staticResolvent_resolves ε hε h hb hh)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh) n r s hx,
   kthPowerGraphNormSq_iteratedIdentityPower_comp_defect_bound_on_succ T RT a b ha hb_pos
     (staticResolvent_resolves ε hε h hb hh)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh) n r s hx⟩

/-- Multi-order `(r, s)` Yosida difference and composed defect bounds on
`potentialPowerDomain ε hε h hh hb m g k (n + 1)` for `P`. -/
theorem potential_arbitraryOrder_multiPower_yosida_package
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r s : ℕ) {x : Hilbert}
    (hx : x ∈ potentialPowerDomain ε hε h hh hb m g k (n + 1)) :
    kthPowerGraphNormSq P n
      (iteratedIdentityPower (RP a) a r x - iteratedIdentityPower (RP b) b s x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq P (n + 1) x ∧
    kthPowerGraphNormSq P n
      (iteratedIdentityPower (RP a) a r (iteratedIdentityPower (RP b) b s x) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq P (n + 1) x :=
  ⟨kthPowerGraphNormSq_iteratedIdentityPower_multiOrder_rate_on_succ P RP a b ha hb_pos
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k) n r s hx,
   kthPowerGraphNormSq_iteratedIdentityPower_comp_defect_bound_on_succ P RP a b ha hb_pos
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k) n r s hx⟩

/-- Multi-order `(r, s)` Yosida difference and composed defect bounds on
`growingPowerDomain ε hε h hh hb m g k (n + 1)` for `G`. -/
theorem growing_arbitraryOrder_multiPower_yosida_package
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r s : ℕ) {x : Hilbert}
    (hx : x ∈ growingPowerDomain ε hε h hh hb m g k (n + 1)) :
    kthPowerGraphNormSq G n
      (iteratedIdentityPower (RG a) a r x - iteratedIdentityPower (RG b) b s x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq G (n + 1) x ∧
    kthPowerGraphNormSq G n
      (iteratedIdentityPower (RG a) a r (iteratedIdentityPower (RG b) b s x) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq G (n + 1) x :=
  ⟨kthPowerGraphNormSq_iteratedIdentityPower_multiOrder_rate_on_succ G RG a b ha hb_pos
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) n r s hx,
   kthPowerGraphNormSq_iteratedIdentityPower_comp_defect_bound_on_succ G RG a b ha hb_pos
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) n r s hx⟩

/-- Multi-order `(r, s)` Yosida difference and composed defect bounds on
`residualPowerDomain ε hε h hh hb m g k t (n + 1)` for `S t`. -/
theorem residual_arbitraryOrder_multiPower_yosida_package
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r s : ℕ) {x : Hilbert}
    (hx : x ∈ residualPowerDomain ε hε h hh hb m g k t (n + 1)) :
    kthPowerGraphNormSq (S t) n
      (iteratedIdentityPower (RS t a) a r x - iteratedIdentityPower (RS t b) b s x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (S t) (n + 1) x ∧
    kthPowerGraphNormSq (S t) n
      (iteratedIdentityPower (RS t a) a r (iteratedIdentityPower (RS t b) b s x) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (S t) (n + 1) x :=
  ⟨kthPowerGraphNormSq_iteratedIdentityPower_multiOrder_rate_on_succ (S t) (RS t) a b ha hb_pos
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t) n r s hx,
   kthPowerGraphNormSq_iteratedIdentityPower_comp_defect_bound_on_succ (S t) (RS t) a b ha hb_pos
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t) n r s hx⟩

/-- Multi-order `(r, s)` Yosida difference and composed defect bounds on
`hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)` for `H t`. -/
theorem hamiltonian_arbitraryOrder_multiPower_yosida_package
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r s : ℕ) {x : Hilbert}
    (hx : x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)) :
    kthPowerGraphNormSq (H t) n
      (iteratedIdentityPower (RH t a) a r x - iteratedIdentityPower (RH t b) b s x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (H t) (n + 1) x ∧
    kthPowerGraphNormSq (H t) n
      (iteratedIdentityPower (RH t a) a r (iteratedIdentityPower (RH t b) b s x) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (H t) (n + 1) x :=
  ⟨kthPowerGraphNormSq_iteratedIdentityPower_multiOrder_rate_on_succ (H t) (RH t) a b ha hb_pos
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) n r s hx,
   kthPowerGraphNormSq_iteratedIdentityPower_comp_defect_bound_on_succ (H t) (RH t) a b ha hb_pos
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) n r s hx⟩

/-- Master Five-Operator Arbitrary-Order Multi-Power `(r, s)` Yosida Difference and
Composition Defect Synthesis across `T`, `P`, `G`, `S(t)`, and `H(t)`. -/
theorem fiveOperator_arbitraryOrder_multiPower_yosida_composition_master_synthesis
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r s : ℕ)
    {xT xP xG xS xH : Hilbert}
    (hxT : xT ∈ staticPowerDomain ε hε h (n + 1))
    (hxP : xP ∈ potentialPowerDomain ε hε h hh hb m g k (n + 1))
    (hxG : xG ∈ growingPowerDomain ε hε h hh hb m g k (n + 1))
    (hxS : xS ∈ residualPowerDomain ε hε h hh hb m g k t (n + 1))
    (hxH : xH ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)) :
    (kthPowerGraphNormSq T n
       (iteratedIdentityPower (RT a) a r xT - iteratedIdentityPower (RT b) b s xT) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq T (n + 1) xT ∧
     kthPowerGraphNormSq P n
       (iteratedIdentityPower (RP a) a r xP - iteratedIdentityPower (RP b) b s xP) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq P (n + 1) xP ∧
     kthPowerGraphNormSq G n
       (iteratedIdentityPower (RG a) a r xG - iteratedIdentityPower (RG b) b s xG) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq G (n + 1) xG ∧
     kthPowerGraphNormSq (S t) n
       (iteratedIdentityPower (RS t a) a r xS - iteratedIdentityPower (RS t b) b s xS) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (S t) (n + 1) xS ∧
     kthPowerGraphNormSq (H t) n
       (iteratedIdentityPower (RH t a) a r xH - iteratedIdentityPower (RH t b) b s xH) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (H t) (n + 1) xH) ∧
    (kthPowerGraphNormSq T n
       (iteratedIdentityPower (RT a) a r (iteratedIdentityPower (RT b) b s xT) - xT) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq T (n + 1) xT ∧
     kthPowerGraphNormSq P n
       (iteratedIdentityPower (RP a) a r (iteratedIdentityPower (RP b) b s xP) - xP) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq P (n + 1) xP ∧
     kthPowerGraphNormSq G n
       (iteratedIdentityPower (RG a) a r (iteratedIdentityPower (RG b) b s xG) - xG) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq G (n + 1) xG ∧
     kthPowerGraphNormSq (S t) n
       (iteratedIdentityPower (RS t a) a r (iteratedIdentityPower (RS t b) b s xS) - xS) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (S t) (n + 1) xS ∧
     kthPowerGraphNormSq (H t) n
       (iteratedIdentityPower (RH t a) a r (iteratedIdentityPower (RH t b) b s xH) - xH) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (H t) (n + 1) xH) := by
  have hT := static_arbitraryOrder_multiPower_yosida_package ε hε h hh hb a b ha hb_pos n r s hxT
  have hP := potential_arbitraryOrder_multiPower_yosida_package ε hε h hh hb m g k a b ha hb_pos n r s hxP
  have hG := growing_arbitraryOrder_multiPower_yosida_package ε hε h hh hb m g k a b ha hb_pos n r s hxG
  have hS := residual_arbitraryOrder_multiPower_yosida_package ε hε h hh hb m g k t a b ha hb_pos n r s hxS
  have hH := hamiltonian_arbitraryOrder_multiPower_yosida_package ε hε h hh hb m g k t a b ha hb_pos n r s hxH
  exact ⟨⟨hT.1, hP.1, hG.1, hS.1, hH.1⟩, ⟨hT.2, hP.2, hG.2, hS.2, hH.2⟩⟩

#print axioms iteratedOperatorPower_iteratedIdentityPower_multiOrder_sub_comm
#print axioms iteratedOperatorPower_iteratedIdentityPower_multiOrder_rate_on_succ
#print axioms kthPowerGraphNormSq_iteratedIdentityPower_multiOrder_rate_on_succ
#print axioms iteratedIdentityPower_comp_mem_comm_and_contraction
#print axioms iteratedOperatorPower_iteratedIdentityPower_comp_defect_rate_on_succ
#print axioms kthPowerGraphNormSq_iteratedIdentityPower_comp_defect_bound_on_succ
#print axioms static_arbitraryOrder_multiPower_yosida_package
#print axioms potential_arbitraryOrder_multiPower_yosida_package
#print axioms growing_arbitraryOrder_multiPower_yosida_package
#print axioms residual_arbitraryOrder_multiPower_yosida_package
#print axioms hamiltonian_arbitraryOrder_multiPower_yosida_package
#print axioms fiveOperator_arbitraryOrder_multiPower_yosida_composition_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderMultiPowerYosidaCompositionDefect
