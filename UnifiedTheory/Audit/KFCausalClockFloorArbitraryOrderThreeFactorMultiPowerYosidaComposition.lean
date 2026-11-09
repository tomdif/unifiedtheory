/- Arbitrary-Order Three-Factor Multi-Power `(r, s, q)` and Three-Parameter `(a, b, d)`
Yosida Composition Defect Calculus on `Dom(A^n)` and `Dom(A^{n+1})` Across All Five
Clock-Floor Hamiltonians `T`, `P`, `G`, `S(t)`, and `H(t)`:
1. Generalizes `KFCausalClockFloorArbitraryOrderMultiPowerYosidaCompositionDefect` from
   two-factor `(r, s)` Yosida composition to three-factor `(r, s, q)` and three-parameter
   `(a, b, d)` Yosida smoothing
   `iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q x))`:
   - `operatorPowerDomain A n` invariance, commutation with `iteratedOperatorPower A n`,
     and uniform `kthPowerGraphNormSq A n` contractivity,
   - Three-factor composed defect rate bound on `operatorPowerDomain A (n + 1)`:
     `‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q x)) - x)‖ ≤ ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖`,
   - Squared `n`-th order graph-norm three-factor composed defect bound:
     `kthPowerGraphNormSq A n (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q x)) - x) ≤ ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) ^ 2 * kthPowerGraphNormSq A (n + 1) x`.
2. Instantiates the three-factor multi-power `(r, s, q)` Yosida composition defect
   hierarchy across all five clock-floor Hamiltonians `T`, `P`, `G`, `S(t)`, and `H(t)`. -/
import UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderMultiPowerYosidaCompositionDefect

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderThreeFactorMultiPowerYosidaComposition

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
open KFCausalClockFloorArbitraryOrderMultiPowerYosidaCompositionDefect
  (iteratedIdentityPower_comp_mem_comm_and_contraction
   iteratedOperatorPower_iteratedIdentityPower_comp_defect_rate_on_succ)

section AbstractThreeFactorMultiPowerYosida

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `operatorPowerDomain A n` invariance, commutation with `iteratedOperatorPower A n`,
and `kthPowerGraphNormSq A n` contractivity for the three-factor Yosida smoother
`iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q x))`. -/
theorem iteratedIdentityPower_threeFactor_comp_mem_comm_and_contraction
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hr : ∀ c, 0 < c → Resolves A (R c) c)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ c, 0 < c → ∀ z : A.domain, R c (A z + c • (z : H)) = (z : H))
    (n r s q : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A n) :
    iteratedIdentityPower (R a) a r
      (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q x)) ∈
      operatorPowerDomain A n ∧
    iteratedOperatorPower A n
      (iteratedIdentityPower (R a) a r
        (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q x))) =
      iteratedIdentityPower (R a) a r
        (iteratedIdentityPower (R b) b s
          (iteratedIdentityPower (R d) d q (iteratedOperatorPower A n x))) ∧
    kthPowerGraphNormSq A n
      (iteratedIdentityPower (R a) a r
        (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q x))) ≤
      kthPowerGraphNormSq A n x := by
  have hbd := iteratedIdentityPower_comp_mem_comm_and_contraction
    A R b d hb hd hr hp hl n s q hx
  have habd :
      iteratedIdentityPower (R a) a r
        (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q x)) ∈
        operatorPowerDomain A n :=
    iteratedIdentityPower_maps_operatorPowerDomain_to_self A (R a) a (hr a ha) (hl a ha) n r hbd.1
  have hca :=
    iteratedOperatorPower_iteratedIdentityPower_comm A (R a) a (hr a ha) (hl a ha) n r hbd.1
  have hcontr_a := kthPowerGraphNormSq_iteratedIdentityPower_contraction
    A (R a) a ha (hr a ha) hp (hl a ha) n r hbd.1
  exact ⟨habd, by rw [hca, hbd.2.1], hcontr_a.trans hbd.2.2⟩

/-- Three-factor multi-order `(r, s, q)` Yosida composition defect rate bound on
`operatorPowerDomain A (n + 1)`:
`‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q x)) - x)‖ ≤ ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖`. -/
theorem iteratedOperatorPower_iteratedIdentityPower_threeFactor_defect_rate_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hr : ∀ c, 0 < c → Resolves A (R c) c)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ c, 0 < c → ∀ z : A.domain, R c (A z + c • (z : H)) = (z : H))
    (n r s q : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    ‖iteratedOperatorPower A n
      (iteratedIdentityPower (R a) a r
        (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q x)) - x)‖ ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖ := by
  have hxn : x ∈ operatorPowerDomain A n :=
    operatorPowerDomain_le_of_le A (Nat.le_succ n) hx
  have hx_dom : iteratedOperatorPower A n x ∈ A.domain :=
    iteratedOperatorPower_mem_domain_of_mem_succ A n hx
  have h3 := iteratedIdentityPower_threeFactor_comp_mem_comm_and_contraction
    A R a b d ha hb hd hr hp hl n r s q hxn
  have h2_succ := iteratedIdentityPower_comp_mem_comm_and_contraction
    A R b d hb hd hr hp hl (n + 1) s q hx
  have h2_n := iteratedIdentityPower_comp_mem_comm_and_contraction
    A R b d hb hd hr hp hl n s q hxn
  let z := iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q x)
  have hsplit :
      iteratedIdentityPower (R a) a r z - x =
        (iteratedIdentityPower (R a) a r z - z) + (z - x) := by abel
  have hsub1 := (iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain
    A n h3.1 h2_n.1).2
  have hsub2 := (iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain
    A n h2_n.1 hxn).2
  have hadd := (iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain
    A n ((operatorPowerDomain A n).sub_mem h3.1 h2_n.1)
      ((operatorPowerDomain A n).sub_mem h2_n.1 hxn)).1
  rw [hsplit, hadd]
  have htri := norm_add_le
    (iteratedOperatorPower A n (iteratedIdentityPower (R a) a r z - z))
    (iteratedOperatorPower A n (z - x))
  have hbd2 := iteratedOperatorPower_iteratedIdentityPower_comp_defect_rate_on_succ
    A R b d hb hd hr hp hl n s q hx
  have hz_dom : iteratedOperatorPower A n z ∈ A.domain :=
    iteratedOperatorPower_mem_domain_of_mem_succ A n h2_succ.1
  have hca_z := iteratedOperatorPower_iteratedIdentityPower_comm
    A (R a) a (hr a ha) (hl a ha) n r h2_n.1
  have hba := iteratedIdentityPower_domain_rate_bound
    A (R a) a ha (hr a ha) hp (hl a ha) r ⟨iteratedOperatorPower A n z, hz_dom⟩
  have hAz :
      ‖A ⟨iteratedOperatorPower A n z, hz_dom⟩‖ ≤ ‖iteratedOperatorPower A (n + 1) x‖ := by
    have hsucc_z :
        A ⟨iteratedOperatorPower A n z, hz_dom⟩ = iteratedOperatorPower A (n + 1) z := by
      rw [iteratedOperatorPower_succ_apply, totalOperator_of_mem_domain A hz_dom]
    rw [hsucc_z, h2_succ.2.1]
    have hcb := iteratedIdentityPower_norm_le A (R b) b hb (hr b hb) hp s
      (iteratedIdentityPower (R d) d q (iteratedOperatorPower A (n + 1) x))
    have hcd := iteratedIdentityPower_norm_le A (R d) d hd (hr d hd) hp q
      (iteratedOperatorPower A (n + 1) x)
    exact hcb.trans hcd
  have hba' :
      ‖iteratedIdentityPower (R a) a r (iteratedOperatorPower A n z) -
          iteratedOperatorPower A n z‖ ≤
        ((r : ℝ) * a⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖ := by
    have hr_nn : 0 ≤ (r : ℝ) * a⁻¹ :=
      mul_nonneg (Nat.cast_nonneg r) (inv_nonneg.mpr (le_of_lt ha))
    exact hba.trans (mul_le_mul_of_nonneg_left hAz hr_nn)
  calc
    ‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r z - z) +
        iteratedOperatorPower A n (z - x)‖
      ≤ ‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r z - z)‖ +
          ‖iteratedOperatorPower A n (z - x)‖ := htri
    _ = ‖iteratedIdentityPower (R a) a r (iteratedOperatorPower A n z) -
            iteratedOperatorPower A n z‖ +
          ‖iteratedOperatorPower A n (z - x)‖ := by rw [hsub1, hca_z]
    _ ≤ ((r : ℝ) * a⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖ +
          ((s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖ :=
        add_le_add hba' hbd2
    _ = ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) *
          ‖iteratedOperatorPower A (n + 1) x‖ := by ring

/-- Squared `n`-th order graph-norm three-factor multi-order `(r, s, q)` Yosida
composition defect bound on `operatorPowerDomain A (n + 1)`. -/
theorem kthPowerGraphNormSq_iteratedIdentityPower_threeFactor_defect_bound_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hr : ∀ c, 0 < c → Resolves A (R c) c)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ c, 0 < c → ∀ z : A.domain, R c (A z + c • (z : H)) = (z : H))
    (n r s q : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    kthPowerGraphNormSq A n
      (iteratedIdentityPower (R a) a r
        (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q x)) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) ^ 2 * kthPowerGraphNormSq A (n + 1) x := by
  have h1 :
      kthPowerGraphNormSq A n
        (iteratedIdentityPower (R a) a r
          (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q x)) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) ^ 2 *
        (∑ j ∈ Finset.range (n + 1), ‖iteratedOperatorPower A (j + 1) x‖ ^ 2) := by
    unfold kthPowerGraphNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hxj : x ∈ operatorPowerDomain A (j + 1) :=
      operatorPowerDomain_le_of_le A (Nat.succ_le_succ hjn) hx
    have hbd := iteratedOperatorPower_iteratedIdentityPower_threeFactor_defect_rate_on_succ
      A R a b d ha hb hd hr hp hl j r s q hxj
    have hsq :
        ‖iteratedOperatorPower A j
          (iteratedIdentityPower (R a) a r
            (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q x)) - x)‖ ^ 2 ≤
        (((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) *
          ‖iteratedOperatorPower A (j + 1) x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbd 2
    linarith [mul_pow ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹)
      ‖iteratedOperatorPower A (j + 1) x‖ 2]
  have h2 := mul_le_mul_of_nonneg_left
    (sum_succ_iteratedOperatorPower_sq_le_kthPowerGraphNormSq_succ A n x)
    (sq_nonneg ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹))
  exact h1.trans h2

end AbstractThreeFactorMultiPowerYosida

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

/-- Three-factor multi-order `(r, s, q)` Yosida contraction and defect bound on
`staticPowerDomain ε hε h (n + 1)` for `T`. -/
theorem static_arbitraryOrder_threeFactor_yosida_package
    (a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (n r s q : ℕ) {x : Hilbert}
    (hx : x ∈ staticPowerDomain ε hε h (n + 1)) :
    kthPowerGraphNormSq T (n + 1)
      (iteratedIdentityPower (RT a) a r
        (iteratedIdentityPower (RT b) b s (iteratedIdentityPower (RT d) d q x))) ≤
      kthPowerGraphNormSq T (n + 1) x ∧
    kthPowerGraphNormSq T n
      (iteratedIdentityPower (RT a) a r
        (iteratedIdentityPower (RT b) b s (iteratedIdentityPower (RT d) d q x)) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) ^ 2 * kthPowerGraphNormSq T (n + 1) x :=
  ⟨(iteratedIdentityPower_threeFactor_comp_mem_comm_and_contraction T RT a b d ha hb_pos hd
     (staticResolvent_resolves ε hε h hb hh)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh) (n + 1) r s q hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_threeFactor_defect_bound_on_succ T RT a b d ha hb_pos hd
     (staticResolvent_resolves ε hε h hb hh)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh) n r s q hx⟩

/-- Three-factor multi-order `(r, s, q)` Yosida contraction and defect bound on
`potentialPowerDomain ε hε h hh hb m g k (n + 1)` for `P`. -/
theorem potential_arbitraryOrder_threeFactor_yosida_package
    (a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (n r s q : ℕ) {x : Hilbert}
    (hx : x ∈ potentialPowerDomain ε hε h hh hb m g k (n + 1)) :
    kthPowerGraphNormSq P (n + 1)
      (iteratedIdentityPower (RP a) a r
        (iteratedIdentityPower (RP b) b s (iteratedIdentityPower (RP d) d q x))) ≤
      kthPowerGraphNormSq P (n + 1) x ∧
    kthPowerGraphNormSq P n
      (iteratedIdentityPower (RP a) a r
        (iteratedIdentityPower (RP b) b s (iteratedIdentityPower (RP d) d q x)) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) ^ 2 * kthPowerGraphNormSq P (n + 1) x :=
  ⟨(iteratedIdentityPower_threeFactor_comp_mem_comm_and_contraction P RP a b d ha hb_pos hd
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k)
     (n + 1) r s q hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_threeFactor_defect_bound_on_succ P RP a b d ha hb_pos hd
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k) n r s q hx⟩

/-- Three-factor multi-order `(r, s, q)` Yosida contraction and defect bound on
`growingPowerDomain ε hε h hh hb m g k (n + 1)` for `G`. -/
theorem growing_arbitraryOrder_threeFactor_yosida_package
    (a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (n r s q : ℕ) {x : Hilbert}
    (hx : x ∈ growingPowerDomain ε hε h hh hb m g k (n + 1)) :
    kthPowerGraphNormSq G (n + 1)
      (iteratedIdentityPower (RG a) a r
        (iteratedIdentityPower (RG b) b s (iteratedIdentityPower (RG d) d q x))) ≤
      kthPowerGraphNormSq G (n + 1) x ∧
    kthPowerGraphNormSq G n
      (iteratedIdentityPower (RG a) a r
        (iteratedIdentityPower (RG b) b s (iteratedIdentityPower (RG d) d q x)) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) ^ 2 * kthPowerGraphNormSq G (n + 1) x :=
  ⟨(iteratedIdentityPower_threeFactor_comp_mem_comm_and_contraction G RG a b d ha hb_pos hd
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) (n + 1) r s q hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_threeFactor_defect_bound_on_succ G RG a b d ha hb_pos hd
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) n r s q hx⟩

/-- Three-factor multi-order `(r, s, q)` Yosida contraction and defect bound on
`residualPowerDomain ε hε h hh hb m g k t (n + 1)` for `S t`. -/
theorem residual_arbitraryOrder_threeFactor_yosida_package
    (t a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (n r s q : ℕ) {x : Hilbert}
    (hx : x ∈ residualPowerDomain ε hε h hh hb m g k t (n + 1)) :
    kthPowerGraphNormSq (S t) (n + 1)
      (iteratedIdentityPower (RS t a) a r
        (iteratedIdentityPower (RS t b) b s (iteratedIdentityPower (RS t d) d q x))) ≤
      kthPowerGraphNormSq (S t) (n + 1) x ∧
    kthPowerGraphNormSq (S t) n
      (iteratedIdentityPower (RS t a) a r
        (iteratedIdentityPower (RS t b) b s (iteratedIdentityPower (RS t d) d q x)) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) ^ 2 * kthPowerGraphNormSq (S t) (n + 1) x :=
  ⟨(iteratedIdentityPower_threeFactor_comp_mem_comm_and_contraction (S t) (RS t) a b d ha hb_pos hd
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t)
     (n + 1) r s q hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_threeFactor_defect_bound_on_succ (S t) (RS t) a b d ha hb_pos hd
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t) n r s q hx⟩

/-- Three-factor multi-order `(r, s, q)` Yosida contraction and defect bound on
`hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)` for `H t`. -/
theorem hamiltonian_arbitraryOrder_threeFactor_yosida_package
    (t a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (n r s q : ℕ) {x : Hilbert}
    (hx : x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)) :
    kthPowerGraphNormSq (H t) (n + 1)
      (iteratedIdentityPower (RH t a) a r
        (iteratedIdentityPower (RH t b) b s (iteratedIdentityPower (RH t d) d q x))) ≤
      kthPowerGraphNormSq (H t) (n + 1) x ∧
    kthPowerGraphNormSq (H t) n
      (iteratedIdentityPower (RH t a) a r
        (iteratedIdentityPower (RH t b) b s (iteratedIdentityPower (RH t d) d q x)) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) ^ 2 * kthPowerGraphNormSq (H t) (n + 1) x :=
  ⟨(iteratedIdentityPower_threeFactor_comp_mem_comm_and_contraction (H t) (RH t) a b d ha hb_pos hd
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t)
     (n + 1) r s q hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_threeFactor_defect_bound_on_succ (H t) (RH t) a b d ha hb_pos hd
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) n r s q hx⟩

/-- Master Five-Operator Arbitrary-Order Three-Factor Multi-Power `(r, s, q)` Yosida
Composition Defect Synthesis across `T`, `P`, `G`, `S(t)`, and `H(t)`. -/
theorem fiveOperator_arbitraryOrder_threeFactor_yosida_composition_master_synthesis
    (t a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (n r s q : ℕ)
    {xT xP xG xS xH : Hilbert}
    (hxT : xT ∈ staticPowerDomain ε hε h (n + 1))
    (hxP : xP ∈ potentialPowerDomain ε hε h hh hb m g k (n + 1))
    (hxG : xG ∈ growingPowerDomain ε hε h hh hb m g k (n + 1))
    (hxS : xS ∈ residualPowerDomain ε hε h hh hb m g k t (n + 1))
    (hxH : xH ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)) :
    let rateSq := ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹) ^ 2
    kthPowerGraphNormSq T n
      (iteratedIdentityPower (RT a) a r
        (iteratedIdentityPower (RT b) b s (iteratedIdentityPower (RT d) d q xT)) - xT) ≤
      rateSq * kthPowerGraphNormSq T (n + 1) xT ∧
    kthPowerGraphNormSq P n
      (iteratedIdentityPower (RP a) a r
        (iteratedIdentityPower (RP b) b s (iteratedIdentityPower (RP d) d q xP)) - xP) ≤
      rateSq * kthPowerGraphNormSq P (n + 1) xP ∧
    kthPowerGraphNormSq G n
      (iteratedIdentityPower (RG a) a r
        (iteratedIdentityPower (RG b) b s (iteratedIdentityPower (RG d) d q xG)) - xG) ≤
      rateSq * kthPowerGraphNormSq G (n + 1) xG ∧
    kthPowerGraphNormSq (S t) n
      (iteratedIdentityPower (RS t a) a r
        (iteratedIdentityPower (RS t b) b s (iteratedIdentityPower (RS t d) d q xS)) - xS) ≤
      rateSq * kthPowerGraphNormSq (S t) (n + 1) xS ∧
    kthPowerGraphNormSq (H t) n
      (iteratedIdentityPower (RH t a) a r
        (iteratedIdentityPower (RH t b) b s (iteratedIdentityPower (RH t d) d q xH)) - xH) ≤
      rateSq * kthPowerGraphNormSq (H t) (n + 1) xH := by
  intro rateSq
  have hT := static_arbitraryOrder_threeFactor_yosida_package ε hε h hh hb a b d ha hb_pos hd n r s q hxT
  have hP := potential_arbitraryOrder_threeFactor_yosida_package ε hε h hh hb m g k a b d ha hb_pos hd n r s q hxP
  have hG := growing_arbitraryOrder_threeFactor_yosida_package ε hε h hh hb m g k a b d ha hb_pos hd n r s q hxG
  have hS := residual_arbitraryOrder_threeFactor_yosida_package ε hε h hh hb m g k t a b d ha hb_pos hd n r s q hxS
  have hH := hamiltonian_arbitraryOrder_threeFactor_yosida_package ε hε h hh hb m g k t a b d ha hb_pos hd n r s q hxH
  exact ⟨hT.2, hP.2, hG.2, hS.2, hH.2⟩

#print axioms iteratedIdentityPower_threeFactor_comp_mem_comm_and_contraction
#print axioms iteratedOperatorPower_iteratedIdentityPower_threeFactor_defect_rate_on_succ
#print axioms kthPowerGraphNormSq_iteratedIdentityPower_threeFactor_defect_bound_on_succ
#print axioms static_arbitraryOrder_threeFactor_yosida_package
#print axioms potential_arbitraryOrder_threeFactor_yosida_package
#print axioms growing_arbitraryOrder_threeFactor_yosida_package
#print axioms residual_arbitraryOrder_threeFactor_yosida_package
#print axioms hamiltonian_arbitraryOrder_threeFactor_yosida_package
#print axioms fiveOperator_arbitraryOrder_threeFactor_yosida_composition_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderThreeFactorMultiPowerYosidaComposition
