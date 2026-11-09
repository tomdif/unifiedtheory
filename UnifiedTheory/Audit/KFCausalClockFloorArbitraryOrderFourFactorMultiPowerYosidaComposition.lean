/- Arbitrary-Order Four-Factor Multi-Power `(r, s, q, p)` and Four-Parameter `(a, b, d, e)`
Yosida Composition Defect Calculus on `Dom(A^n)` and `Dom(A^{n+1})` Across All Five
Clock-Floor Hamiltonians `T`, `P`, `G`, `S(t)`, and `H(t)`. -/
import UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderThreeFactorMultiPowerYosidaComposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderFourFactorMultiPowerYosidaComposition

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
open KFCausalClockFloorArbitraryOrderThreeFactorMultiPowerYosidaComposition
  (iteratedIdentityPower_threeFactor_comp_mem_comm_and_contraction
   iteratedOperatorPower_iteratedIdentityPower_threeFactor_defect_rate_on_succ)

section AbstractFourFactorMultiPowerYosida

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `operatorPowerDomain A n` invariance, commutation with `iteratedOperatorPower A n`,
and `kthPowerGraphNormSq A n` contractivity for the four-factor Yosida smoother
`iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q (iteratedIdentityPower (R e) e p x)))`. -/
theorem iteratedIdentityPower_fourFactor_comp_mem_comm_and_contraction
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b d e : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (he : 0 < e)
    (hr : ∀ c, 0 < c → Resolves A (R c) c)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ c, 0 < c → ∀ z : A.domain, R c (A z + c • (z : H)) = (z : H))
    (n r s q p : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A n) :
    iteratedIdentityPower (R a) a r
      (iteratedIdentityPower (R b) b s
        (iteratedIdentityPower (R d) d q (iteratedIdentityPower (R e) e p x))) ∈
      operatorPowerDomain A n ∧
    iteratedOperatorPower A n
      (iteratedIdentityPower (R a) a r
        (iteratedIdentityPower (R b) b s
          (iteratedIdentityPower (R d) d q (iteratedIdentityPower (R e) e p x)))) =
      iteratedIdentityPower (R a) a r
        (iteratedIdentityPower (R b) b s
          (iteratedIdentityPower (R d) d q
            (iteratedIdentityPower (R e) e p (iteratedOperatorPower A n x)))) ∧
    kthPowerGraphNormSq A n
      (iteratedIdentityPower (R a) a r
        (iteratedIdentityPower (R b) b s
          (iteratedIdentityPower (R d) d q (iteratedIdentityPower (R e) e p x)))) ≤
      kthPowerGraphNormSq A n x := by
  have hbde := iteratedIdentityPower_threeFactor_comp_mem_comm_and_contraction
    A R b d e hb hd he hr hp hl n s q p hx
  have habde :
      iteratedIdentityPower (R a) a r
        (iteratedIdentityPower (R b) b s
          (iteratedIdentityPower (R d) d q (iteratedIdentityPower (R e) e p x))) ∈
        operatorPowerDomain A n :=
    iteratedIdentityPower_maps_operatorPowerDomain_to_self A (R a) a (hr a ha) (hl a ha) n r hbde.1
  have hca :=
    iteratedOperatorPower_iteratedIdentityPower_comm A (R a) a (hr a ha) (hl a ha) n r hbde.1
  have hcontr_a := kthPowerGraphNormSq_iteratedIdentityPower_contraction
    A (R a) a ha (hr a ha) hp (hl a ha) n r hbde.1
  exact ⟨habde, by rw [hca, hbde.2.1], hcontr_a.trans hbde.2.2⟩

/-- Four-factor multi-order `(r, s, q, p)` Yosida composition defect rate bound on
`operatorPowerDomain A (n + 1)`:
`‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r (iteratedIdentityPower (R b) b s (iteratedIdentityPower (R d) d q (iteratedIdentityPower (R e) e p x))) - x)‖ ≤ ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖`. -/
theorem iteratedOperatorPower_iteratedIdentityPower_fourFactor_defect_rate_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b d e : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (he : 0 < e)
    (hr : ∀ c, 0 < c → Resolves A (R c) c)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ c, 0 < c → ∀ z : A.domain, R c (A z + c • (z : H)) = (z : H))
    (n r s q p : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    ‖iteratedOperatorPower A n
      (iteratedIdentityPower (R a) a r
        (iteratedIdentityPower (R b) b s
          (iteratedIdentityPower (R d) d q (iteratedIdentityPower (R e) e p x))) - x)‖ ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) *
        ‖iteratedOperatorPower A (n + 1) x‖ := by
  have hxn : x ∈ operatorPowerDomain A n :=
    operatorPowerDomain_le_of_le A (Nat.le_succ n) hx
  have h4 := iteratedIdentityPower_fourFactor_comp_mem_comm_and_contraction
    A R a b d e ha hb hd he hr hp hl n r s q p hxn
  have h3_succ := iteratedIdentityPower_threeFactor_comp_mem_comm_and_contraction
    A R b d e hb hd he hr hp hl (n + 1) s q p hx
  have h3_n := iteratedIdentityPower_threeFactor_comp_mem_comm_and_contraction
    A R b d e hb hd he hr hp hl n s q p hxn
  let z := iteratedIdentityPower (R b) b s
    (iteratedIdentityPower (R d) d q (iteratedIdentityPower (R e) e p x))
  have hsplit :
      iteratedIdentityPower (R a) a r z - x =
        (iteratedIdentityPower (R a) a r z - z) + (z - x) := by abel
  have hsub1 := (iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain
    A n h4.1 h3_n.1).2
  have hadd := (iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain
    A n ((operatorPowerDomain A n).sub_mem h4.1 h3_n.1)
      ((operatorPowerDomain A n).sub_mem h3_n.1 hxn)).1
  rw [hsplit, hadd]
  have htri := norm_add_le
    (iteratedOperatorPower A n (iteratedIdentityPower (R a) a r z - z))
    (iteratedOperatorPower A n (z - x))
  have hbd3 := iteratedOperatorPower_iteratedIdentityPower_threeFactor_defect_rate_on_succ
    A R b d e hb hd he hr hp hl n s q p hx
  have hz_dom : iteratedOperatorPower A n z ∈ A.domain :=
    iteratedOperatorPower_mem_domain_of_mem_succ A n h3_succ.1
  have hca_z := iteratedOperatorPower_iteratedIdentityPower_comm
    A (R a) a (hr a ha) (hl a ha) n r h3_n.1
  have hba := iteratedIdentityPower_domain_rate_bound
    A (R a) a ha (hr a ha) hp (hl a ha) r ⟨iteratedOperatorPower A n z, hz_dom⟩
  have hAz :
      ‖A ⟨iteratedOperatorPower A n z, hz_dom⟩‖ ≤ ‖iteratedOperatorPower A (n + 1) x‖ := by
    have hsucc_z :
        A ⟨iteratedOperatorPower A n z, hz_dom⟩ = iteratedOperatorPower A (n + 1) z := by
      rw [iteratedOperatorPower_succ_apply, totalOperator_of_mem_domain A hz_dom]
    rw [hsucc_z, h3_succ.2.1]
    have hcb := iteratedIdentityPower_norm_le A (R b) b hb (hr b hb) hp s
      (iteratedIdentityPower (R d) d q
        (iteratedIdentityPower (R e) e p (iteratedOperatorPower A (n + 1) x)))
    have hcd := iteratedIdentityPower_norm_le A (R d) d hd (hr d hd) hp q
      (iteratedIdentityPower (R e) e p (iteratedOperatorPower A (n + 1) x))
    have hce := iteratedIdentityPower_norm_le A (R e) e he (hr e he) hp p
      (iteratedOperatorPower A (n + 1) x)
    exact hcb.trans (hcd.trans hce)
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
          ((s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) *
            ‖iteratedOperatorPower A (n + 1) x‖ :=
        add_le_add hba' hbd3
    _ = ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) *
          ‖iteratedOperatorPower A (n + 1) x‖ := by ring

/-- Squared `n`-th order graph-norm four-factor multi-order `(r, s, q, p)` Yosida
composition defect bound on `operatorPowerDomain A (n + 1)`. -/
theorem kthPowerGraphNormSq_iteratedIdentityPower_fourFactor_defect_bound_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b d e : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (he : 0 < e)
    (hr : ∀ c, 0 < c → Resolves A (R c) c)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ c, 0 < c → ∀ z : A.domain, R c (A z + c • (z : H)) = (z : H))
    (n r s q p : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    kthPowerGraphNormSq A n
      (iteratedIdentityPower (R a) a r
        (iteratedIdentityPower (R b) b s
          (iteratedIdentityPower (R d) d q (iteratedIdentityPower (R e) e p x))) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) ^ 2 *
        kthPowerGraphNormSq A (n + 1) x := by
  have h1 :
      kthPowerGraphNormSq A n
        (iteratedIdentityPower (R a) a r
          (iteratedIdentityPower (R b) b s
            (iteratedIdentityPower (R d) d q (iteratedIdentityPower (R e) e p x))) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) ^ 2 *
        (∑ j ∈ Finset.range (n + 1), ‖iteratedOperatorPower A (j + 1) x‖ ^ 2) := by
    unfold kthPowerGraphNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hxj : x ∈ operatorPowerDomain A (j + 1) :=
      operatorPowerDomain_le_of_le A (Nat.succ_le_succ hjn) hx
    have hbd := iteratedOperatorPower_iteratedIdentityPower_fourFactor_defect_rate_on_succ
      A R a b d e ha hb hd he hr hp hl j r s q p hxj
    have hsq :
        ‖iteratedOperatorPower A j
          (iteratedIdentityPower (R a) a r
            (iteratedIdentityPower (R b) b s
              (iteratedIdentityPower (R d) d q (iteratedIdentityPower (R e) e p x))) - x)‖ ^ 2 ≤
        (((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) *
          ‖iteratedOperatorPower A (j + 1) x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbd 2
    linarith [mul_pow ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹)
      ‖iteratedOperatorPower A (j + 1) x‖ 2]
  have h2 := mul_le_mul_of_nonneg_left
    (sum_succ_iteratedOperatorPower_sq_le_kthPowerGraphNormSq_succ A n x)
    (sq_nonneg ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹))
  exact h1.trans h2

end AbstractFourFactorMultiPowerYosida

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

/-- Four-factor multi-order `(r, s, q, p)` Yosida contraction and defect bound on
`staticPowerDomain ε hε h (n + 1)` for `T`. -/
theorem static_arbitraryOrder_fourFactor_yosida_package
    (a b d e : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (he : 0 < e)
    (n r s q p : ℕ) {x : Hilbert}
    (hx : x ∈ staticPowerDomain ε hε h (n + 1)) :
    kthPowerGraphNormSq T (n + 1)
      (iteratedIdentityPower (RT a) a r
        (iteratedIdentityPower (RT b) b s
          (iteratedIdentityPower (RT d) d q (iteratedIdentityPower (RT e) e p x)))) ≤
      kthPowerGraphNormSq T (n + 1) x ∧
    kthPowerGraphNormSq T n
      (iteratedIdentityPower (RT a) a r
        (iteratedIdentityPower (RT b) b s
          (iteratedIdentityPower (RT d) d q (iteratedIdentityPower (RT e) e p x))) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) ^ 2 *
        kthPowerGraphNormSq T (n + 1) x :=
  ⟨(iteratedIdentityPower_fourFactor_comp_mem_comm_and_contraction T RT a b d e ha hb_pos hd he
     (staticResolvent_resolves ε hε h hb hh)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh) (n + 1) r s q p hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_fourFactor_defect_bound_on_succ T RT a b d e ha hb_pos hd he
     (staticResolvent_resolves ε hε h hb hh)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh) n r s q p hx⟩

/-- Four-factor multi-order `(r, s, q, p)` Yosida contraction and defect bound on
`potentialPowerDomain ε hε h hh hb m g k (n + 1)` for `P`. -/
theorem potential_arbitraryOrder_fourFactor_yosida_package
    (a b d e : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (he : 0 < e)
    (n r s q p : ℕ) {x : Hilbert}
    (hx : x ∈ potentialPowerDomain ε hε h hh hb m g k (n + 1)) :
    kthPowerGraphNormSq P (n + 1)
      (iteratedIdentityPower (RP a) a r
        (iteratedIdentityPower (RP b) b s
          (iteratedIdentityPower (RP d) d q (iteratedIdentityPower (RP e) e p x)))) ≤
      kthPowerGraphNormSq P (n + 1) x ∧
    kthPowerGraphNormSq P n
      (iteratedIdentityPower (RP a) a r
        (iteratedIdentityPower (RP b) b s
          (iteratedIdentityPower (RP d) d q (iteratedIdentityPower (RP e) e p x))) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) ^ 2 *
        kthPowerGraphNormSq P (n + 1) x :=
  ⟨(iteratedIdentityPower_fourFactor_comp_mem_comm_and_contraction P RP a b d e ha hb_pos hd he
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k)
     (n + 1) r s q p hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_fourFactor_defect_bound_on_succ P RP a b d e ha hb_pos hd he
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k) n r s q p hx⟩

/-- Four-factor multi-order `(r, s, q, p)` Yosida contraction and defect bound on
`growingPowerDomain ε hε h hh hb m g k (n + 1)` for `G`. -/
theorem growing_arbitraryOrder_fourFactor_yosida_package
    (a b d e : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (he : 0 < e)
    (n r s q p : ℕ) {x : Hilbert}
    (hx : x ∈ growingPowerDomain ε hε h hh hb m g k (n + 1)) :
    kthPowerGraphNormSq G (n + 1)
      (iteratedIdentityPower (RG a) a r
        (iteratedIdentityPower (RG b) b s
          (iteratedIdentityPower (RG d) d q (iteratedIdentityPower (RG e) e p x)))) ≤
      kthPowerGraphNormSq G (n + 1) x ∧
    kthPowerGraphNormSq G n
      (iteratedIdentityPower (RG a) a r
        (iteratedIdentityPower (RG b) b s
          (iteratedIdentityPower (RG d) d q (iteratedIdentityPower (RG e) e p x))) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) ^ 2 *
        kthPowerGraphNormSq G (n + 1) x :=
  ⟨(iteratedIdentityPower_fourFactor_comp_mem_comm_and_contraction G RG a b d e ha hb_pos hd he
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) (n + 1) r s q p hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_fourFactor_defect_bound_on_succ G RG a b d e ha hb_pos hd he
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) n r s q p hx⟩

/-- Four-factor multi-order `(r, s, q, p)` Yosida contraction and defect bound on
`residualPowerDomain ε hε h hh hb m g k t (n + 1)` for `S t`. -/
theorem residual_arbitraryOrder_fourFactor_yosida_package
    (t a b d e : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (he : 0 < e)
    (n r s q p : ℕ) {x : Hilbert}
    (hx : x ∈ residualPowerDomain ε hε h hh hb m g k t (n + 1)) :
    kthPowerGraphNormSq (S t) (n + 1)
      (iteratedIdentityPower (RS t a) a r
        (iteratedIdentityPower (RS t b) b s
          (iteratedIdentityPower (RS t d) d q (iteratedIdentityPower (RS t e) e p x)))) ≤
      kthPowerGraphNormSq (S t) (n + 1) x ∧
    kthPowerGraphNormSq (S t) n
      (iteratedIdentityPower (RS t a) a r
        (iteratedIdentityPower (RS t b) b s
          (iteratedIdentityPower (RS t d) d q (iteratedIdentityPower (RS t e) e p x))) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) ^ 2 *
        kthPowerGraphNormSq (S t) (n + 1) x :=
  ⟨(iteratedIdentityPower_fourFactor_comp_mem_comm_and_contraction (S t) (RS t) a b d e ha hb_pos hd he
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t)
     (n + 1) r s q p hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_fourFactor_defect_bound_on_succ (S t) (RS t) a b d e ha hb_pos hd he
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t) n r s q p hx⟩

/-- Four-factor multi-order `(r, s, q, p)` Yosida contraction and defect bound on
`hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)` for `H t`. -/
theorem hamiltonian_arbitraryOrder_fourFactor_yosida_package
    (t a b d e : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (he : 0 < e)
    (n r s q p : ℕ) {x : Hilbert}
    (hx : x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)) :
    kthPowerGraphNormSq (H t) (n + 1)
      (iteratedIdentityPower (RH t a) a r
        (iteratedIdentityPower (RH t b) b s
          (iteratedIdentityPower (RH t d) d q (iteratedIdentityPower (RH t e) e p x)))) ≤
      kthPowerGraphNormSq (H t) (n + 1) x ∧
    kthPowerGraphNormSq (H t) n
      (iteratedIdentityPower (RH t a) a r
        (iteratedIdentityPower (RH t b) b s
          (iteratedIdentityPower (RH t d) d q (iteratedIdentityPower (RH t e) e p x))) - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) ^ 2 *
        kthPowerGraphNormSq (H t) (n + 1) x :=
  ⟨(iteratedIdentityPower_fourFactor_comp_mem_comm_and_contraction (H t) (RH t) a b d e ha hb_pos hd he
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t)
     (n + 1) r s q p hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_fourFactor_defect_bound_on_succ (H t) (RH t) a b d e ha hb_pos hd he
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) n r s q p hx⟩

/-- Master Five-Operator Arbitrary-Order Four-Factor Multi-Power `(r, s, q, p)` Yosida
Composition Defect Synthesis across `T`, `P`, `G`, `S(t)`, and `H(t)`. -/
theorem arbitraryOrder_fourFactor_multiPower_yosida_master_synthesis
    (t a b d e : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (he : 0 < e)
    (n r s q p : ℕ) {xT xP xG xS xH : Hilbert}
    (hxT : xT ∈ staticPowerDomain ε hε h (n + 1))
    (hxP : xP ∈ potentialPowerDomain ε hε h hh hb m g k (n + 1))
    (hxG : xG ∈ growingPowerDomain ε hε h hh hb m g k (n + 1))
    (hxS : xS ∈ residualPowerDomain ε hε h hh hb m g k t (n + 1))
    (hxH : xH ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)) :
    kthPowerGraphNormSq T n
      (iteratedIdentityPower (RT a) a r
        (iteratedIdentityPower (RT b) b s
          (iteratedIdentityPower (RT d) d q (iteratedIdentityPower (RT e) e p xT))) - xT) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) ^ 2 *
        kthPowerGraphNormSq T (n + 1) xT ∧
    kthPowerGraphNormSq P n
      (iteratedIdentityPower (RP a) a r
        (iteratedIdentityPower (RP b) b s
          (iteratedIdentityPower (RP d) d q (iteratedIdentityPower (RP e) e p xP))) - xP) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) ^ 2 *
        kthPowerGraphNormSq P (n + 1) xP ∧
    kthPowerGraphNormSq G n
      (iteratedIdentityPower (RG a) a r
        (iteratedIdentityPower (RG b) b s
          (iteratedIdentityPower (RG d) d q (iteratedIdentityPower (RG e) e p xG))) - xG) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) ^ 2 *
        kthPowerGraphNormSq G (n + 1) xG ∧
    kthPowerGraphNormSq (S t) n
      (iteratedIdentityPower (RS t a) a r
        (iteratedIdentityPower (RS t b) b s
          (iteratedIdentityPower (RS t d) d q (iteratedIdentityPower (RS t e) e p xS))) - xS) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) ^ 2 *
        kthPowerGraphNormSq (S t) (n + 1) xS ∧
    kthPowerGraphNormSq (H t) n
      (iteratedIdentityPower (RH t a) a r
        (iteratedIdentityPower (RH t b) b s
          (iteratedIdentityPower (RH t d) d q (iteratedIdentityPower (RH t e) e p xH))) - xH) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹) ^ 2 *
        kthPowerGraphNormSq (H t) (n + 1) xH :=
  ⟨(static_arbitraryOrder_fourFactor_yosida_package ε hε h hh hb a b d e ha hb_pos hd he n r s q p hxT).2,
   (potential_arbitraryOrder_fourFactor_yosida_package ε hε h hh hb m g k a b d e ha hb_pos hd he n r s q p hxP).2,
   (growing_arbitraryOrder_fourFactor_yosida_package ε hε h hh hb m g k a b d e ha hb_pos hd he n r s q p hxG).2,
   (residual_arbitraryOrder_fourFactor_yosida_package ε hε h hh hb m g k t a b d e ha hb_pos hd he n r s q p hxS).2,
   (hamiltonian_arbitraryOrder_fourFactor_yosida_package ε hε h hh hb m g k t a b d e ha hb_pos hd he n r s q p hxH).2⟩

#print axioms iteratedIdentityPower_fourFactor_comp_mem_comm_and_contraction
#print axioms iteratedOperatorPower_iteratedIdentityPower_fourFactor_defect_rate_on_succ
#print axioms kthPowerGraphNormSq_iteratedIdentityPower_fourFactor_defect_bound_on_succ
#print axioms static_arbitraryOrder_fourFactor_yosida_package
#print axioms potential_arbitraryOrder_fourFactor_yosida_package
#print axioms growing_arbitraryOrder_fourFactor_yosida_package
#print axioms residual_arbitraryOrder_fourFactor_yosida_package
#print axioms hamiltonian_arbitraryOrder_fourFactor_yosida_package
#print axioms arbitraryOrder_fourFactor_multiPower_yosida_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderFourFactorMultiPowerYosidaComposition
