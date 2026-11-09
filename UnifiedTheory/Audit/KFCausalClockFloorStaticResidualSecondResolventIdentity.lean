/- Exact Second Resolvent Identities and Multi-Channel Norm Bounds connecting
the Static Hamiltonian resolvent R_T(a) = (T + a)⁻¹, the Potential Hamiltonian
resolvent R_P(a) = (P + a)⁻¹, and the Residual Hamiltonian resolvent
R_{S(t)}(a) = (S(t) + a)⁻¹ for all real couplings m, g, k ∈ ℝ, physical times
t ∈ ℝ, and positive shifts a > 0:
1. Establishes the complete operator, static-root form (T_stat), and half-clock
   (clockHalf) resolvent calculus for the maximal static operator T and its
   shifted resolvent R_T(a).
2. Proves the exact operator decompositions on Dom(S(t)) ∩ Dom(P) = Dom(S(t)) ∩ Dom(T):
   S(t) x = T x + exp(2t) • P x,
   T x = S(t) x - exp(2t) • P x,
   P x = exp(-2t) • (S(t) x - T x).
3. Deduces the exact Static-Residual Second Resolvent Identity for every state
   f : Hilbert with R_{S(t)}(a) f ∈ Dom(P) (equivalently R_{S(t)}(a) f ∈ Dom(T)):
   R_T(a) f - R_{S(t)}(a) f = exp(2t) • R_T(a) (P (R_{S(t)}(a) f)),
   together with Hilbert, static-operator, static-root form (T_stat), and
   half-clock (clockHalf) norm bounds, plus the dual Potential-Residual Second
   Resolvent Identity at t = 0:
   R_P(a) f - R_{S(0)}(a) f = R_P(a) (T (R_{S(0)}(a) f)). -/
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResidualSecondResolventIdentity
import UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialSecondResolventIdentity
import UnifiedTheory.Audit.KFCausalClockFloorStaticClockCore
import UnifiedTheory.Audit.KFCausalClockFloorResidualStaticPotentialDecomposition
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalThreeOperatorDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticResidualSecondResolventIdentity
noncomputable section
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (static_root_subset_clockHalf_domain static_root_clockHalf_norm_sq_le)
open KFCausalClockFloorResidualStaticPotentialDecomposition
  (static_graph_of_residual potential_graph_of_residual)
open KFCausalClockFloorPotentialResolventRadialRegularity
  (potential_resolvent_norm_le)
open KFCausalClockFloorGrowingPotentialSecondResolventIdentity
  (potential_resolvent_mem_potential_domain potential_resolvent_left_inverse
    potential_resolvent_operator_norm_le
    potential_resolvent_mem_potentialForm_domain
    potential_resolvent_potentialForm_norm_sq_le)
open KFCausalClockFloorHamiltonianResidualSecondResolventIdentity
  (residual_resolvent_mem_residual_domain residual_resolvent_equation
    residual_resolvent_left_inverse)

private theorem left_inverse_of_eq
    (A B : Hilbert →ₗ.[ℂ] Hilbert) (R : Hilbert →L[ℂ] Hilbert) (a : ℝ)
    (hAB : A = B)
    (hlinv : ∀ x : A.domain, R (A x + a • (x : Hilbert)) = (x : Hilbert))
    (x : B.domain) :
    R (B x + a • (x : Hilbert)) = (x : Hilbert) := by
  subst hAB
  exact hlinv x

private theorem accretive_resolvent_energy_split {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : KFCausalPositiveResolventBounds.Resolves A R a)
    (hp : ∀ x : A.domain, 0 ≤ (inner ℂ (A x) (x : H)).re) (f : H) :
    ‖A (KFCausalPositiveResolventBounds.point A R a hr f)‖ ^ 2 + a ^ 2 * ‖R f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  let x := KFCausalPositiveResolventBounds.point A R a hr f
  have hv := KFCausalPositiveResolventBounds.point_value A R a hr f
  have hsum : A x + (a : ℂ) • R f = f := by
    rw [hv, Complex.coe_smul, sub_add_cancel]
  have hexp : ‖A x + (a : ℂ) • R f‖ ^ 2 =
      ‖A x‖ ^ 2 + 2 * (inner ℂ (A x) ((a : ℂ) • R f)).re + ‖(a : ℂ) • R f‖ ^ 2 :=
    norm_add_sq (𝕜 := ℂ) (A x) ((a : ℂ) • R f)
  have hi : (inner ℂ (A x) ((a : ℂ) • R f)).re = a * (inner ℂ (A x) (x : H)).re := by
    change (inner ℂ (A x) ((a : ℂ) • (x : H))).re = a * (inner ℂ (A x) (x : H)).re
    rw [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hn : ‖(a : ℂ) • R f‖ ^ 2 = a ^ 2 * ‖R f‖ ^ 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, mul_pow]
  have hpos : 0 ≤ 2 * (a * (inner ℂ (A x) (x : H)).re) :=
    mul_nonneg zero_le_two (mul_nonneg ha.le (hp x))
  rw [hsum, hi, hn] at hexp
  linarith

private theorem resolvent_pairing_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : KFCausalPositiveResolventBounds.Resolves A R a)
    (hp : ∀ x : A.domain, 0 ≤ (inner ℂ (A x) (x : H)).re) (f : H) :
    (inner ℂ (A (KFCausalPositiveResolventBounds.point A R a hr f)) (R f)).re +
      a * ‖R f‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 := by
  have hv := KFCausalPositiveResolventBounds.point_value A R a hr f
  have heq : (inner ℂ (A (KFCausalPositiveResolventBounds.point A R a hr f)) (R f)).re +
      a * ‖R f‖ ^ 2 = (inner ℂ f (R f)).re := by
    rw [hv, inner_sub_left, inner_smul_left_eq_smul,
      KFCausalShiftedForm.complex_inner_square (R f)]
    simp only [Complex.sub_re, Complex.real_smul, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [heq]
  have hi : (inner ℂ f (R f)).re ≤ ‖f‖ * ‖R f‖ := re_inner_le_norm (𝕜 := ℂ) f (R f)
  have hnorm := KFCausalPositiveResolventBounds.resolvent_apply_norm_bound A R a ha hr hp f
  have hmul : ‖f‖ * ‖R f‖ ≤ ‖f‖ * (a⁻¹ * ‖f‖) :=
    mul_le_mul_of_nonneg_left hnorm (norm_nonneg f)
  linarith [show ‖f‖ * (a⁻¹ * ‖f‖) = a⁻¹ * ‖f‖ ^ 2 by ring]

private theorem subst_energy_le {e s b c : ℝ} (he : e = s) (hp : e + b ≤ c) : s + b ≤ c := by
  rw [← he]
  exact hp

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k t : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => KFCausalClockFloorStaticClockCore.resolvent ε hε h hh hw m g k 0
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k

/-! ### 1. Static Resolvent Operator, Form-Energy, and Half-Clock Calculus -/

theorem static_resolves (a : ℝ) (ha : 0 < a) :
    KFCausalPositiveResolventBounds.Resolves T (RT a) a :=
  (congrArg (fun A : Hilbert →ₗ.[ℂ] Hilbert =>
    KFCausalPositiveResolventBounds.Resolves A (RT a) a)
    (KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hw m g k 0)).mp
    (KFCausalClockFloorStaticClockCore.resolves ε hε h hh hw m g k 0 a ha)

def staticResolventPoint (a : ℝ) (ha : 0 < a) (f : Hilbert) : (T).domain :=
  KFCausalPositiveResolventBounds.point T (RT a) a
    (static_resolves ε hε h hh hb m g k a ha) f

theorem static_resolvent_mem_static_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RT a f ∈ (T).domain :=
  (staticResolventPoint ε hε h hh hb m g k a ha f).property

theorem static_resolvent_equation (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    T ⟨RT a f, static_resolvent_mem_static_domain ε hε h hh hb m g k a ha f⟩ =
      f - a • RT a f :=
  KFCausalPositiveResolventBounds.point_value T (RT a) a
    (static_resolves ε hε h hh hb m g k a ha) f

theorem static_resolvent_shifted_eq (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    T ⟨RT a f, static_resolvent_mem_static_domain ε hε h hh hb m g k a ha f⟩ +
      (a : ℂ) • RT a f = f := by
  rw [static_resolvent_equation ε hε h hh hb m g k a ha f, Complex.coe_smul, sub_add_cancel]

theorem static_resolvent_left_inverse (a : ℝ) (ha : 0 < a) (x : (T).domain) :
    RT a (T x + a • (x : Hilbert)) = (x : Hilbert) :=
  left_inverse_of_eq
    (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw m g k 0) T (RT a) a
    (KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hw m g k 0)
    (KFCausalClockFloorStaticClockCore.left_inverse ε hε h hh hw m g k 0 a ha) x

theorem static_form_energy_eq_staticRoot (x : (T).domain) :
    (inner ℂ (T x) (x : Hilbert)).re =
      ‖Tstat ⟨(x : Hilbert), KFCausalClockFloorStaticOperator.root_domain ε hε h x⟩‖ ^ 2 := by
  let rx : (Tstat).domain := ⟨(x : Hilbert), KFCausalClockFloorStaticOperator.root_domain ε hε h x⟩
  have hp := KFCausalClockFloorStaticOperator.root_pairing ε hε h x rx
  have hre : (inner ℂ (Tstat rx) (Tstat rx)).re = (inner ℂ (x : Hilbert) (T x)).re :=
    congrArg Complex.re hp
  have hsq : (inner ℂ (Tstat rx) (Tstat rx)).re = ‖Tstat rx‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (Tstat rx)
  have hsymm : (inner ℂ (x : Hilbert) (T x)).re = (inner ℂ (T x) (x : Hilbert)).re :=
    inner_re_symm (𝕜 := ℂ) (x : Hilbert) (T x)
  exact hsymm.symm.trans (hre.symm.trans hsq)

theorem static_operator_positive (x : (T).domain) :
    0 ≤ (inner ℂ (T x) (x : Hilbert)).re := by
  rw [static_form_energy_eq_staticRoot ε hε h x]
  exact sq_nonneg _

theorem static_resolvent_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖RT a f‖ ≤ a⁻¹ * ‖f‖ :=
  KFCausalPositiveResolventBounds.resolvent_apply_norm_bound T (RT a) a ha
    (static_resolves ε hε h hh hb m g k a ha)
    (static_operator_positive ε hε h) f

theorem static_resolvent_operator_norm_sq_add_scaled_sq_le
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖T ⟨RT a f, static_resolvent_mem_static_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 +
      a ^ 2 * ‖RT a f‖ ^ 2 ≤ ‖f‖ ^ 2 :=
  accretive_resolvent_energy_split T (RT a) a ha
    (static_resolves ε hε h hh hb m g k a ha)
    (static_operator_positive ε hε h) f

theorem static_resolvent_operator_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖T ⟨RT a f, static_resolvent_mem_static_domain ε hε h hh hb m g k a ha f⟩‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h1 := static_resolvent_operator_norm_sq_add_scaled_sq_le ε hε h hh hb m g k a ha f
  have h2 : 0 ≤ a ^ 2 * ‖RT a f‖ ^ 2 := by positivity
  linarith

theorem static_resolvent_mem_staticRoot_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RT a f ∈ (Tstat).domain :=
  KFCausalClockFloorStaticOperator.root_domain ε hε h
    (staticResolventPoint ε hε h hh hb m g k a ha f)

theorem static_resolvent_staticRoot_energy_add_scaled_sq_le
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tstat ⟨RT a f, static_resolvent_mem_staticRoot_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 +
      a * ‖RT a f‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 :=
  subst_energy_le
    (static_form_energy_eq_staticRoot ε hε h
      (staticResolventPoint ε hε h hh hb m g k a ha f))
    (resolvent_pairing_le T (RT a) a ha
      (static_resolves ε hε h hh hb m g k a ha)
      (static_operator_positive ε hε h) f)

theorem static_resolvent_staticRoot_norm_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tstat ⟨RT a f, static_resolvent_mem_staticRoot_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 ≤
      a⁻¹ * ‖f‖ ^ 2 := by
  have h1 := static_resolvent_staticRoot_energy_add_scaled_sq_le ε hε h hh hb m g k a ha f
  have h2 : 0 ≤ a * ‖RT a f‖ ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  linarith

theorem static_resolvent_mem_clockHalf_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RT a f ∈ (clockHalf ε).domain :=
  static_root_subset_clockHalf_domain ε hε h (RT a f)
    (static_resolvent_mem_staticRoot_domain ε hε h hh hb m g k a ha f)

theorem static_resolvent_clockHalf_norm_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖clockHalf ε ⟨RT a f, static_resolvent_mem_clockHalf_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 ≤
      2 * a⁻¹ * ‖f‖ ^ 2 := by
  have h1 := static_root_clockHalf_norm_sq_le ε hε h (RT a f)
    (static_resolvent_mem_staticRoot_domain ε hε h hh hb m g k a ha f)
  have h2 := static_resolvent_staticRoot_norm_sq_le ε hε h hh hb m g k a ha f
  linarith

/-! ### 2. Exact Residual-Static-Potential Operator Decompositions -/

theorem residual_potential_mem_static_domain (x : Hilbert)
    (hs : x ∈ (S t).domain) (hp : x ∈ (P).domain) :
    x ∈ (T).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (static_graph_of_residual ε hε h hh hw m g k t x (S t ⟨x, hs⟩) (P ⟨x, hp⟩)
      ((S t).mem_graph ⟨x, hs⟩) ((P).mem_graph ⟨x, hp⟩))

theorem static_apply_on_residual_potential (x : Hilbert)
    (hs : x ∈ (S t).domain) (hp : x ∈ (P).domain) :
    T ⟨x, residual_potential_mem_static_domain ε hε h hh hb m g k t x hs hp⟩ =
      S t ⟨x, hs⟩ - (Real.exp (2 * t) : ℂ) • P ⟨x, hp⟩ :=
  (T).mem_graph_snd_inj'
    ((T).mem_graph ⟨x, residual_potential_mem_static_domain ε hε h hh hb m g k t x hs hp⟩)
    (static_graph_of_residual ε hε h hh hw m g k t x (S t ⟨x, hs⟩) (P ⟨x, hp⟩)
      ((S t).mem_graph ⟨x, hs⟩) ((P).mem_graph ⟨x, hp⟩)) rfl

theorem residual_eq_static_add_scaled_potential (x : Hilbert)
    (hs : x ∈ (S t).domain) (hp : x ∈ (P).domain) :
    S t ⟨x, hs⟩ =
      T ⟨x, residual_potential_mem_static_domain ε hε h hh hb m g k t x hs hp⟩ +
        (Real.exp (2 * t) : ℂ) • P ⟨x, hp⟩ := by
  rw [static_apply_on_residual_potential ε hε h hh hb m g k t x hs hp, sub_add_cancel]

theorem residual_static_mem_potential_domain (x : Hilbert)
    (hs : x ∈ (S t).domain) (ht : x ∈ (T).domain) :
    x ∈ (P).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (potential_graph_of_residual ε hε h hh hw m g k t x (S t ⟨x, hs⟩) (T ⟨x, ht⟩)
      ((S t).mem_graph ⟨x, hs⟩) ((T).mem_graph ⟨x, ht⟩))

theorem potential_apply_on_residual_static (x : Hilbert)
    (hs : x ∈ (S t).domain) (ht : x ∈ (T).domain) :
    P ⟨x, residual_static_mem_potential_domain ε hε h hh hb m g k t x hs ht⟩ =
      (Real.exp (-2 * t) : ℂ) • (S t ⟨x, hs⟩ - T ⟨x, ht⟩) :=
  (P).mem_graph_snd_inj'
    ((P).mem_graph ⟨x, residual_static_mem_potential_domain ε hε h hh hb m g k t x hs ht⟩)
    (potential_graph_of_residual ε hε h hh hw m g k t x (S t ⟨x, hs⟩) (T ⟨x, ht⟩)
      ((S t).mem_graph ⟨x, hs⟩) ((T).mem_graph ⟨x, ht⟩)) rfl

theorem static_resolvent_on_shifted_residual_sub_eq
    (a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hs : x ∈ (S t).domain) (hp : x ∈ (P).domain) :
    RT a (S t ⟨x, hs⟩ + a • x) - x =
      (Real.exp (2 * t) : ℂ) • RT a (P ⟨x, hp⟩) := by
  let ht := residual_potential_mem_static_domain ε hε h hh hb m g k t x hs hp
  have hsum : S t ⟨x, hs⟩ + a • x =
      (T ⟨x, ht⟩ + a • x) + (Real.exp (2 * t) : ℂ) • P ⟨x, hp⟩ := by
    rw [residual_eq_static_add_scaled_potential ε hε h hh hb m g k t x hs hp]
    abel
  have hlinv := static_resolvent_left_inverse ε hε h hh hb m g k a ha ⟨x, ht⟩
  change RT a (T ⟨x, ht⟩ + a • x) = x at hlinv
  rw [hsum, map_add, hlinv, map_smul, add_sub_cancel_left]

/-! ### 3. Exact Static-Residual Second Resolvent Identity and Multi-Channel Bounds -/

theorem residual_resolvent_mem_static_of_potential
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RS t a f ∈ (P).domain) :
    RS t a f ∈ (T).domain :=
  residual_potential_mem_static_domain ε hε h hh hb m g k t (RS t a f)
    (residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f) hp

theorem residual_resolvent_shifted_static_eq
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RS t a f ∈ (P).domain) :
    T ⟨RS t a f, residual_resolvent_mem_static_of_potential ε hε h hh hb m g k t a ha f hp⟩ +
      (a : ℂ) • RS t a f =
      f - (Real.exp (2 * t) : ℂ) • P ⟨RS t a f, hp⟩ := by
  rw [static_apply_on_residual_potential ε hε h hh hb m g k t (RS t a f)
      (residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f) hp,
    residual_resolvent_equation ε hε h hh hb m g k t a ha f, ← Complex.coe_smul]
  abel

theorem residual_resolvent_shifted_static_eq_real
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RS t a f ∈ (P).domain) :
    T ⟨RS t a f, residual_resolvent_mem_static_of_potential ε hε h hh hb m g k t a ha f hp⟩ +
      a • RS t a f =
      f - (Real.exp (2 * t) : ℂ) • P ⟨RS t a f, hp⟩ := by
  rw [← Complex.coe_smul]
  exact residual_resolvent_shifted_static_eq ε hε h hh hb m g k t a ha f hp

theorem residual_resolvent_eq_static_resolvent_shifted_source
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RS t a f ∈ (P).domain) :
    RS t a f = RT a (f - (Real.exp (2 * t) : ℂ) • P ⟨RS t a f, hp⟩) := by
  have hlinv := static_resolvent_left_inverse ε hε h hh hb m g k a ha
    ⟨RS t a f, residual_resolvent_mem_static_of_potential ε hε h hh hb m g k t a ha f hp⟩
  change RT a
    (T ⟨RS t a f, residual_resolvent_mem_static_of_potential ε hε h hh hb m g k t a ha f hp⟩ +
      a • RS t a f) = RS t a f at hlinv
  rw [residual_resolvent_shifted_static_eq_real ε hε h hh hb m g k t a ha f hp] at hlinv
  exact hlinv.symm

theorem residual_resolvent_second_resolvent_identity
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RS t a f ∈ (P).domain) :
    RS t a f = RT a f - (Real.exp (2 * t) : ℂ) • RT a (P ⟨RS t a f, hp⟩) :=
  (residual_resolvent_eq_static_resolvent_shifted_source ε hε h hh hb m g k t a ha f hp).trans
    ((map_sub (RT a) f _).trans
      (congrArg (fun u : Hilbert => RT a f - u)
        (map_smul (RT a) (Real.exp (2 * t) : ℂ) (P ⟨RS t a f, hp⟩))))

theorem static_sub_residual_resolvent_eq
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RS t a f ∈ (P).domain) :
    RT a f - RS t a f = (Real.exp (2 * t) : ℂ) • RT a (P ⟨RS t a f, hp⟩) :=
  (congrArg (fun u : Hilbert => RT a f - u)
    (residual_resolvent_second_resolvent_identity ε hε h hh hb m g k t a ha f hp)).trans
    (sub_sub_cancel _ _)

theorem static_sub_residual_resolvent_mem_static_domain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RS t a f ∈ (P).domain) :
    RT a f - RS t a f ∈ (T).domain :=
  (T).domain.sub_mem
    (static_resolvent_mem_static_domain ε hε h hh hb m g k a ha f)
    (residual_resolvent_mem_static_of_potential ε hε h hh hb m g k t a ha f hp)

theorem static_on_static_sub_residual_resolvent_eq
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RS t a f ∈ (P).domain) :
    T ⟨RT a f, static_resolvent_mem_static_domain ε hε h hh hb m g k a ha f⟩ -
      T ⟨RS t a f, residual_resolvent_mem_static_of_potential ε hε h hh hb m g k t a ha f hp⟩ =
      (Real.exp (2 * t) : ℂ) •
        T ⟨RT a (P ⟨RS t a f, hp⟩),
          static_resolvent_mem_static_domain ε hε h hh hb m g k a ha (P ⟨RS t a f, hp⟩)⟩ := by
  let xT : (T).domain := ⟨RT a f, static_resolvent_mem_static_domain ε hε h hh hb m g k a ha f⟩
  let xS : (T).domain :=
    ⟨RS t a f, residual_resolvent_mem_static_of_potential ε hε h hh hb m g k t a ha f hp⟩
  let xP : (T).domain :=
    ⟨RT a (P ⟨RS t a f, hp⟩),
      static_resolvent_mem_static_domain ε hε h hh hb m g k a ha (P ⟨RS t a f, hp⟩)⟩
  have hsub : xT - xS = (Real.exp (2 * t) : ℂ) • xP :=
    Subtype.ext (static_sub_residual_resolvent_eq ε hε h hh hb m g k t a ha f hp)
  exact ((T).map_sub xT xS).symm.trans ((congrArg T hsub).trans ((T).map_smul _ xP))

theorem static_sub_residual_resolvent_norm_le_potential
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RS t a f ∈ (P).domain) :
    ‖RT a f - RS t a f‖ ≤ a⁻¹ * Real.exp (2 * t) * ‖P ⟨RS t a f, hp⟩‖ := by
  let pVec := P ⟨RS t a f, hp⟩
  have heq : ‖RT a f - RS t a f‖ = Real.exp (2 * t) * ‖RT a pVec‖ := by
    refine (congrArg norm (static_sub_residual_resolvent_eq ε hε h hh hb m g k t a ha f hp)).trans ?_
    change ‖(Real.exp (2 * t) : ℂ) • RT a pVec‖ = Real.exp (2 * t) * ‖RT a pVec‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (2 * t))]
  have hr := static_resolvent_norm_le ε hε h hh hb m g k a ha pVec
  calc
    ‖RT a f - RS t a f‖ = Real.exp (2 * t) * ‖RT a pVec‖ := heq
    _ ≤ Real.exp (2 * t) * (a⁻¹ * ‖pVec‖) :=
      mul_le_mul_of_nonneg_left hr (Real.exp_pos (2 * t)).le
    _ = a⁻¹ * Real.exp (2 * t) * ‖pVec‖ := by ring

theorem static_action_diff_norm_le_potential
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RS t a f ∈ (P).domain) :
    ‖T ⟨RT a f, static_resolvent_mem_static_domain ε hε h hh hb m g k a ha f⟩ -
      T ⟨RS t a f, residual_resolvent_mem_static_of_potential ε hε h hh hb m g k t a ha f hp⟩‖ ≤
      Real.exp (2 * t) * ‖P ⟨RS t a f, hp⟩‖ := by
  let pVec := P ⟨RS t a f, hp⟩
  let tP := T ⟨RT a pVec, static_resolvent_mem_static_domain ε hε h hh hb m g k a ha pVec⟩
  have heq : ‖T ⟨RT a f, static_resolvent_mem_static_domain ε hε h hh hb m g k a ha f⟩ -
      T ⟨RS t a f, residual_resolvent_mem_static_of_potential ε hε h hh hb m g k t a ha f hp⟩‖ =
      Real.exp (2 * t) * ‖tP‖ := by
    refine (congrArg norm
      (static_on_static_sub_residual_resolvent_eq ε hε h hh hb m g k t a ha f hp)).trans ?_
    change ‖(Real.exp (2 * t) : ℂ) • tP‖ = Real.exp (2 * t) * ‖tP‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (2 * t))]
  rw [heq]
  exact mul_le_mul_of_nonneg_left
    (static_resolvent_operator_norm_le ε hε h hh hb m g k a ha pVec)
    (Real.exp_pos (2 * t)).le

theorem static_sub_residual_resolvent_mem_staticRoot_domain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RS t a f ∈ (P).domain) :
    RT a f - RS t a f ∈ (Tstat).domain :=
  KFCausalClockFloorStaticOperator.root_domain ε hε h
    ⟨RT a f - RS t a f, static_sub_residual_resolvent_mem_static_domain ε hε h hh hb m g k t a ha f hp⟩

theorem static_sub_residual_resolvent_staticRoot_norm_sq_le_potential
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RS t a f ∈ (P).domain) :
    ‖Tstat ⟨RT a f - RS t a f,
      static_sub_residual_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f hp⟩‖ ^ 2 ≤
      a⁻¹ * Real.exp (4 * t) * ‖P ⟨RS t a f, hp⟩‖ ^ 2 := by
  let pVec := P ⟨RS t a f, hp⟩
  let xDiff : (Tstat).domain :=
    ⟨RT a f - RS t a f,
      static_sub_residual_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f hp⟩
  let xP : (Tstat).domain :=
    ⟨RT a pVec, static_resolvent_mem_staticRoot_domain ε hε h hh hb m g k a ha pVec⟩
  have hsub : xDiff = (Real.exp (2 * t) : ℂ) • xP :=
    Subtype.ext (static_sub_residual_resolvent_eq ε hε h hh hb m g k t a ha f hp)
  have hmap : Tstat xDiff = (Real.exp (2 * t) : ℂ) • Tstat xP :=
    (congrArg Tstat hsub).trans ((Tstat).map_smul _ xP)
  have he : Real.exp (2 * t) ^ 2 = Real.exp (4 * t) := by
    rw [sq, ← Real.exp_add, show 2 * t + 2 * t = 4 * t by ring]
  have hnorm : ‖Tstat xDiff‖ ^ 2 = Real.exp (4 * t) * ‖Tstat xP‖ ^ 2 := by
    rw [hmap, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos (2 * t)), mul_pow, he]
  have hbP := static_resolvent_staticRoot_norm_sq_le ε hε h hh hb m g k a ha pVec
  have hmul := mul_le_mul_of_nonneg_left hbP (Real.exp_pos (4 * t)).le
  change ‖Tstat xDiff‖ ^ 2 ≤ a⁻¹ * Real.exp (4 * t) * ‖pVec‖ ^ 2
  rw [hnorm]
  linarith

theorem static_sub_residual_resolvent_mem_clockHalf_domain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RS t a f ∈ (P).domain) :
    RT a f - RS t a f ∈ (clockHalf ε).domain :=
  static_root_subset_clockHalf_domain ε hε h (RT a f - RS t a f)
    (static_sub_residual_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f hp)

theorem static_sub_residual_resolvent_clockHalf_norm_sq_le_potential
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RS t a f ∈ (P).domain) :
    ‖clockHalf ε ⟨RT a f - RS t a f,
      static_sub_residual_resolvent_mem_clockHalf_domain ε hε h hh hb m g k t a ha f hp⟩‖ ^ 2 ≤
      2 * a⁻¹ * Real.exp (4 * t) * ‖P ⟨RS t a f, hp⟩‖ ^ 2 := by
  have h1 := static_root_clockHalf_norm_sq_le ε hε h (RT a f - RS t a f)
    (static_sub_residual_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f hp)
  have h2 := static_sub_residual_resolvent_staticRoot_norm_sq_le_potential
    ε hε h hh hb m g k t a ha f hp
  linarith

theorem potential_sub_residual_zero_resolvent_eq
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (ht : RS 0 a f ∈ (T).domain) :
    RP a f - RS 0 a f = RP a (T ⟨RS 0 a f, ht⟩) := by
  have hs0 := residual_resolvent_mem_residual_domain ε hε h hh hb m g k 0 a ha f
  let hp0 := residual_static_mem_potential_domain ε hε h hh hb m g k 0 (RS 0 a f) hs0 ht
  have hp_eq := potential_apply_on_residual_static ε hε h hh hb m g k 0 (RS 0 a f) hs0 ht
  have hexp0 : (Real.exp (-2 * (0 : ℝ)) : ℂ) = 1 := by
    rw [mul_zero, Real.exp_zero, Complex.ofReal_one]
  change P ⟨RS 0 a f, hp0⟩ = (Real.exp (-2 * (0 : ℝ)) : ℂ) • (S 0 ⟨RS 0 a f, hs0⟩ - T ⟨RS 0 a f, ht⟩) at hp_eq
  rw [hexp0, one_smul] at hp_eq
  have hshift : P ⟨RS 0 a f, hp0⟩ + a • RS 0 a f = f - T ⟨RS 0 a f, ht⟩ := by
    rw [hp_eq, residual_resolvent_equation ε hε h hh hb m g k 0 a ha f]
    abel
  have hlinv := potential_resolvent_left_inverse ε hε h hh hb m g k a ha ⟨RS 0 a f, hp0⟩
  change RP a (P ⟨RS 0 a f, hp0⟩ + a • RS 0 a f) = RS 0 a f at hlinv
  rw [hshift, map_sub] at hlinv
  exact (congrArg (fun u : Hilbert => RP a f - u) hlinv.symm).trans (sub_sub_cancel _ _)

#print axioms static_resolves
#print axioms static_resolvent_mem_static_domain
#print axioms static_resolvent_equation
#print axioms static_resolvent_shifted_eq
#print axioms static_resolvent_left_inverse
#print axioms static_form_energy_eq_staticRoot
#print axioms static_operator_positive
#print axioms static_resolvent_norm_le
#print axioms static_resolvent_operator_norm_sq_add_scaled_sq_le
#print axioms static_resolvent_operator_norm_le
#print axioms static_resolvent_mem_staticRoot_domain
#print axioms static_resolvent_staticRoot_energy_add_scaled_sq_le
#print axioms static_resolvent_staticRoot_norm_sq_le
#print axioms static_resolvent_mem_clockHalf_domain
#print axioms static_resolvent_clockHalf_norm_sq_le
#print axioms residual_potential_mem_static_domain
#print axioms static_apply_on_residual_potential
#print axioms residual_eq_static_add_scaled_potential
#print axioms residual_static_mem_potential_domain
#print axioms potential_apply_on_residual_static
#print axioms static_resolvent_on_shifted_residual_sub_eq
#print axioms residual_resolvent_mem_static_of_potential
#print axioms residual_resolvent_shifted_static_eq
#print axioms residual_resolvent_shifted_static_eq_real
#print axioms residual_resolvent_eq_static_resolvent_shifted_source
#print axioms residual_resolvent_second_resolvent_identity
#print axioms static_sub_residual_resolvent_eq
#print axioms static_sub_residual_resolvent_mem_static_domain
#print axioms static_on_static_sub_residual_resolvent_eq
#print axioms static_sub_residual_resolvent_norm_le_potential
#print axioms static_action_diff_norm_le_potential
#print axioms static_sub_residual_resolvent_mem_staticRoot_domain
#print axioms static_sub_residual_resolvent_staticRoot_norm_sq_le_potential
#print axioms static_sub_residual_resolvent_mem_clockHalf_domain
#print axioms static_sub_residual_resolvent_clockHalf_norm_sq_le_potential
#print axioms potential_sub_residual_zero_resolvent_eq
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticResidualSecondResolventIdentity
