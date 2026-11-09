/- Unconditional Full-Hamiltonian Yosida Pairing Lower Bounds, Yosida-Root
Regularity, and 5-Way Three-Operator Resolvent Synthesis:
1. Establishes the radial Yosida lower bound on Dom(K):
   ‖M_N x‖² ≤ Re ⟨K x, M_N x⟩ and 0 ≤ Re ⟨K x, M_N x⟩,
   and combines H(t) x = exp(2t) • K x + S(t) x with the residual Yosida lower
   bound to prove the unconditional full-Hamiltonian Yosida pairing lower bounds
   on Dom(H(t)):
   exp(2t) ‖M_N x‖² - (h²/ε²) ‖x‖² ≤ Re ⟨H(t) x, M_N x⟩,
   -(h²/ε²) ‖x‖² ≤ Re ⟨H(t) x, M_N x⟩.
2. Deduces unconditional M_N and M_N^{1/2} norm bounds on every Hamiltonian
   resolvent state R_{H(t)}(a) f for all f : Hilbert and f ∈ Dom(K_root).
3. Proves the unconditional 5-way operator-domain equivalence for R_{H(t)}(a) f:
   R_{H(t)}(a) f ∈ Dom(P) ↔ R_{H(t)}(a) f ∈ Dom(T) ↔ R_{H(t)}(a) f ∈ Dom(G)
   ↔ R_{H(t)}(a) f ∈ commonOperatorDomain
   ↔ R_{S(t)}(a) (f - exp(2t) • K (R_{H(t)}(a) f)) ∈ Dom(P),
   together with the exact 3-operator decompositions and mutual norm bounds. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventGrowingDomain
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResidualSecondResolventIdentity
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeResolventContinuity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis
noncomputable section
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaSymbol (action)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOperator)
open KFCausalClockFloorRadialYosidaPairing (root_graph kinetic_pairing_lower)
open KFCausalClockFloorRadialResolventGrowingDomain
  (root_radial_pairing radial_domain_le_root_domain)
open KFCausalClockFloorUnconditionalThreeOperatorDecomposition
  (unconditional_three_operator_residual_graph
    unconditional_three_operator_hamiltonian_graph
    unconditional_static_growing_hamiltonian_graph
    hamiltonian_residual_common_domain_eq
    hamiltonian_growing_common_domain_eq
    hamiltonian_static_common_domain_eq)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain common_domain_subset_hamiltonian
    common_domain_subset_residual common_domain_subset_growing)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (unconditional_two_operator_growing_eval)
open KFCausalClockFloorResidualResolventRadialRootRegularity
  (yosidaRootAction yosidaRootAction_sq_inner yosidaRootAction_norm_sq_eq_inner
    yosidaRootAction_norm_le_rootOperator root_norm_of_uniform_bound
    residual_operator_yosida_pairing_lower)
open KFCausalClockFloorHamiltonianComponentResolventBounds
  (resolventPoint resolvent_mem_hamiltonian_domain resolvent_mem_radial_domain
    resolvent_mem_residual_domain resolvent_equation resolvent_operator_sum
    resolvent_hamiltonian_norm_le resolvent_norm_le)
open KFCausalClockFloorHamiltonianResidualSecondResolventIdentity
  (hamiltonian_resolvent_eq_residual_resolvent_shifted_source)

private theorem quadratic_bound (u v z e : ℝ) (hv : 0 ≤ v)
    (hz : 0 ≤ z) (he : 0 < e) (hq : e ^ 2 * u ^ 2 ≤ v * u + z ^ 2) :
    u ≤ v / e ^ 2 + z / e := by
  have hmul : (v / e) * (e * u) = v * u := by rw [← mul_assoc, div_mul_cancel₀ _ he.ne']
  have hs : (e * u) ^ 2 ≤ (v / e) * (e * u) + z ^ 2 := by rw [hmul]; nlinarith only [hq]
  have hn : e * u ≤ v / e + z := by
    have ha : 0 ≤ v / e := div_nonneg hv he.le
    by_contra hbad
    have hb := lt_of_not_ge hbad
    have hc : z < e * u := by linarith
    nlinarith [mul_nonneg ha (show 0 ≤ e * u - z by linarith)]
  have hd : u ≤ (v / e + z) / e := (le_div_iff₀ he).mpr (by simpa only [mul_comm u e] using hn)
  have heq : (v / e + z) / e = v / e ^ 2 + z / e := by ring
  exact hd.trans_eq heq

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "Kroot" => rootOperator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k

/-! ### 1. Radial and Full-Hamiltonian Yosida Pairing Lower Bounds -/

theorem radial_operator_yosida_pairing_lower (N : ℝ) (hN : 0 < N)
    (x : (K).domain) :
    ‖action ε hε h N hN (x : Hilbert)‖ ^ 2 ≤
      (inner ℂ (K x) (action ε hε h N hN (x : Hilbert))).re := by
  let hroot : (x : Hilbert) ∈ (Kroot).domain :=
    radial_domain_le_root_domain ε hε h (x : Hilbert) x.property
  let r : Hilbert := Kroot ⟨(x : Hilbert), hroot⟩
  have hrg : ((x : Hilbert), r) ∈ (Kroot).graph :=
    (Kroot).mem_graph ⟨(x : Hilbert), hroot⟩
  have hMg : (action ε hε h N hN (x : Hilbert), action ε hε h N hN r) ∈ (Kroot).graph :=
    root_graph ε hε h N hN (x : Hilbert) r hrg
  have hpair : inner ℂ r (action ε hε h N hN r) =
      inner ℂ (K x) (action ε hε h N hN (x : Hilbert)) :=
    root_radial_pairing ε hε h (x : Hilbert) (action ε hε h N hN (x : Hilbert))
      r (action ε hε h N hN r) (K x) hrg hMg ((K).mem_graph x)
  exact (kinetic_pairing_lower ε hε h N hN (x : Hilbert) r hrg).trans_eq
    (congrArg Complex.re hpair)

theorem radial_operator_yosida_pairing_nonneg (N : ℝ) (hN : 0 < N)
    (x : (K).domain) :
    0 ≤ (inner ℂ (K x) (action ε hε h N hN (x : Hilbert))).re :=
  (sq_nonneg _).trans (radial_operator_yosida_pairing_lower ε hε h N hN x)

theorem hamiltonian_operator_yosida_pairing_lower (N : ℝ) (hN : 0 < N) (t : ℝ)
    (x : (H t).domain) :
    Real.exp (2 * t) * ‖action ε hε h N hN (x : Hilbert)‖ ^ 2 -
      (h ^ 2 / ε ^ 2) * ‖(x : Hilbert)‖ ^ 2 ≤
      (inner ℂ (H t x) (action ε hε h N hN (x : Hilbert))).re := by
  let hk : (x : Hilbert) ∈ (K).domain :=
    KFCausalClockFloorHamiltonianRadialDomination.radial_domain ε hε h hh hb m g k t x
  let hs : (x : Hilbert) ∈ (S t).domain :=
    KFCausalClockFloorHamiltonianRadialSum.residual_domain ε hε h hh hb m g k t x
  have hsum : H t x =
      (Real.exp (2 * t) : ℂ) • K ⟨(x : Hilbert), hk⟩ + S t ⟨(x : Hilbert), hs⟩ := by
    rw [KFCausalClockFloorHamiltonianRadialSum.residual_output ε hε h hh hb m g k t x]
    exact (add_sub_cancel _ _).symm
  have hK := radial_operator_yosida_pairing_lower ε hε h N hN ⟨(x : Hilbert), hk⟩
  have hK_scaled := mul_le_mul_of_nonneg_left hK (Real.exp_pos (2 * t)).le
  have hS := residual_operator_yosida_pairing_lower ε hε h hh hb m g k N hN t ⟨(x : Hilbert), hs⟩
  have hre : (inner ℂ (H t x) (action ε hε h N hN (x : Hilbert))).re =
      Real.exp (2 * t) * (inner ℂ (K ⟨(x : Hilbert), hk⟩) (action ε hε h N hN (x : Hilbert))).re +
        (inner ℂ (S t ⟨(x : Hilbert), hs⟩) (action ε hε h N hN (x : Hilbert))).re := by
    rw [hsum, inner_add_left, inner_smul_left, Complex.conj_ofReal, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change -(h ^ 2 / ε ^ 2) * ‖(x : Hilbert)‖ ^ 2 ≤
    (inner ℂ (S t ⟨(x : Hilbert), hs⟩) (action ε hε h N hN (x : Hilbert))).re at hS
  change ‖action ε hε h N hN (x : Hilbert)‖ ^ 2 ≤
    (inner ℂ (K ⟨(x : Hilbert), hk⟩) (action ε hε h N hN (x : Hilbert))).re at hK
  linarith

theorem hamiltonian_operator_yosida_pairing_lower_weak (N : ℝ) (hN : 0 < N) (t : ℝ)
    (x : (H t).domain) :
    -(h ^ 2 / ε ^ 2) * ‖(x : Hilbert)‖ ^ 2 ≤
      (inner ℂ (H t x) (action ε hε h N hN (x : Hilbert))).re := by
  have h1 := hamiltonian_operator_yosida_pairing_lower ε hε h hh hb m g k N hN t x
  have h2 : 0 ≤ Real.exp (2 * t) * ‖action ε hε h N hN (x : Hilbert)‖ ^ 2 :=
    mul_nonneg (Real.exp_pos (2 * t)).le (sq_nonneg _)
  linarith

/-! ### 2. Unconditional Yosida and Yosida-Root Bounds on R_{H(t)}(a) f -/

theorem hamiltonian_resolvent_yosida_combined_ineq
    (N : ℝ) (hN : 0 < N) (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Real.exp (2 * t) * ‖action ε hε h N hN (RH t a f)‖ ^ 2 +
      a * ‖yosidaRootAction ε hε h N hN (RH t a f)‖ ^ 2 ≤
      (inner ℂ f (action ε hε h N hN (RH t a f))).re +
        (h ^ 2 / ε ^ 2) * ‖RH t a f‖ ^ 2 := by
  let x := resolventPoint ε hε h hh hb m g k t a ha f
  have hx : (x : Hilbert) = RH t a f := rfl
  have hval : H t x = f - a • RH t a f :=
    resolvent_equation ε hε h hh hb m g k t a ha f
  have hlow := hamiltonian_operator_yosida_pairing_lower ε hε h hh hb m g k N hN t x
  rw [hx, hval, inner_sub_left, inner_smul_left_eq_smul, Complex.sub_re,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero,
    ← yosidaRootAction_norm_sq_eq_inner ε hε h N hN (RH t a f)] at hlow
  linarith

theorem hamiltonian_resolvent_yosida_quadratic_ineq
    (N : ℝ) (hN : 0 < N) (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Real.exp (2 * t) * ‖action ε hε h N hN (RH t a f)‖ ^ 2 ≤
      (inner ℂ f (action ε hε h N hN (RH t a f))).re +
        (h ^ 2 / ε ^ 2) * ‖RH t a f‖ ^ 2 := by
  have h1 := hamiltonian_resolvent_yosida_combined_ineq ε hε h hh hb m g k N hN t a ha f
  have h2 : 0 ≤ a * ‖yosidaRootAction ε hε h N hN (RH t a f)‖ ^ 2 :=
    mul_nonneg ha.le (sq_nonneg _)
  linarith

theorem hamiltonian_resolvent_yosida_norm_bound
    (N : ℝ) (hN : 0 < N) (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖action ε hε h N hN (RH t a f)‖ ≤
      ‖f‖ / Real.exp (2 * t) + (|h| / ε * ‖RH t a f‖) / Real.exp t := by
  have hq0 := hamiltonian_resolvent_yosida_quadratic_ineq ε hε h hh hb m g k N hN t a ha f
  have hcs : (inner ℂ f (action ε hε h N hN (RH t a f))).re ≤
      ‖f‖ * ‖action ε hε h N hN (RH t a f)‖ :=
    re_inner_le_norm (𝕜 := ℂ) f (action ε hε h N hN (RH t a f))
  have he : (Real.exp t) ^ 2 = Real.exp (2 * t) := by
    rw [sq, ← Real.exp_add, show t + t = 2 * t by ring]
  have hd : (|h| / ε * ‖RH t a f‖) ^ 2 = (h ^ 2 / ε ^ 2) * ‖RH t a f‖ ^ 2 := by
    rw [mul_pow, div_pow, sq_abs]
  have hq := quadratic_bound
    ‖action ε hε h N hN (RH t a f)‖
    ‖f‖
    (|h| / ε * ‖RH t a f‖)
    (Real.exp t)
    (norm_nonneg _)
    (by positivity)
    (Real.exp_pos t)
    (by rw [he, hd]; linarith)
  simpa only [he] using hq

theorem hamiltonian_resolvent_yosidaRoot_quadratic_ineq
    (N : ℝ) (hN : 0 < N) (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    a * ‖yosidaRootAction ε hε h N hN (RH t a f)‖ ^ 2 ≤
      (inner ℂ (yosidaRootAction ε hε h N hN f)
        (yosidaRootAction ε hε h N hN (RH t a f))).re +
        (h ^ 2 / ε ^ 2) * ‖RH t a f‖ ^ 2 := by
  have h1 := hamiltonian_resolvent_yosida_combined_ineq ε hε h hh hb m g k N hN t a ha f
  have h2 : 0 ≤ Real.exp (2 * t) * ‖action ε hε h N hN (RH t a f)‖ ^ 2 :=
    mul_nonneg (Real.exp_pos (2 * t)).le (sq_nonneg _)
  rw [← yosidaRootAction_sq_inner ε hε h N hN f (RH t a f)] at h1
  linarith

theorem hamiltonian_resolvent_yosidaRoot_bound
    (N : ℝ) (hN : 0 < N) (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖yosidaRootAction ε hε h N hN (RH t a f)‖ ≤
      ‖yosidaRootAction ε hε h N hN f‖ / a +
        (|h| / ε * ‖RH t a f‖) / Real.sqrt a := by
  have hq0 := hamiltonian_resolvent_yosidaRoot_quadratic_ineq ε hε h hh hb m g k N hN t a ha f
  have hcs : (inner ℂ (yosidaRootAction ε hε h N hN f)
      (yosidaRootAction ε hε h N hN (RH t a f))).re ≤
      ‖yosidaRootAction ε hε h N hN f‖ * ‖yosidaRootAction ε hε h N hN (RH t a f)‖ :=
    re_inner_le_norm (𝕜 := ℂ)
      (yosidaRootAction ε hε h N hN f) (yosidaRootAction ε hε h N hN (RH t a f))
  have he : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
  have hd : (|h| / ε * ‖RH t a f‖) ^ 2 = (h ^ 2 / ε ^ 2) * ‖RH t a f‖ ^ 2 := by
    rw [mul_pow, div_pow, sq_abs]
  have hq := quadratic_bound
    ‖yosidaRootAction ε hε h N hN (RH t a f)‖
    ‖yosidaRootAction ε hε h N hN f‖
    (|h| / ε * ‖RH t a f‖)
    (Real.sqrt a)
    (norm_nonneg _)
    (by positivity)
    (Real.sqrt_pos.mpr ha)
    (by rw [he, hd]; linarith)
  simpa only [he] using hq

theorem hamiltonian_resolvent_yosidaRoot_le_of_radialRoot
    (N : ℝ) (hN : 0 < N) (t a : ℝ) (ha : 0 < a)
    (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖yosidaRootAction ε hε h N hN (RH t a f)‖ ≤
      ‖Kroot ⟨f, hf⟩‖ / a + (|h| / ε * ‖RH t a f‖) / Real.sqrt a := by
  have h1 := hamiltonian_resolvent_yosidaRoot_bound ε hε h hh hb m g k N hN t a ha f
  have h2 := div_le_div_of_nonneg_right
    (yosidaRootAction_norm_le_rootOperator ε hε h N hN f hf) ha.le
  linarith

theorem hamiltonian_resolvent_radialRoot_norm_le_of_radialRoot
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖Kroot ⟨RH t a f,
      KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_radialRoot_domain
        ε hε h hh hb m g k t a ha f⟩‖ ≤
      ‖Kroot ⟨f, hf⟩‖ / a + (|h| / ε * ‖RH t a f‖) / Real.sqrt a :=
  root_norm_of_uniform_bound ε hε h (RH t a f)
    (‖Kroot ⟨f, hf⟩‖ / a + (|h| / ε * ‖RH t a f‖) / Real.sqrt a)
    (fun n => hamiltonian_resolvent_yosidaRoot_le_of_radialRoot ε hε h hh hb m g k
      ((n : ℝ) + 1) (by positivity) t a ha f hf)

/-! ### 3. Unconditional 5-Way Three-Operator Domain Equivalence and Synthesis for R_{H(t)}(a) f -/

theorem hamiltonian_resolvent_mem_potential_iff_common
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (P).domain ↔
      RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k := by
  have hH : RH t a f ∈ (H t).domain :=
    resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f
  have heq := Set.ext_iff.mp (congrArg SetLike.coe
    (hamiltonian_residual_common_domain_eq ε hε h hh hb m g k t)) (RH t a f)
  change (RH t a f ∈ (H t).domain ∧ RH t a f ∈ (P).domain) ↔
    RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k at heq
  exact ⟨fun hp => heq.mp ⟨hH, hp⟩, fun hc => (heq.mpr hc).2⟩

theorem hamiltonian_resolvent_mem_static_iff_common
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (T).domain ↔
      RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k := by
  have hH : RH t a f ∈ (H t).domain :=
    resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f
  have heq := Set.ext_iff.mp (congrArg SetLike.coe
    (hamiltonian_static_common_domain_eq ε hε h hh hb m g k t)) (RH t a f)
  change (RH t a f ∈ (H t).domain ∧ RH t a f ∈ (T).domain) ↔
    RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k at heq
  exact ⟨fun ht => heq.mp ⟨hH, ht⟩, fun hc => (heq.mpr hc).2⟩

theorem hamiltonian_resolvent_mem_growing_iff_common
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (G).domain ↔
      RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k := by
  have hH : RH t a f ∈ (H t).domain :=
    resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f
  have heq := Set.ext_iff.mp (congrArg SetLike.coe
    (hamiltonian_growing_common_domain_eq ε hε h hh hb m g k t)) (RH t a f)
  change (RH t a f ∈ (H t).domain ∧ RH t a f ∈ (G).domain) ↔
    RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k at heq
  exact ⟨fun hg => heq.mp ⟨hH, hg⟩, fun hc => (heq.mpr hc).2⟩

theorem hamiltonian_resolvent_mem_potential_iff_static
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (P).domain ↔ RH t a f ∈ (T).domain :=
  (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).trans
    (hamiltonian_resolvent_mem_static_iff_common ε hε h hh hb m g k t a ha f).symm

theorem hamiltonian_resolvent_mem_potential_iff_growing
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (P).domain ↔ RH t a f ∈ (G).domain :=
  (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).trans
    (hamiltonian_resolvent_mem_growing_iff_common ε hε h hh hb m g k t a ha f).symm

theorem hamiltonian_resolvent_mem_potential_iff_shifted_residual_resolvent
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (P).domain ↔
      RS t a (f - (Real.exp (2 * t) : ℂ) •
        K ⟨RH t a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩) ∈ (P).domain :=
  iff_of_eq (congrArg (fun u : Hilbert => u ∈ (P).domain)
    (hamiltonian_resolvent_eq_residual_resolvent_shifted_source ε hε h hh hb m g k t a ha f))

theorem hamiltonian_resolvent_five_way_domain_iff
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    (RH t a f ∈ (P).domain ↔ RH t a f ∈ (T).domain) ∧
    (RH t a f ∈ (T).domain ↔ RH t a f ∈ (G).domain) ∧
    (RH t a f ∈ (G).domain ↔ RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k) ∧
    (RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k ↔
      RS t a (f - (Real.exp (2 * t) : ℂ) •
        K ⟨RH t a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩) ∈ (P).domain) :=
  ⟨hamiltonian_resolvent_mem_potential_iff_static ε hε h hh hb m g k t a ha f,
   (hamiltonian_resolvent_mem_static_iff_common ε hε h hh hb m g k t a ha f).trans
     (hamiltonian_resolvent_mem_growing_iff_common ε hε h hh hb m g k t a ha f).symm,
   hamiltonian_resolvent_mem_growing_iff_common ε hε h hh hb m g k t a ha f,
   (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).symm.trans
     (hamiltonian_resolvent_mem_potential_iff_shifted_residual_resolvent ε hε h hh hb m g k t a ha f)⟩

theorem hamiltonian_resolvent_eq_static_add_growing_of_potential
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
      (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
    let ht : RH t a f ∈ (T).domain := hc.1.1.1
    let hg : RH t a f ∈ (G).domain := common_domain_subset_growing ε hε h hh hb m g k hc
    H t ⟨RH t a f, resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩ =
      T ⟨RH t a f, ht⟩ + (Real.exp (2 * t) : ℂ) • G ⟨RH t a f, hg⟩ := by
  let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
    (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
  let ht : RH t a f ∈ (T).domain := hc.1.1.1
  let hg : RH t a f ∈ (G).domain := common_domain_subset_growing ε hε h hh hb m g k hc
  exact (H t).mem_graph_snd_inj'
    ((H t).mem_graph ⟨RH t a f, resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩)
    (unconditional_static_growing_hamiltonian_graph ε hε h hh hb m g k t
      (RH t a f) (T ⟨RH t a f, ht⟩) (G ⟨RH t a f, hg⟩)
      ((T).mem_graph ⟨RH t a f, ht⟩) ((G).mem_graph ⟨RH t a f, hg⟩) hc.2) rfl

theorem hamiltonian_resolvent_eq_three_operator_of_potential
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
      (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
    let ht : RH t a f ∈ (T).domain := hc.1.1.1
    H t ⟨RH t a f, resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩ =
      T ⟨RH t a f, ht⟩ +
        (Real.exp (2 * t) : ℂ) •
          (K ⟨RH t a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩ +
            P ⟨RH t a f, hp⟩) := by
  let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
    (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
  let ht : RH t a f ∈ (T).domain := hc.1.1.1
  exact (H t).mem_graph_snd_inj'
    ((H t).mem_graph ⟨RH t a f, resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩)
    (unconditional_three_operator_hamiltonian_graph ε hε h hh hb m g k t
      (RH t a f) (T ⟨RH t a f, ht⟩)
      (K ⟨RH t a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩)
      (P ⟨RH t a f, hp⟩)
      ((T).mem_graph ⟨RH t a f, ht⟩)
      ((K).mem_graph ⟨RH t a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩)
      ((P).mem_graph ⟨RH t a f, hp⟩) hc.2) rfl

theorem residual_on_hamiltonian_resolvent_eq_static_add_potential
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
      (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
    let ht : RH t a f ∈ (T).domain := hc.1.1.1
    S t ⟨RH t a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ =
      T ⟨RH t a f, ht⟩ + (Real.exp (2 * t) : ℂ) • P ⟨RH t a f, hp⟩ := by
  let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
    (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
  let ht : RH t a f ∈ (T).domain := hc.1.1.1
  exact (S t).mem_graph_snd_inj'
    ((S t).mem_graph ⟨RH t a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩)
    (unconditional_three_operator_residual_graph ε hε h hh hb m g k t
      (RH t a f) (T ⟨RH t a f, ht⟩) (P ⟨RH t a f, hp⟩)
      ((T).mem_graph ⟨RH t a f, ht⟩) ((P).mem_graph ⟨RH t a f, hp⟩) hc.2) rfl

theorem growing_on_hamiltonian_resolvent_eq_radial_add_potential
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
      (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
    let hg : RH t a f ∈ (G).domain := common_domain_subset_growing ε hε h hh hb m g k hc
    G ⟨RH t a f, hg⟩ =
      K ⟨RH t a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩ +
        P ⟨RH t a f, hp⟩ := by
  have hev := unconditional_two_operator_growing_eval ε hε h hh hb m g k
    (resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f) hp
  exact hev.choose_spec

theorem growing_on_hamiltonian_resolvent_split_norm_sq_le
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
      (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
    let hg : RH t a f ∈ (G).domain := common_domain_subset_growing ε hε h hh hb m g k hc
    ‖K ⟨RH t a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 +
      ‖P ⟨RH t a f, hp⟩‖ ^ 2 ≤
      ‖G ⟨RH t a f, hg⟩‖ ^ 2 := by
  let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
    (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
  let hg : RH t a f ∈ (G).domain := common_domain_subset_growing ε hε h hh hb m g k hc
  exact KFCausalClockFloorGrowingPotentialSum.split_norm_square ε hε h hh hb m g k
    ⟨RH t a f, hg⟩

theorem hamiltonian_resolvent_potential_norm_le_static_add_residual
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
      (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
    let ht : RH t a f ∈ (T).domain := hc.1.1.1
    Real.exp (2 * t) * ‖P ⟨RH t a f, hp⟩‖ ≤
      ‖T ⟨RH t a f, ht⟩‖ +
        ‖S t ⟨RH t a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖ := by
  let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
    (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
  let ht : RH t a f ∈ (T).domain := hc.1.1.1
  have hS := residual_on_hamiltonian_resolvent_eq_static_add_potential ε hε h hh hb m g k t a ha f hp
  dsimp only at hS
  have hsub : (Real.exp (2 * t) : ℂ) • P ⟨RH t a f, hp⟩ =
      S t ⟨RH t a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ -
        T ⟨RH t a f, ht⟩ := by
    rw [hS]
    abel
  have hnorm : Real.exp (2 * t) * ‖P ⟨RH t a f, hp⟩‖ =
      ‖S t ⟨RH t a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ -
        T ⟨RH t a f, ht⟩‖ := by
    rw [← hsub, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (2 * t))]
  have htri := norm_sub_le
    (S t ⟨RH t a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩)
    (T ⟨RH t a f, ht⟩)
  dsimp only
  linarith

theorem hamiltonian_resolvent_static_norm_le_potential_add_residual
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
      (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
    let ht : RH t a f ∈ (T).domain := hc.1.1.1
    ‖T ⟨RH t a f, ht⟩‖ ≤
      Real.exp (2 * t) * ‖P ⟨RH t a f, hp⟩‖ +
        ‖S t ⟨RH t a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖ := by
  let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
    (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
  let ht : RH t a f ∈ (T).domain := hc.1.1.1
  have hS := residual_on_hamiltonian_resolvent_eq_static_add_potential ε hε h hh hb m g k t a ha f hp
  dsimp only at hS
  have hsub : T ⟨RH t a f, ht⟩ =
      S t ⟨RH t a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ -
        (Real.exp (2 * t) : ℂ) • P ⟨RH t a f, hp⟩ := by
    rw [hS]
    abel
  have htri := norm_sub_le
    (S t ⟨RH t a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩)
    ((Real.exp (2 * t) : ℂ) • P ⟨RH t a f, hp⟩)
  rw [ ← hsub, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (2 * t))] at htri
  dsimp only
  linarith

theorem hamiltonian_resolvent_growing_norm_le_static_add_source
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
      (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
    let ht : RH t a f ∈ (T).domain := hc.1.1.1
    let hg : RH t a f ∈ (G).domain := common_domain_subset_growing ε hε h hh hb m g k hc
    Real.exp (2 * t) * ‖G ⟨RH t a f, hg⟩‖ ≤ ‖T ⟨RH t a f, ht⟩‖ + ‖f‖ := by
  let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
    (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
  let ht : RH t a f ∈ (T).domain := hc.1.1.1
  let hg : RH t a f ∈ (G).domain := common_domain_subset_growing ε hε h hh hb m g k hc
  have hH := hamiltonian_resolvent_eq_static_add_growing_of_potential ε hε h hh hb m g k t a ha f hp
  dsimp only at hH
  have hsub : (Real.exp (2 * t) : ℂ) • G ⟨RH t a f, hg⟩ =
      H t ⟨RH t a f, resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩ -
        T ⟨RH t a f, ht⟩ := by
    rw [hH]
    abel
  have hnorm : Real.exp (2 * t) * ‖G ⟨RH t a f, hg⟩‖ =
      ‖H t ⟨RH t a f, resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩ -
        T ⟨RH t a f, ht⟩‖ := by
    rw [← hsub, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (2 * t))]
  have htri := norm_sub_le
    (H t ⟨RH t a f, resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩)
    (T ⟨RH t a f, ht⟩)
  have hbH := resolvent_hamiltonian_norm_le ε hε h hh hb m g k t a ha f
  dsimp only
  linarith

theorem hamiltonian_resolvent_growing_norm_le_static_add_two_source
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    let hc : RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k :=
      (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f).mp hp
    let ht : RH t a f ∈ (T).domain := hc.1.1.1
    let hg : RH t a f ∈ (G).domain := common_domain_subset_growing ε hε h hh hb m g k hc
    Real.exp (2 * t) * ‖G ⟨RH t a f, hg⟩‖ ≤ ‖T ⟨RH t a f, ht⟩‖ + 2 * ‖f‖ := by
  have h1 := hamiltonian_resolvent_growing_norm_le_static_add_source ε hε h hh hb m g k t a ha f hp
  have hf0 : 0 ≤ ‖f‖ := norm_nonneg f
  dsimp only at h1 ⊢
  linarith

#print axioms radial_operator_yosida_pairing_lower
#print axioms radial_operator_yosida_pairing_nonneg
#print axioms hamiltonian_operator_yosida_pairing_lower
#print axioms hamiltonian_operator_yosida_pairing_lower_weak
#print axioms hamiltonian_resolvent_yosida_combined_ineq
#print axioms hamiltonian_resolvent_yosida_quadratic_ineq
#print axioms hamiltonian_resolvent_yosida_norm_bound
#print axioms hamiltonian_resolvent_yosidaRoot_quadratic_ineq
#print axioms hamiltonian_resolvent_yosidaRoot_bound
#print axioms hamiltonian_resolvent_yosidaRoot_le_of_radialRoot
#print axioms hamiltonian_resolvent_radialRoot_norm_le_of_radialRoot
#print axioms hamiltonian_resolvent_mem_potential_iff_common
#print axioms hamiltonian_resolvent_mem_static_iff_common
#print axioms hamiltonian_resolvent_mem_growing_iff_common
#print axioms hamiltonian_resolvent_mem_potential_iff_static
#print axioms hamiltonian_resolvent_mem_potential_iff_growing
#print axioms hamiltonian_resolvent_mem_potential_iff_shifted_residual_resolvent
#print axioms hamiltonian_resolvent_five_way_domain_iff
#print axioms hamiltonian_resolvent_eq_static_add_growing_of_potential
#print axioms hamiltonian_resolvent_eq_three_operator_of_potential
#print axioms residual_on_hamiltonian_resolvent_eq_static_add_potential
#print axioms growing_on_hamiltonian_resolvent_eq_radial_add_potential
#print axioms growing_on_hamiltonian_resolvent_split_norm_sq_le
#print axioms hamiltonian_resolvent_potential_norm_le_static_add_residual
#print axioms hamiltonian_resolvent_static_norm_le_potential_add_residual
#print axioms hamiltonian_resolvent_growing_norm_le_static_add_source
#print axioms hamiltonian_resolvent_growing_norm_le_static_add_two_source
end
end UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis
