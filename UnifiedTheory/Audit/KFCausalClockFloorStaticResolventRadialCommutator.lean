/- Unconditional static resolvent-radial commutator identity, joint 5-domain
regularity, O(N^{-1/2}) norm bounds, and strong graph convergence on all of
Hilbert:
1. For every f ∈ Hilbert, a > 0, and N > 0, the radial-regularized static
   resolvent state J_N (R_T(a) f) lies simultaneously in
   Dom(T) ∩ Dom(K_rad) ∩ Dom(clockHalf ε) ∩ Dom(T_stat) ∩ Dom(K_root),
   and M_N (R_T(a) f) lies in Dom(T) ∩ Dom(clockHalf ε) ∩ Dom(T_stat).
2. The shifted static operator action on J_N (R_T(a) f) satisfies
   T(J_N (R_T(a) f)) + a J_N (R_T(a) f) = J_N f + C_N(R_T(a) f),
   yielding the unconditional resolvent-radial commutator identity on Hilbert:
   J_N (R_T(a) f) - R_T(a) (J_N f) = R_T(a) (C_N(R_T(a) f))
   and T(J_N (R_T(a) f)) - T(R_T(a) (J_N f)) = T(R_T(a) (C_N(R_T(a) f))).
3. Consequently, R_T(a) (J_N f) ∈ Dom(K_rad) if and only if
   R_T(a) (C_N(R_T(a) f)) ∈ Dom(K_rad) (and similarly for Dom(K_root)),
   and the commutator satisfies explicit O(N^{-1/2}) Hilbert and T-graph norm
   bounds and strong convergence to zero as N → ∞ for every f ∈ Hilbert. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticRadialCore
import UnifiedTheory.Audit.KFCausalClockFloorStaticClockCore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticResolventRadialCommutator
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaDomain (operator)
open KFCausalClockFloorRadialResolventRegularizer
  (action radial_domain radial_graph action_norm sequence_tendsto)
open KFCausalClockFloorRadialResolventRoot (action_root_domain)
open KFCausalClockFloorRadialResolventClockCommutation
  (resolvent_clockHalf_domain resolvent_clockHalf_commute)
open KFCausalClockFloorRadialResolventStaticDomain
  (domainFormLift commutatorVector commutatorVector_tendsto
    staticOperator_resolvent_domain staticOperator_yosida_domain
    staticOperator_resolvent_apply staticOperator_resolvent_commutator_eq
    staticOperator_resolvent_commutator_bound
    staticOperator_resolvent_commutator_tendsto staticOperator_resolvent_tendsto)
open KFCausalClockFloorRadialResolventStaticRadialCore
  (static_domain_subset_clockHalf_domain static_resolvent_domain static_yosida_domain
    resolvent_maps_static_to_static_radial_clockHalf
    yosida_maps_static_to_static_clockHalf static_radial_core_commutator_bound)

private theorem accretive_resolvent_energy_split {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : KFCausalPositiveResolventBounds.Resolves T R a)
    (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x : H)).re) (f : H) :
    ‖T (KFCausalPositiveResolventBounds.point T R a hr f)‖ ^ 2 +
      a ^ 2 * ‖R f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  let x := KFCausalPositiveResolventBounds.point T R a hr f
  have hv := KFCausalPositiveResolventBounds.point_value T R a hr f
  have hsum : T x + (a : ℂ) • R f = f := by
    rw [hv, Complex.coe_smul, sub_add_cancel]
  have hexp : ‖T x + (a : ℂ) • R f‖ ^ 2 =
      ‖T x‖ ^ 2 + 2 * (inner ℂ (T x) ((a : ℂ) • R f)).re + ‖(a : ℂ) • R f‖ ^ 2 :=
    norm_add_sq (𝕜 := ℂ) (T x) ((a : ℂ) • R f)
  have hi : (inner ℂ (T x) ((a : ℂ) • R f)).re = a * (inner ℂ (T x) (x : H)).re := by
    change (inner ℂ (T x) ((a : ℂ) • (x : H))).re = a * (inner ℂ (T x) (x : H)).re
    rw [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  have hn : ‖(a : ℂ) • R f‖ ^ 2 = a ^ 2 * ‖R f‖ ^ 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, mul_pow]
  have hpos : 0 ≤ 2 * (a * (inner ℂ (T x) (x : H)).re) :=
    mul_nonneg zero_le_two (mul_nonneg ha.le (hp x))
  rw [hsum, hi, hn] at hexp
  linarith

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ)
  (hb : |h| ≤ Real.pi * ε / 3) (hh : h ≠ 0)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "Kr" => operator ε hε h
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "TD0" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw 0 0 0 0
local notation "TB0" => KFCausalClosedGraphForm.energyOutput TD0

/-! ### 1. Unconditional Static Operator Positivity and Shifted Resolvent on T -/

theorem staticOperator_positive (x : (T).domain) :
    0 ≤ (inner ℂ (T x) (x : Hilbert)).re := by
  let xR : (Tstat).domain :=
    ⟨(x : Hilbert), KFCausalClockFloorStaticOperator.root_domain ε hε h x⟩
  have hp : inner ℂ (Tstat xR) (Tstat xR) = inner ℂ (x : Hilbert) (T x) :=
    KFCausalClockFloorStaticOperator.root_pairing ε hε h x xR
  have hsymm : (inner ℂ (T x) (x : Hilbert)).re = (inner ℂ (x : Hilbert) (T x)).re := by
    rw [← inner_conj_symm (T x) (x : Hilbert), Complex.conj_re]
  rw [hsymm, ← hp]
  exact (sq_nonneg ‖Tstat xR‖).trans_eq (inner_self_eq_norm_sq (𝕜 := ℂ) (Tstat xR)).symm

def staticResolvent (a : ℝ) : Hilbert →L[ℂ] Hilbert :=
  KFCausalClockFloorStaticClockCore.resolvent ε hε h hh hw 0 0 0 0 a

local notation "RT" => staticResolvent ε hε h hb hh

theorem staticResolvent_resolves (a : ℝ) (ha : 0 < a) :
    KFCausalPositiveResolventBounds.Resolves T (RT a) a := by
  have hr := KFCausalClockFloorStaticClockCore.resolves ε hε h hh hw 0 0 0 0 a ha
  rwa [KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hw 0 0 0 0] at hr

private theorem mem_hamiltonian_domain_of_mem_static (f : Hilbert) (hf : f ∈ (T).domain) :
    f ∈ (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw 0 0 0 0).domain := by
  rwa [KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hw 0 0 0 0]

private theorem hamiltonian_graph_to_static {f q : Hilbert}
    (hg : (f, q) ∈
      (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw 0 0 0 0).graph) :
    (f, q) ∈ (T).graph := by
  rwa [KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hw 0 0 0 0] at hg

theorem staticResolvent_left_inverse (a : ℝ) (ha : 0 < a) (x : (T).domain) :
    RT a (T x + a • (x : Hilbert)) = (x : Hilbert) := by
  let xH : (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw 0 0 0 0).domain :=
    ⟨(x : Hilbert), mem_hamiltonian_domain_of_mem_static ε hε h hb hh (x : Hilbert) x.property⟩
  have hval : KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw 0 0 0 0 xH = T x := by
    have hg : ((x : Hilbert),
        KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw 0 0 0 0 xH) ∈ (T).graph :=
      hamiltonian_graph_to_static ε hε h hb hh
        ((KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw 0 0 0 0).mem_graph xH)
    exact (T).mem_graph_snd_inj' hg ((T).mem_graph x) rfl
  rw [← hval]
  exact KFCausalClockFloorStaticClockCore.left_inverse ε hε h hh hw 0 0 0 0 a ha xH

def staticResolventPoint (a : ℝ) (ha : 0 < a) (f : Hilbert) : (T).domain :=
  KFCausalPositiveResolventBounds.point T (RT a) a
    (staticResolvent_resolves ε hε h hb hh a ha) f

theorem staticResolvent_mem_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RT a f ∈ (T).domain :=
  (staticResolventPoint ε hε h hb hh a ha f).property

theorem staticResolvent_equation (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    T (staticResolventPoint ε hε h hb hh a ha f) = f - a • RT a f :=
  KFCausalPositiveResolventBounds.point_value T (RT a) a
    (staticResolvent_resolves ε hε h hb hh a ha) f

theorem staticResolvent_shifted_apply (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    T (staticResolventPoint ε hε h hb hh a ha f) + a • RT a f = f := by
  rw [staticResolvent_equation ε hε h hb hh a ha f, sub_add_cancel]

theorem staticResolvent_eq_any_couplings (m g k t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    KFCausalClockFloorStaticClockCore.resolvent ε hε h hh hw m g k t a f = RT a f := by
  let R' := KFCausalClockFloorStaticClockCore.resolvent ε hε h hh hw m g k t a
  have hr' : KFCausalPositiveResolventBounds.Resolves T R' a := by
    have hr0 := KFCausalClockFloorStaticClockCore.resolves ε hε h hh hw m g k t a ha
    rwa [KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hw m g k t] at hr0
  let x' := KFCausalPositiveResolventBounds.point T R' a hr' f
  have hv' : T x' + a • (x' : Hilbert) = f := by
    change T x' + a • R' f = f
    rw [KFCausalPositiveResolventBounds.point_value T R' a hr' f, sub_add_cancel]
  exact (staticResolvent_left_inverse ε hε h hb hh a ha x').symm.trans (congrArg (RT a) hv')

theorem staticResolvent_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖RT a f‖ ≤ a⁻¹ * ‖f‖ :=
  KFCausalPositiveResolventBounds.resolvent_apply_norm_bound T (RT a) a ha
    (staticResolvent_resolves ε hε h hb hh a ha)
    (staticOperator_positive ε hε h) f

theorem staticResolvent_operator_norm_sq_add_scaled_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖T (staticResolventPoint ε hε h hb hh a ha f)‖ ^ 2 +
      a ^ 2 * ‖RT a f‖ ^ 2 ≤ ‖f‖ ^ 2 :=
  accretive_resolvent_energy_split T (RT a) a ha
    (staticResolvent_resolves ε hε h hb hh a ha)
    (staticOperator_positive ε hε h) f

theorem staticResolvent_operator_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖T (staticResolventPoint ε hε h hb hh a ha f)‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hsq := staticResolvent_operator_norm_sq_add_scaled_sq_le ε hε h hb hh a ha f
  have ha0 : 0 ≤ a ^ 2 * ‖RT a f‖ ^ 2 := by positivity
  linarith

theorem staticResolvent_operator_norm_le_two (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖T (staticResolventPoint ε hε h hb hh a ha f)‖ ≤ 2 * ‖f‖ := by
  have h1 := staticResolvent_operator_norm_le ε hε h hb hh a ha f
  linarith [norm_nonneg f]

theorem staticResolvent_mem_clockHalf_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RT a f ∈ (clockHalf ε).domain :=
  static_domain_subset_clockHalf_domain ε hε h (RT a f)
    (staticResolvent_mem_domain ε hε h hb hh a ha f)

theorem staticResolvent_mem_staticRoot_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RT a f ∈ (Tstat).domain :=
  KFCausalClockFloorStaticOperator.root_domain ε hε h
    (staticResolventPoint ε hε h hb hh a ha f)

/-! ### 2. Unconditional Joint 5-Domain Regularity and Exact Resolvent-Radial Commutator Identity -/

variable (N : ℝ) (hN : 0 < N)

local notation "J" => action ε hε h N hN
local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN

theorem radial_staticResolvent_mem_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    J (RT a f) ∈ (T).domain :=
  static_resolvent_domain ε hε h N hN hb hh (RT a f)
    (staticResolvent_mem_domain ε hε h hb hh a ha f)

def radialStaticResolventPoint (a : ℝ) (ha : 0 < a) (f : Hilbert) : (T).domain :=
  ⟨J (RT a f), radial_staticResolvent_mem_domain ε hε h hb hh N hN a ha f⟩

theorem radial_staticResolvent_five_domains (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    J (RT a f) ∈ (T).domain ∧
      J (RT a f) ∈ (Kr).domain ∧
      J (RT a f) ∈ (clockHalf ε).domain ∧
      J (RT a f) ∈ (Tstat).domain ∧
      J (RT a f) ∈ (Kroot).domain :=
  resolvent_maps_static_to_static_radial_clockHalf ε hε h N hN hb hh (RT a f)
    (staticResolvent_mem_domain ε hε h hb hh a ha f)

theorem yosida_staticResolvent_three_domains (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    M (RT a f) ∈ (T).domain ∧
      M (RT a f) ∈ (clockHalf ε).domain ∧
      M (RT a f) ∈ (Tstat).domain :=
  yosida_maps_static_to_static_clockHalf ε hε h N hN hb hh (RT a f)
    (staticResolvent_mem_domain ε hε h hb hh a ha f)

def staticResolventCommutator (a : ℝ) (ha : 0 < a) (f : Hilbert) : Hilbert :=
  commutatorVector ε hε h N hN hh 0 0 0 (RT a f)
    (TB0 (domainFormLift ε hε h hb hh 0 0 0 (staticResolventPoint ε hε h hb hh a ha f)))

theorem static_apply_radial_staticResolvent_eq (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    T (radialStaticResolventPoint ε hε h hb hh N hN a ha f) =
      J (T (staticResolventPoint ε hε h hb hh a ha f)) +
        staticResolventCommutator ε hε h hb hh N hN a ha f :=
  staticOperator_resolvent_apply ε hε h N hN hb hh 0 0 0
    (staticResolventPoint ε hε h hb hh a ha f)

theorem static_apply_radial_staticResolvent (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    T (radialStaticResolventPoint ε hε h hb hh N hN a ha f) =
      J f - a • J (RT a f) + staticResolventCommutator ε hε h hb hh N hN a ha f := by
  rw [static_apply_radial_staticResolvent_eq ε hε h hb hh N hN a ha f,
    staticResolvent_equation ε hε h hb hh a ha f,
    map_sub, ContinuousLinearMap.map_smul_of_tower]

theorem shifted_static_apply_radial_staticResolvent (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    T (radialStaticResolventPoint ε hε h hb hh N hN a ha f) + a • J (RT a f) =
      J f + staticResolventCommutator ε hε h hb hh N hN a ha f := by
  rw [static_apply_radial_staticResolvent ε hε h hb hh N hN a ha f]
  abel

theorem radial_staticResolvent_eq_add (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    J (RT a f) =
      RT a (J f) + RT a (staticResolventCommutator ε hε h hb hh N hN a ha f) := by
  have hleft := staticResolvent_left_inverse ε hε h hb hh a ha
    (radialStaticResolventPoint ε hε h hb hh N hN a ha f)
  change RT a (T (radialStaticResolventPoint ε hε h hb hh N hN a ha f) + a • J (RT a f)) =
    J (RT a f) at hleft
  rw [shifted_static_apply_radial_staticResolvent ε hε h hb hh N hN a ha f,
    map_add] at hleft
  exact hleft.symm

theorem staticResolvent_radial_commutator_eq (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    J (RT a f) - RT a (J f) =
      RT a (staticResolventCommutator ε hε h hb hh N hN a ha f) := by
  rw [radial_staticResolvent_eq_add ε hε h hb hh N hN a ha f, add_sub_cancel_left]

theorem staticResolvent_radial_eq_sub (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RT a (J f) =
      J (RT a f) - RT a (staticResolventCommutator ε hε h hb hh N hN a ha f) := by
  rw [radial_staticResolvent_eq_add ε hε h hb hh N hN a ha f, add_sub_cancel_right]

theorem staticResolvent_radial_mem_radial_domain_iff (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RT a (J f) ∈ (Kr).domain ↔
      RT a (staticResolventCommutator ε hε h hb hh N hN a ha f) ∈ (Kr).domain := by
  have hJ : J (RT a f) ∈ (Kr).domain := radial_domain ε hε h N hN (RT a f)
  constructor
  · intro hR
    have hsub := (Kr).domain.sub_mem hJ hR
    rwa [staticResolvent_radial_commutator_eq ε hε h hb hh N hN a ha f] at hsub
  · intro hC
    have hsub := (Kr).domain.sub_mem hJ hC
    rwa [← staticResolvent_radial_eq_sub ε hε h hb hh N hN a ha f] at hsub

theorem staticResolvent_radial_mem_radialRoot_domain_iff (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RT a (J f) ∈ (Kroot).domain ↔
      RT a (staticResolventCommutator ε hε h hb hh N hN a ha f) ∈ (Kroot).domain := by
  have hJ : J (RT a f) ∈ (Kroot).domain := action_root_domain ε hε h N hN (RT a f)
  constructor
  · intro hR
    have hsub := (Kroot).domain.sub_mem hJ hR
    rwa [staticResolvent_radial_commutator_eq ε hε h hb hh N hN a ha f] at hsub
  · intro hC
    have hsub := (Kroot).domain.sub_mem hJ hC
    rwa [← staticResolvent_radial_eq_sub ε hε h hb hh N hN a ha f] at hsub

theorem static_apply_commutator_eq (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    T (radialStaticResolventPoint ε hε h hb hh N hN a ha f) -
      T (staticResolventPoint ε hε h hb hh a ha (J f)) =
      T (staticResolventPoint ε hε h hb hh a ha
        (staticResolventCommutator ε hε h hb hh N hN a ha f)) := by
  rw [static_apply_radial_staticResolvent ε hε h hb hh N hN a ha f,
    staticResolvent_equation ε hε h hb hh a ha (J f),
    staticResolvent_equation ε hε h hb hh a ha
      (staticResolventCommutator ε hε h hb hh N hN a ha f),
    ← staticResolvent_radial_commutator_eq ε hε h hb hh N hN a ha f,
    smul_sub]
  abel

/-! ### 3. Unconditional O(N^{-1/2}) Commutator Norm Bounds and Strong Convergence -/

theorem staticResolventCommutator_bound (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖staticResolventCommutator ε hε h hb hh N hN a ha f‖ ≤
      (3 * (N⁻¹ * (|h| * Real.sqrt (N / ε) * (Real.sqrt ε)⁻¹))) *
        Real.sqrt (‖T (staticResolventPoint ε hε h hb hh a ha f)‖ * ‖RT a f‖) +
      (N⁻¹ * (6 * h ^ 2 / ε ^ 2)) * ‖RT a f‖ := by
  have heq := staticOperator_resolvent_commutator_eq ε hε h N hN hb hh 0 0 0
    (staticResolventPoint ε hε h hb hh a ha f)
  change T (radialStaticResolventPoint ε hε h hb hh N hN a ha f) -
    J (T (staticResolventPoint ε hε h hb hh a ha f)) =
    staticResolventCommutator ε hε h hb hh N hN a ha f at heq
  rw [← heq]
  exact static_radial_core_commutator_bound ε hε h N hN hb hh
    (staticResolventPoint ε hε h hb hh a ha f)

theorem staticResolventCommutator_source_bound (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖staticResolventCommutator ε hε h hb hh N hN a ha f‖ ≤
      ((3 * (N⁻¹ * (|h| * Real.sqrt (N / ε) * (Real.sqrt ε)⁻¹))) * Real.sqrt (a⁻¹) +
        (N⁻¹ * (6 * h ^ 2 / ε ^ 2)) * a⁻¹) * ‖f‖ := by
  have hb0 := staticResolventCommutator_bound ε hε h hb hh N hN a ha f
  have hT := staticResolvent_operator_norm_le ε hε h hb hh a ha f
  have hR := staticResolvent_norm_le ε hε h hb hh a ha f
  have hprod : ‖T (staticResolventPoint ε hε h hb hh a ha f)‖ * ‖RT a f‖ ≤
      (Real.sqrt (a⁻¹) * ‖f‖) ^ 2 := by
    calc
      ‖T (staticResolventPoint ε hε h hb hh a ha f)‖ * ‖RT a f‖ ≤
          ‖f‖ * (a⁻¹ * ‖f‖) :=
        mul_le_mul hT hR (norm_nonneg _) (norm_nonneg _)
      _ = a⁻¹ * ‖f‖ ^ 2 := by ring
      _ = (Real.sqrt (a⁻¹) * ‖f‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr ha.le)]
  have hsqrt : Real.sqrt (‖T (staticResolventPoint ε hε h hb hh a ha f)‖ * ‖RT a f‖) ≤
      Real.sqrt (a⁻¹) * ‖f‖ :=
    Real.sqrt_le_iff.mpr ⟨mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _), hprod⟩
  have hm1 := mul_le_mul_of_nonneg_left hsqrt
    (show 0 ≤ 3 * (N⁻¹ * (|h| * Real.sqrt (N / ε) * (Real.sqrt ε)⁻¹)) by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hR
    (show 0 ≤ N⁻¹ * (6 * h ^ 2 / ε ^ 2) by positivity)
  linarith

theorem staticResolvent_radial_commutator_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖J (RT a f) - RT a (J f)‖ ≤
      a⁻¹ * ‖staticResolventCommutator ε hε h hb hh N hN a ha f‖ := by
  rw [staticResolvent_radial_commutator_eq ε hε h hb hh N hN a ha f]
  exact staticResolvent_norm_le ε hε h hb hh a ha
    (staticResolventCommutator ε hε h hb hh N hN a ha f)

theorem staticResolvent_radial_commutator_source_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖J (RT a f) - RT a (J f)‖ ≤
      a⁻¹ * (((3 * (N⁻¹ * (|h| * Real.sqrt (N / ε) * (Real.sqrt ε)⁻¹))) * Real.sqrt (a⁻¹) +
        (N⁻¹ * (6 * h ^ 2 / ε ^ 2)) * a⁻¹) * ‖f‖) :=
  (staticResolvent_radial_commutator_norm_le ε hε h hb hh N hN a ha f).trans
    (mul_le_mul_of_nonneg_left
      (staticResolventCommutator_source_bound ε hε h hb hh N hN a ha f)
      (inv_nonneg.mpr ha.le))

theorem staticResolvent_radial_operator_diff_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖T (radialStaticResolventPoint ε hε h hb hh N hN a ha f) -
        T (staticResolventPoint ε hε h hb hh a ha (J f))‖ ≤
      ‖staticResolventCommutator ε hε h hb hh N hN a ha f‖ := by
  rw [static_apply_commutator_eq ε hε h hb hh N hN a ha f]
  exact staticResolvent_operator_norm_le ε hε h hb hh a ha
    (staticResolventCommutator ε hε h hb hh N hN a ha f)

theorem staticResolvent_radial_operator_diff_norm_le_two (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖T (radialStaticResolventPoint ε hε h hb hh N hN a ha f) -
        T (staticResolventPoint ε hε h hb hh a ha (J f))‖ ≤
      2 * ‖staticResolventCommutator ε hε h hb hh N hN a ha f‖ := by
  have h1 := staticResolvent_radial_operator_diff_norm_le ε hε h hb hh N hN a ha f
  linarith [norm_nonneg (staticResolventCommutator ε hε h hb hh N hN a ha f)]

theorem staticResolventCommutator_tendsto (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Tendsto (fun n : ℕ =>
      staticResolventCommutator ε hε h hb hh ((n : ℝ) + 1) (by positivity) a ha f)
      atTop (𝓝 0) :=
  commutatorVector_tendsto ε hε h hh 0 0 0 (RT a f)
    (TB0 (domainFormLift ε hε h hb hh 0 0 0 (staticResolventPoint ε hε h hb hh a ha f)))

theorem staticResolvent_radial_commutator_tendsto (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Tendsto (fun n : ℕ =>
      action ε hε h ((n : ℝ) + 1) (by positivity) (RT a f) -
        RT a (action ε hε h ((n : ℝ) + 1) (by positivity) f))
      atTop (𝓝 0) := by
  have hcont := ((RT a).continuous.tendsto 0).comp
    (staticResolventCommutator_tendsto ε hε h hb hh a ha f)
  rw [map_zero] at hcont
  exact hcont.congr (fun n =>
    (staticResolvent_radial_commutator_eq ε hε h hb hh ((n : ℝ) + 1) (by positivity) a ha f).symm)

theorem staticResolvent_radial_operator_tendsto (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Tendsto (fun n : ℕ =>
      T (radialStaticResolventPoint ε hε h hb hh ((n : ℝ) + 1) (by positivity) a ha f))
      atTop (𝓝 (T (staticResolventPoint ε hε h hb hh a ha f))) :=
  staticOperator_resolvent_tendsto ε hε h hb hh 0 0 0
    (staticResolventPoint ε hε h hb hh a ha f)

theorem staticResolvent_radial_operator_diff_tendsto (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Tendsto (fun n : ℕ =>
      T (radialStaticResolventPoint ε hε h hb hh ((n : ℝ) + 1) (by positivity) a ha f) -
        T (staticResolventPoint ε hε h hb hh a ha
          (action ε hε h ((n : ℝ) + 1) (by positivity) f)))
      atTop (𝓝 0) := by
  have hc := (tendsto_zero_iff_norm_tendsto_zero.mp
    (staticResolventCommutator_tendsto ε hε h hb hh a ha f))
  have hn : Tendsto (fun n : ℕ =>
      ‖T (radialStaticResolventPoint ε hε h hb hh ((n : ℝ) + 1) (by positivity) a ha f) -
        T (staticResolventPoint ε hε h hb hh a ha
          (action ε hε h ((n : ℝ) + 1) (by positivity) f))‖)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _)
      (fun n => staticResolvent_radial_operator_diff_norm_le
        ε hε h hb hh ((n : ℝ) + 1) (by positivity) a ha f) hc
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

#print axioms staticOperator_positive
#print axioms staticResolvent_resolves
#print axioms staticResolvent_left_inverse
#print axioms staticResolvent_mem_domain
#print axioms staticResolvent_equation
#print axioms staticResolvent_shifted_apply
#print axioms staticResolvent_eq_any_couplings
#print axioms staticResolvent_norm_le
#print axioms staticResolvent_operator_norm_sq_add_scaled_sq_le
#print axioms staticResolvent_operator_norm_le
#print axioms staticResolvent_operator_norm_le_two
#print axioms staticResolvent_mem_clockHalf_domain
#print axioms staticResolvent_mem_staticRoot_domain
#print axioms radial_staticResolvent_mem_domain
#print axioms radial_staticResolvent_five_domains
#print axioms yosida_staticResolvent_three_domains
#print axioms static_apply_radial_staticResolvent_eq
#print axioms static_apply_radial_staticResolvent
#print axioms shifted_static_apply_radial_staticResolvent
#print axioms radial_staticResolvent_eq_add
#print axioms staticResolvent_radial_commutator_eq
#print axioms staticResolvent_radial_eq_sub
#print axioms staticResolvent_radial_mem_radial_domain_iff
#print axioms staticResolvent_radial_mem_radialRoot_domain_iff
#print axioms static_apply_commutator_eq
#print axioms staticResolventCommutator_bound
#print axioms staticResolventCommutator_source_bound
#print axioms staticResolvent_radial_commutator_norm_le
#print axioms staticResolvent_radial_commutator_source_norm_le
#print axioms staticResolvent_radial_operator_diff_norm_le
#print axioms staticResolvent_radial_operator_diff_norm_le_two
#print axioms staticResolventCommutator_tendsto
#print axioms staticResolvent_radial_commutator_tendsto
#print axioms staticResolvent_radial_operator_tendsto
#print axioms staticResolvent_radial_operator_diff_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticResolventRadialCommutator
