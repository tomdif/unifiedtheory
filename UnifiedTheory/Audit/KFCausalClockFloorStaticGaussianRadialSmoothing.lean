/- Joint clock-Gaussian and radial-resolvent smoothing on the maximal static
operator domain:
1. For every x ∈ Dom(T), Gaussian width a > 0, and radial Yosida parameter N > 0,
   the doubly regularized state J_N (G_a x) = G_a (J_N x) lies simultaneously in
   all six domains:
   Dom(T) ∩ Dom(K_rad) ∩ Dom(clockOperator ε hε) ∩ Dom(clockHalf ε) ∩ Dom(T_stat) ∩ Dom(K_root),
   and M_N (G_a x) = G_a (M_N x) lies in
   Dom(T) ∩ Dom(clockOperator ε hε) ∩ Dom(clockHalf ε) ∩ Dom(T_stat).
2. The static-radial commutator vector C_N on Dom(T) is equivariant under
   centered clock-Gaussian smoothing:
   C_N(G_a x) = G_a (C_N x),
   so ‖C_N(G_a x)‖ ≤ ‖C_N x‖ and ‖T(J_N (G_a x))‖ ≤ ‖T(J_N x)‖ uniformly in a ≥ 0.
3. As a → 0+ at fixed N > 0, J_N (G_a x) converges strongly to J_N x across
   Hilbert, T, K_rad, K_root, T_stat, and clockHalf ε; as N → ∞ at fixed a ≥ 0,
   T(J_N (G_a x)) → G_a (T x); and along the diagonal a_n = (n+1)⁻¹, N_n = n+1,
   J_{n+1}(G_{(n+1)⁻¹} x) ∈ Dom(T) ∩ Dom(K_rad) ∩ Dom(clockOperator ε hε)
   converges to x in the graph norm of T (as well as in clockHalf ε and T_stat),
   proving that Dom(T) ∩ Dom(K_rad) ∩ Dom(clockOperator ε hε) is an operator
   graph core for T. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticRadialCore
import UnifiedTheory.Audit.KFCausalClockFloorGaussianClockCommutation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticGaussianRadialSmoothing
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalChargeTransverseSplit (dualPhysical)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorClockOperator (clockOperator)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaDomain (operator)
open KFCausalClockFloorRadialResolventRegularizer
  (action radial_domain radial_graph action_norm sequence_tendsto)
open KFCausalClockFloorRadialResolventRoot
  (cutoffRootSymbol rootAction rootAction_coe root_graph action_root_domain)
open KFCausalClockFloorGaussianGrowingTransport (line action_coordinates)
open KFCausalClockFloorGaussianGrowingApproximation (action_tendsto)
open KFCausalClockFloorGaussianStaticCommutation
  (gaussian_dual_coe static_graph static_domain)
open KFCausalClockFloorGaussianGrowingRadialPairing
  (root_gaussian_graph radial_gaussian_graph)
open KFCausalClockFloorGaussianClockCommutation
  (gaussian_clockHalf_domain gaussian_clockHalf_commute
    gaussian_clockOperator_domain gaussian_clockOperator_commute
    gaussian_mem_clockOperator_domain_of_pos gaussian_mem_clockHalf_domain_of_pos)
open KFCausalClockFloorRadialResolventClockCommutation
  (resolvent_gaussian_commute yosida_gaussian_commute
    resolvent_clockHalf_domain resolvent_clockHalf_commute resolvent_clockHalf_tendsto
    resolvent_clockOperator_domain resolvent_clockOperator_commute)
open KFCausalClockFloorRadialResolventStaticDomain
  (domainFormLift commutatorVector commutatorVector_tendsto
    staticOperator_resolvent_domain staticOperator_yosida_domain
    staticOperator_resolvent_apply staticOperator_resolvent_commutator_eq
    staticOperator_resolvent_commutator_bound
    staticOperator_resolvent_commutator_tendsto staticOperator_resolvent_tendsto)
open KFCausalClockFloorRadialResolventStaticRadialCore
  (static_domain_subset_clockHalf_domain static_resolvent_domain static_yosida_domain
    resolvent_radial_apply_eq_yosida)
open KFCausalUnitaryRealMultiplier (realPullback_graph)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ)
  (hb : |h| ≤ Real.pi * ε / 3) (hh : h ≠ 0)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "Kr" => operator ε hε h
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "TD0" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw 0 0 0 0
local notation "TB0" => KFCausalClosedGraphForm.energyOutput TD0
local notation "Ga" => KFCausalClockFloorGaussianGrowingTransport.action ε

/-! ### 1. Centered Clock-Gaussian Contraction and Operator Commutation -/

theorem gaussian_zero_norm_le (a : ℝ) (ha : 0 ≤ a) (f : Hilbert) :
    ‖Ga a ha 0 f‖ ≤ ‖f‖ := by
  have hn := KFCausalClockFloorGaussianGrowingTransport.action_norm ε a ha 0 f
  simpa only [sq, mul_zero, Real.exp_zero, one_mul] using hn

theorem static_gaussian_commute (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (x : (T).domain) :
    T ⟨Ga a ha y (x : Hilbert), static_domain ε hε a ha h y x⟩ =
      Ga a ha y (T x) :=
  (T).mem_graph_snd_inj'
    ((T).mem_graph ⟨Ga a ha y (x : Hilbert), static_domain ε hε a ha h y x⟩)
    (static_graph ε hε a ha h y (x : Hilbert) (T x) ((T).mem_graph x)) rfl

theorem radial_gaussian_domain (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert)
    (hf : f ∈ (Kr).domain) :
    Ga a ha y f ∈ (Kr).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (radial_gaussian_graph ε hε a ha h y f (Kr ⟨f, hf⟩) ((Kr).mem_graph ⟨f, hf⟩))

theorem radial_gaussian_commute (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert)
    (hf : f ∈ (Kr).domain) :
    Kr ⟨Ga a ha y f, radial_gaussian_domain ε hε h a ha y f hf⟩ =
      Ga a ha y (Kr ⟨f, hf⟩) :=
  (Kr).mem_graph_snd_inj'
    ((Kr).mem_graph ⟨Ga a ha y f, radial_gaussian_domain ε hε h a ha y f hf⟩)
    (radial_gaussian_graph ε hε a ha h y f (Kr ⟨f, hf⟩) ((Kr).mem_graph ⟨f, hf⟩)) rfl

theorem root_gaussian_domain (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert)
    (hf : f ∈ (Kroot).domain) :
    Ga a ha y f ∈ (Kroot).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (root_gaussian_graph ε hε a ha h y f (Kroot ⟨f, hf⟩) ((Kroot).mem_graph ⟨f, hf⟩))

theorem root_gaussian_commute (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert)
    (hf : f ∈ (Kroot).domain) :
    Kroot ⟨Ga a ha y f, root_gaussian_domain ε hε h a ha y f hf⟩ =
      Ga a ha y (Kroot ⟨f, hf⟩) :=
  (Kroot).mem_graph_snd_inj'
    ((Kroot).mem_graph ⟨Ga a ha y f, root_gaussian_domain ε hε h a ha y f hf⟩)
    (root_gaussian_graph ε hε a ha h y f (Kroot ⟨f, hf⟩) ((Kroot).mem_graph ⟨f, hf⟩)) rfl

theorem staticRoot_gaussian_graph (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f z : Hilbert)
    (hfg : (f, z) ∈ (Tstat).graph) :
    (Ga a ha y f, Ga a ha y z) ∈ (Tstat).graph := by
  have hm : Measurable (KFCausalClockFloorStaticMultiplierForm.rootSymbol ε h) :=
    (KFCausalClockFloorStaticMultiplierForm.symbol_continuous ε hε h).sqrt.measurable
  have hr := (realPullback_graph dualPhysical
    (KFCausalClockFloorStaticMultiplierForm.rootSymbol ε h) hm f z).mp hfg
  apply (realPullback_graph dualPhysical
    (KFCausalClockFloorStaticMultiplierForm.rootSymbol ε h) hm _ _).mpr
  filter_upwards [hr, gaussian_dual_coe ε a ha y f, gaussian_dual_coe ε a ha y z]
    with x hx hf hz
  rw [hz, hf, hx]
  ring

theorem staticRoot_gaussian_domain (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert)
    (hf : f ∈ (Tstat).domain) :
    Ga a ha y f ∈ (Tstat).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (staticRoot_gaussian_graph ε hε h a ha y f (Tstat ⟨f, hf⟩) ((Tstat).mem_graph ⟨f, hf⟩))

theorem staticRoot_gaussian_commute (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert)
    (hf : f ∈ (Tstat).domain) :
    Tstat ⟨Ga a ha y f, staticRoot_gaussian_domain ε hε h a ha y f hf⟩ =
      Ga a ha y (Tstat ⟨f, hf⟩) :=
  (Tstat).mem_graph_snd_inj'
    ((Tstat).mem_graph ⟨Ga a ha y f, staticRoot_gaussian_domain ε hε h a ha y f hf⟩)
    (staticRoot_gaussian_graph ε hε h a ha y f (Tstat ⟨f, hf⟩) ((Tstat).mem_graph ⟨f, hf⟩)) rfl

theorem rootAction_gaussian_commute (N : ℝ) (hN : 0 < N) (a : ℝ) (ha : 0 ≤ a)
    (y : ℝ) (f : Hilbert) :
    rootAction ε hε h N hN (Ga a ha y f) =
      Ga a ha y (rootAction ε hε h N hN f) := by
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [rootAction_coe ε hε h N hN (Ga a ha y f),
    action_coordinates ε a ha y f,
    action_coordinates ε a ha y (rootAction ε hε h N hN f),
    rootAction_coe ε hε h N hN f] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  ring

def gaussianStaticPoint (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) : (T).domain :=
  ⟨Ga a ha 0 (x : Hilbert), static_domain ε hε a ha h 0 x⟩

theorem gaussianStaticPoint_coe (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) :
    ((gaussianStaticPoint ε hε h a ha x : (T).domain) : Hilbert) =
      Ga a ha 0 (x : Hilbert) := rfl

theorem gaussianStaticPoint_apply (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) :
    T (gaussianStaticPoint ε hε h a ha x) = Ga a ha 0 (T x) :=
  static_gaussian_commute ε hε h a ha 0 x

theorem gaussianStaticPoint_norm_le (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) :
    ‖((gaussianStaticPoint ε hε h a ha x : (T).domain) : Hilbert)‖ ≤ ‖(x : Hilbert)‖ :=
  gaussian_zero_norm_le ε a ha (x : Hilbert)

theorem gaussianStaticPoint_apply_norm_le (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) :
    ‖T (gaussianStaticPoint ε hε h a ha x)‖ ≤ ‖T x‖ := by
  rw [gaussianStaticPoint_apply]
  exact gaussian_zero_norm_le ε a ha (T x)

/-! ### 2. Doubly Regularized State J_N (G_a f) and Simultaneous 6-Domain Regularity -/

def smoothedStaticVector (N : ℝ) (hN : 0 < N) (a : ℝ) (ha : 0 ≤ a) (f : Hilbert) : Hilbert :=
  action ε hε h N hN (Ga a ha 0 f)

theorem smoothedStaticVector_eq_gaussian_resolvent (N : ℝ) (hN : 0 < N)
    (a : ℝ) (ha : 0 ≤ a) (f : Hilbert) :
    smoothedStaticVector ε hε h N hN a ha f =
      Ga a ha 0 (action ε hε h N hN f) :=
  resolvent_gaussian_commute ε hε h N hN a ha 0 f

theorem smoothedStaticVector_norm_le (N : ℝ) (hN : 0 < N)
    (a : ℝ) (ha : 0 ≤ a) (f : Hilbert) :
    ‖smoothedStaticVector ε hε h N hN a ha f‖ ≤ ‖f‖ :=
  (action_norm ε hε h N hN (Ga a ha 0 f)).trans (gaussian_zero_norm_le ε a ha f)

theorem smoothedStaticVector_mem_radial_domain (N : ℝ) (hN : 0 < N)
    (a : ℝ) (ha : 0 ≤ a) (f : Hilbert) :
    smoothedStaticVector ε hε h N hN a ha f ∈ (Kr).domain :=
  radial_domain ε hε h N hN (Ga a ha 0 f)

theorem smoothedStaticVector_radial_apply (N : ℝ) (hN : 0 < N)
    (a : ℝ) (ha : 0 ≤ a) (f : Hilbert) :
    Kr ⟨smoothedStaticVector ε hε h N hN a ha f,
      smoothedStaticVector_mem_radial_domain ε hε h N hN a ha f⟩ =
      Ga a ha 0 (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f) :=
  (resolvent_radial_apply_eq_yosida ε hε h N hN (Ga a ha 0 f)).trans
    (yosida_gaussian_commute ε hε h N hN a ha 0 f)

theorem smoothedStaticVector_mem_root_domain (N : ℝ) (hN : 0 < N)
    (a : ℝ) (ha : 0 ≤ a) (f : Hilbert) :
    smoothedStaticVector ε hε h N hN a ha f ∈ (Kroot).domain :=
  action_root_domain ε hε h N hN (Ga a ha 0 f)

theorem smoothedStaticVector_root_apply (N : ℝ) (hN : 0 < N)
    (a : ℝ) (ha : 0 ≤ a) (f : Hilbert) :
    Kroot ⟨smoothedStaticVector ε hε h N hN a ha f,
      smoothedStaticVector_mem_root_domain ε hε h N hN a ha f⟩ =
      Ga a ha 0 (rootAction ε hε h N hN f) := by
  have hg : (smoothedStaticVector ε hε h N hN a ha f,
      rootAction ε hε h N hN (Ga a ha 0 f)) ∈ (Kroot).graph :=
    root_graph ε hε h N hN (Ga a ha 0 f)
  exact ((Kroot).mem_graph_snd_inj'
    ((Kroot).mem_graph ⟨smoothedStaticVector ε hε h N hN a ha f,
      smoothedStaticVector_mem_root_domain ε hε h N hN a ha f⟩) hg rfl).trans
    (rootAction_gaussian_commute ε hε h N hN a ha 0 f)

theorem smoothedStaticVector_mem_clockOperator_domain_of_pos (N : ℝ) (hN : 0 < N)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    smoothedStaticVector ε hε h N hN a ha.le f ∈ (clockOperator ε hε).domain :=
  resolvent_clockOperator_domain ε hε h N hN (Ga a ha.le 0 f)
    (gaussian_mem_clockOperator_domain_of_pos ε hε a ha 0 f)

theorem smoothedStaticVector_clockOperator_apply_of_pos (N : ℝ) (hN : 0 < N)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    clockOperator ε hε ⟨smoothedStaticVector ε hε h N hN a ha.le f,
      smoothedStaticVector_mem_clockOperator_domain_of_pos ε hε h N hN a ha f⟩ =
      action ε hε h N hN
        (clockOperator ε hε ⟨Ga a ha.le 0 f,
          gaussian_mem_clockOperator_domain_of_pos ε hε a ha 0 f⟩) :=
  resolvent_clockOperator_commute ε hε h N hN (Ga a ha.le 0 f)
    (gaussian_mem_clockOperator_domain_of_pos ε hε a ha 0 f)

theorem smoothedStaticVector_mem_clockHalf_domain_of_pos (N : ℝ) (hN : 0 < N)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    smoothedStaticVector ε hε h N hN a ha.le f ∈ (clockHalf ε).domain :=
  resolvent_clockHalf_domain ε hε h N hN (Ga a ha.le 0 f)
    (gaussian_mem_clockHalf_domain_of_pos ε hε a ha 0 f)

include hb hh in
theorem smoothedStaticVector_mem_static_domain (N : ℝ) (hN : 0 < N)
    (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) :
    smoothedStaticVector ε hε h N hN a ha (x : Hilbert) ∈ (T).domain :=
  static_resolvent_domain ε hε h N hN hb hh
    (Ga a ha 0 (x : Hilbert)) (static_domain ε hε a ha h 0 x)

include hb hh in
theorem smoothedStaticVector_five_domains (N : ℝ) (hN : 0 < N)
    (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) :
    smoothedStaticVector ε hε h N hN a ha (x : Hilbert) ∈ (T).domain ∧
      smoothedStaticVector ε hε h N hN a ha (x : Hilbert) ∈ (Kr).domain ∧
      smoothedStaticVector ε hε h N hN a ha (x : Hilbert) ∈ (clockHalf ε).domain ∧
      smoothedStaticVector ε hε h N hN a ha (x : Hilbert) ∈ (Tstat).domain ∧
      smoothedStaticVector ε hε h N hN a ha (x : Hilbert) ∈ (Kroot).domain :=
  KFCausalClockFloorRadialResolventStaticRadialCore.resolvent_maps_static_to_static_radial_clockHalf
    ε hε h N hN hb hh (Ga a ha 0 (x : Hilbert)) (static_domain ε hε a ha h 0 x)

include hb hh in
theorem smoothedStaticVector_six_domains_of_pos (N : ℝ) (hN : 0 < N)
    (a : ℝ) (ha : 0 < a) (x : (T).domain) :
    smoothedStaticVector ε hε h N hN a ha.le (x : Hilbert) ∈ (T).domain ∧
      smoothedStaticVector ε hε h N hN a ha.le (x : Hilbert) ∈ (Kr).domain ∧
      smoothedStaticVector ε hε h N hN a ha.le (x : Hilbert) ∈ (clockOperator ε hε).domain ∧
      smoothedStaticVector ε hε h N hN a ha.le (x : Hilbert) ∈ (clockHalf ε).domain ∧
      smoothedStaticVector ε hε h N hN a ha.le (x : Hilbert) ∈ (Tstat).domain ∧
      smoothedStaticVector ε hε h N hN a ha.le (x : Hilbert) ∈ (Kroot).domain := by
  have h5 := smoothedStaticVector_five_domains ε hε h hb hh N hN a ha.le x
  exact ⟨h5.1, h5.2.1,
    smoothedStaticVector_mem_clockOperator_domain_of_pos ε hε h N hN a ha (x : Hilbert),
    h5.2.2.1, h5.2.2.2.1, h5.2.2.2.2⟩

include hb hh in
theorem smoothedYosida_four_domains_of_pos (N : ℝ) (hN : 0 < N)
    (a : ℝ) (ha : 0 < a) (x : (T).domain) :
    KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (Ga a ha.le 0 (x : Hilbert)) ∈
        (T).domain ∧
      KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (Ga a ha.le 0 (x : Hilbert)) ∈
        (clockOperator ε hε).domain ∧
      KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (Ga a ha.le 0 (x : Hilbert)) ∈
        (clockHalf ε).domain ∧
      KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (Ga a ha.le 0 (x : Hilbert)) ∈
        (Tstat).domain := by
  have h3 := KFCausalClockFloorRadialResolventStaticRadialCore.yosida_maps_static_to_static_clockHalf
    ε hε h N hN hb hh (Ga a ha.le 0 (x : Hilbert)) (static_domain ε hε a ha.le h 0 x)
  have hC := KFCausalClockFloorRadialResolventClockCommutation.yosida_clockOperator_domain
    ε hε h N hN (Ga a ha.le 0 (x : Hilbert))
    (gaussian_mem_clockOperator_domain_of_pos ε hε a ha 0 (x : Hilbert))
  exact ⟨h3.1, hC, h3.2.1, h3.2.2⟩

/-! ### 3. Equivariance of the Static-Radial Commutator under Gaussian Smoothing -/

def staticCommutator (N : ℝ) (hN : 0 < N) (x : (T).domain) : Hilbert :=
  commutatorVector ε hε h N hN hh 0 0 0 (x : Hilbert)
    (TB0 (domainFormLift ε hε h hb hh 0 0 0 x))

theorem staticOperator_apply_resolvent_eq_add_staticCommutator
    (N : ℝ) (hN : 0 < N) (x : (T).domain) :
    T ⟨action ε hε h N hN (x : Hilbert),
        static_resolvent_domain ε hε h N hN hb hh (x : Hilbert) x.property⟩ =
      action ε hε h N hN (T x) + staticCommutator ε hε h hb hh N hN x :=
  staticOperator_resolvent_apply ε hε h N hN hb hh 0 0 0 x

theorem smoothedStatic_operator_apply_via_gaussian_point
    (N : ℝ) (hN : 0 < N) (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) :
    T ⟨smoothedStaticVector ε hε h N hN a ha (x : Hilbert),
        smoothedStaticVector_mem_static_domain ε hε h hb hh N hN a ha x⟩ =
      Ga a ha 0 (action ε hε h N hN (T x)) +
        staticCommutator ε hε h hb hh N hN (gaussianStaticPoint ε hε h a ha x) := by
  have hp := staticOperator_apply_resolvent_eq_add_staticCommutator ε hε h hb hh N hN
    (gaussianStaticPoint ε hε h a ha x)
  rw [gaussianStaticPoint_apply, resolvent_gaussian_commute] at hp
  exact hp

theorem smoothedStatic_operator_apply_eq_gaussian_of_resolvent
    (N : ℝ) (hN : 0 < N) (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) :
    T ⟨smoothedStaticVector ε hε h N hN a ha (x : Hilbert),
        smoothedStaticVector_mem_static_domain ε hε h hb hh N hN a ha x⟩ =
      Ga a ha 0
        (T ⟨action ε hε h N hN (x : Hilbert),
          static_resolvent_domain ε hε h N hN hb hh (x : Hilbert) x.property⟩) := by
  let xJ : (T).domain :=
    ⟨action ε hε h N hN (x : Hilbert),
      static_resolvent_domain ε hε h N hN hb hh (x : Hilbert) x.property⟩
  have hg : (Ga a ha 0 (xJ : Hilbert), Ga a ha 0 (T xJ)) ∈ (T).graph :=
    static_graph ε hε a ha h 0 (xJ : Hilbert) (T xJ) ((T).mem_graph xJ)
  have hf : smoothedStaticVector ε hε h N hN a ha (x : Hilbert) = Ga a ha 0 (xJ : Hilbert) :=
    smoothedStaticVector_eq_gaussian_resolvent ε hε h N hN a ha (x : Hilbert)
  exact (T).mem_graph_snd_inj'
    ((T).mem_graph ⟨smoothedStaticVector ε hε h N hN a ha (x : Hilbert),
      smoothedStaticVector_mem_static_domain ε hε h hb hh N hN a ha x⟩)
    hg hf

theorem smoothedStatic_operator_apply_via_commutator
    (N : ℝ) (hN : 0 < N) (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) :
    T ⟨smoothedStaticVector ε hε h N hN a ha (x : Hilbert),
        smoothedStaticVector_mem_static_domain ε hε h hb hh N hN a ha x⟩ =
      Ga a ha 0 (action ε hε h N hN (T x)) +
        Ga a ha 0 (staticCommutator ε hε h hb hh N hN x) := by
  rw [smoothedStatic_operator_apply_eq_gaussian_of_resolvent ε hε h hb hh N hN a ha x,
    staticOperator_apply_resolvent_eq_add_staticCommutator ε hε h hb hh N hN x, map_add]

theorem staticCommutator_gaussianStaticPoint
    (N : ℝ) (hN : 0 < N) (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) :
    staticCommutator ε hε h hb hh N hN (gaussianStaticPoint ε hε h a ha x) =
      Ga a ha 0 (staticCommutator ε hε h hb hh N hN x) := by
  have h1 := smoothedStatic_operator_apply_via_gaussian_point ε hε h hb hh N hN a ha x
  have h2 := smoothedStatic_operator_apply_via_commutator ε hε h hb hh N hN a ha x
  exact add_left_cancel (h1.symm.trans h2)

theorem staticCommutator_gaussianStaticPoint_norm_le
    (N : ℝ) (hN : 0 < N) (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) :
    ‖staticCommutator ε hε h hb hh N hN (gaussianStaticPoint ε hε h a ha x)‖ ≤
      ‖staticCommutator ε hε h hb hh N hN x‖ := by
  rw [staticCommutator_gaussianStaticPoint]
  exact gaussian_zero_norm_le ε a ha (staticCommutator ε hε h hb hh N hN x)

theorem staticCommutator_norm_bound (N : ℝ) (hN : 0 < N) (x : (T).domain) :
    ‖staticCommutator ε hε h hb hh N hN x‖ ≤
      (3 * (N⁻¹ * (|h| * Real.sqrt (N / ε) * (Real.sqrt ε)⁻¹))) *
        Real.sqrt (‖T x‖ * ‖(x : Hilbert)‖) +
      (N⁻¹ * (6 * h ^ 2 / ε ^ 2)) * ‖(x : Hilbert)‖ := by
  have heq : staticCommutator ε hε h hb hh N hN x =
      T ⟨action ε hε h N hN (x : Hilbert),
        static_resolvent_domain ε hε h N hN hb hh (x : Hilbert) x.property⟩ -
      action ε hε h N hN (T x) :=
    (staticOperator_resolvent_commutator_eq ε hε h N hN hb hh 0 0 0 x).symm
  rw [heq]
  exact staticOperator_resolvent_commutator_bound ε hε h N hN hb hh 0 0 0 x

theorem staticCommutator_gaussianStaticPoint_bound
    (N : ℝ) (hN : 0 < N) (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) :
    ‖staticCommutator ε hε h hb hh N hN (gaussianStaticPoint ε hε h a ha x)‖ ≤
      (3 * (N⁻¹ * (|h| * Real.sqrt (N / ε) * (Real.sqrt ε)⁻¹))) *
        Real.sqrt (‖T x‖ * ‖(x : Hilbert)‖) +
      (N⁻¹ * (6 * h ^ 2 / ε ^ 2)) * ‖(x : Hilbert)‖ :=
  (staticCommutator_gaussianStaticPoint_norm_le ε hε h hb hh N hN a ha x).trans
    (staticCommutator_norm_bound ε hε h hb hh N hN x)

theorem smoothedStatic_operator_norm_le
    (N : ℝ) (hN : 0 < N) (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) :
    ‖T ⟨smoothedStaticVector ε hε h N hN a ha (x : Hilbert),
        smoothedStaticVector_mem_static_domain ε hε h hb hh N hN a ha x⟩‖ ≤
      ‖T ⟨action ε hε h N hN (x : Hilbert),
        static_resolvent_domain ε hε h N hN hb hh (x : Hilbert) x.property⟩‖ := by
  rw [smoothedStatic_operator_apply_eq_gaussian_of_resolvent ε hε h hb hh N hN a ha x]
  exact gaussian_zero_norm_le ε a ha _

/-! ### 4. Strong Convergence as a → 0, as N → ∞, and Diagonal 6-Domain Graph Core -/

theorem smoothedStaticVector_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (N : ℝ) (hN : 0 < N) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hz : Tendsto a l (𝓝 0)) (f : Hilbert) :
    Tendsto (fun i => smoothedStaticVector ε hε h N hN (a i) (ha i) f) l
      (𝓝 (action ε hε h N hN f)) := by
  have he : (fun i => smoothedStaticVector ε hε h N hN (a i) (ha i) f) =
      fun i => Ga (a i) (ha i) 0 (action ε hε h N hN f) := by
    funext i
    exact smoothedStaticVector_eq_gaussian_resolvent ε hε h N hN (a i) (ha i) f
  rw [he]
  exact action_tendsto ε 0 a ha hz (action ε hε h N hN f)

theorem smoothedStatic_operator_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (N : ℝ) (hN : 0 < N) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hz : Tendsto a l (𝓝 0)) (x : (T).domain) :
    Tendsto (fun i =>
      T ⟨smoothedStaticVector ε hε h N hN (a i) (ha i) (x : Hilbert),
        smoothedStaticVector_mem_static_domain ε hε h hb hh N hN (a i) (ha i) x⟩) l
      (𝓝 (T ⟨action ε hε h N hN (x : Hilbert),
        static_resolvent_domain ε hε h N hN hb hh (x : Hilbert) x.property⟩)) := by
  have he : (fun i =>
      T ⟨smoothedStaticVector ε hε h N hN (a i) (ha i) (x : Hilbert),
        smoothedStaticVector_mem_static_domain ε hε h hb hh N hN (a i) (ha i) x⟩) =
      fun i => Ga (a i) (ha i) 0
        (T ⟨action ε hε h N hN (x : Hilbert),
          static_resolvent_domain ε hε h N hN hb hh (x : Hilbert) x.property⟩) := by
    funext i
    exact smoothedStatic_operator_apply_eq_gaussian_of_resolvent ε hε h hb hh N hN (a i) (ha i) x
  rw [he]
  exact action_tendsto ε 0 a ha hz _

theorem staticCommutator_gaussian_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (N : ℝ) (hN : 0 < N) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hz : Tendsto a l (𝓝 0)) (x : (T).domain) :
    Tendsto (fun i =>
      staticCommutator ε hε h hb hh N hN (gaussianStaticPoint ε hε h (a i) (ha i) x)) l
      (𝓝 (staticCommutator ε hε h hb hh N hN x)) := by
  have he : (fun i =>
      staticCommutator ε hε h hb hh N hN (gaussianStaticPoint ε hε h (a i) (ha i) x)) =
      fun i => Ga (a i) (ha i) 0 (staticCommutator ε hε h hb hh N hN x) := by
    funext i
    exact staticCommutator_gaussianStaticPoint ε hε h hb hh N hN (a i) (ha i) x
  rw [he]
  exact action_tendsto ε 0 a ha hz _

theorem smoothedStatic_radial_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (N : ℝ) (hN : 0 < N) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hz : Tendsto a l (𝓝 0)) (f : Hilbert) :
    Tendsto (fun i =>
      Kr ⟨smoothedStaticVector ε hε h N hN (a i) (ha i) f,
        smoothedStaticVector_mem_radial_domain ε hε h N hN (a i) (ha i) f⟩) l
      (𝓝 (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f)) := by
  have he : (fun i =>
      Kr ⟨smoothedStaticVector ε hε h N hN (a i) (ha i) f,
        smoothedStaticVector_mem_radial_domain ε hε h N hN (a i) (ha i) f⟩) =
      fun i => Ga (a i) (ha i) 0 (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f) := by
    funext i
    exact smoothedStaticVector_radial_apply ε hε h N hN (a i) (ha i) f
  rw [he]
  exact action_tendsto ε 0 a ha hz _

theorem smoothedStatic_root_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (N : ℝ) (hN : 0 < N) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hz : Tendsto a l (𝓝 0)) (f : Hilbert) :
    Tendsto (fun i =>
      Kroot ⟨smoothedStaticVector ε hε h N hN (a i) (ha i) f,
        smoothedStaticVector_mem_root_domain ε hε h N hN (a i) (ha i) f⟩) l
      (𝓝 (rootAction ε hε h N hN f)) := by
  have he : (fun i =>
      Kroot ⟨smoothedStaticVector ε hε h N hN (a i) (ha i) f,
        smoothedStaticVector_mem_root_domain ε hε h N hN (a i) (ha i) f⟩) =
      fun i => Ga (a i) (ha i) 0 (rootAction ε hε h N hN f) := by
    funext i
    exact smoothedStaticVector_root_apply ε hε h N hN (a i) (ha i) f
  rw [he]
  exact action_tendsto ε 0 a ha hz _

theorem smoothedStatic_radial_limit_at_fixed_width
    (a : ℝ) (ha : 0 ≤ a) (x : (T).domain) :
    Tendsto (fun n : ℕ =>
      T ⟨smoothedStaticVector ε hε h ((n : ℝ) + 1) (by positivity) a ha (x : Hilbert),
        smoothedStaticVector_mem_static_domain ε hε h hb hh
          ((n : ℝ) + 1) (by positivity) a ha x⟩)
      atTop (𝓝 (Ga a ha 0 (T x))) := by
  have ht := staticOperator_resolvent_tendsto ε hε h hb hh 0 0 0
    (gaussianStaticPoint ε hε h a ha x)
  rw [gaussianStaticPoint_apply] at ht
  exact ht

private theorem gaussian_contraction_Sequence_tendsto_of_tendsto
    (u : ℕ → Hilbert) (v : Hilbert) (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n : ℕ => Ga (((n : ℝ) + 1)⁻¹) (by positivity) 0 (u n)) atTop (𝓝 v) := by
  have h1 : Tendsto (fun n : ℕ =>
      ‖Ga (((n : ℝ) + 1)⁻¹) (by positivity) 0 (u n - v)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _)
      (fun n => gaussian_zero_norm_le ε (((n : ℝ) + 1)⁻¹) (by positivity) (u n - v))
      (tendsto_iff_norm_sub_tendsto_zero.mp hu)
  have h2 : Tendsto (fun n : ℕ =>
      Ga (((n : ℝ) + 1)⁻¹) (by positivity) 0 (u n - v)) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using h1)
  have h3 := KFCausalClockFloorGaussianGrowingApproximation.sequence_tendsto ε 0 v
  have hsum : Tendsto (fun n : ℕ =>
      Ga (((n : ℝ) + 1)⁻¹) (by positivity) 0 (u n - v) +
        Ga (((n : ℝ) + 1)⁻¹) (by positivity) 0 v) atTop (𝓝 v) := by
    simpa only [zero_add] using h2.add h3
  exact hsum.congr (fun n => by rw [← map_add, sub_add_cancel])

def diagonalSmoothedVector (n : ℕ) (f : Hilbert) : Hilbert :=
  smoothedStaticVector ε hε h ((n : ℝ) + 1) (by positivity)
    (((n : ℝ) + 1)⁻¹) (by positivity) f

include hb hh in
theorem diagonalSmoothedVector_six_domains (n : ℕ) (x : (T).domain) :
    diagonalSmoothedVector ε hε h n (x : Hilbert) ∈ (T).domain ∧
      diagonalSmoothedVector ε hε h n (x : Hilbert) ∈ (Kr).domain ∧
      diagonalSmoothedVector ε hε h n (x : Hilbert) ∈ (clockOperator ε hε).domain ∧
      diagonalSmoothedVector ε hε h n (x : Hilbert) ∈ (clockHalf ε).domain ∧
      diagonalSmoothedVector ε hε h n (x : Hilbert) ∈ (Tstat).domain ∧
      diagonalSmoothedVector ε hε h n (x : Hilbert) ∈ (Kroot).domain :=
  smoothedStaticVector_six_domains_of_pos ε hε h hb hh
    ((n : ℝ) + 1) (by positivity) (((n : ℝ) + 1)⁻¹) (by positivity) x

theorem diagonalSmoothedVector_tendsto (f : Hilbert) :
    Tendsto (fun n : ℕ => diagonalSmoothedVector ε hε h n f) atTop (𝓝 f) := by
  have he : (fun n : ℕ => diagonalSmoothedVector ε hε h n f) =
      fun n : ℕ => Ga (((n : ℝ) + 1)⁻¹) (by positivity) 0
        (action ε hε h ((n : ℝ) + 1) (by positivity) f) := by
    funext n
    exact smoothedStaticVector_eq_gaussian_resolvent ε hε h
      ((n : ℝ) + 1) (by positivity) (((n : ℝ) + 1)⁻¹) (by positivity) f
  rw [he]
  exact gaussian_contraction_Sequence_tendsto_of_tendsto ε
    (fun n : ℕ => action ε hε h ((n : ℝ) + 1) (by positivity) f) f
    (sequence_tendsto ε hε h f)

include hb hh in
theorem diagonalSmoothed_operator_tendsto (x : (T).domain) :
    Tendsto (fun n : ℕ =>
      T ⟨diagonalSmoothedVector ε hε h n (x : Hilbert),
        (diagonalSmoothedVector_six_domains ε hε h hb hh n x).1⟩)
      atTop (𝓝 (T x)) := by
  have he : (fun n : ℕ =>
      T ⟨diagonalSmoothedVector ε hε h n (x : Hilbert),
        (diagonalSmoothedVector_six_domains ε hε h hb hh n x).1⟩) =
      fun n : ℕ => Ga (((n : ℝ) + 1)⁻¹) (by positivity) 0
        (T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (x : Hilbert),
          static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity)
            hb hh (x : Hilbert) x.property⟩) := by
    funext n
    exact smoothedStatic_operator_apply_eq_gaussian_of_resolvent ε hε h hb hh
      ((n : ℝ) + 1) (by positivity) (((n : ℝ) + 1)⁻¹) (by positivity) x
  rw [he]
  exact gaussian_contraction_Sequence_tendsto_of_tendsto ε
    (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (x : Hilbert),
        static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity)
          hb hh (x : Hilbert) x.property⟩)
    (T x)
    (staticOperator_resolvent_tendsto ε hε h hb hh 0 0 0 x)

include hb hh in
theorem diagonalSmoothed_graph_tendsto (x : (T).domain) :
    Tendsto (fun n : ℕ =>
      (diagonalSmoothedVector ε hε h n (x : Hilbert),
        T ⟨diagonalSmoothedVector ε hε h n (x : Hilbert),
          (diagonalSmoothedVector_six_domains ε hε h hb hh n x).1⟩))
      atTop (𝓝 ((x : Hilbert), T x)) :=
  (diagonalSmoothedVector_tendsto ε hε h (x : Hilbert)).prodMk_nhds
    (diagonalSmoothed_operator_tendsto ε hε h hb hh x)

def staticRadialFullClockDomain : Submodule ℂ Hilbert :=
  ((T).domain ⊓ (Kr).domain) ⊓ (clockOperator ε hε).domain

def staticRadialFullClockGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (T).graph ⊓ (staticRadialFullClockDomain ε hε h).comap (LinearMap.fst ℂ Hilbert Hilbert)

include hb hh in
theorem diagonalSmoothed_pair_mem_staticRadialFullClockGraph (n : ℕ) (x : (T).domain) :
    (diagonalSmoothedVector ε hε h n (x : Hilbert),
      T ⟨diagonalSmoothedVector ε hε h n (x : Hilbert),
        (diagonalSmoothedVector_six_domains ε hε h hb hh n x).1⟩) ∈
      staticRadialFullClockGraph ε hε h := by
  have h6 := diagonalSmoothedVector_six_domains ε hε h hb hh n x
  exact ⟨(T).mem_graph ⟨diagonalSmoothedVector ε hε h n (x : Hilbert), h6.1⟩,
    ⟨⟨h6.1, h6.2.1⟩, h6.2.2.1⟩⟩

include hb hh in
theorem static_radial_fullClock_graph_core :
    (staticRadialFullClockGraph ε hε h).topologicalClosure = (T).graph := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ inf_le_left
      (KFCausalClockFloorStaticOperator.selfAdjoint ε hε h).isClosed
  · rintro ⟨f, y⟩ hfy
    let x : (T).domain := ⟨f, LinearPMap.mem_domain_of_mem_graph hfy⟩
    have hy : T x = y := (T).mem_graph_snd_inj' ((T).mem_graph x) hfy rfl
    rw [← hy]
    exact mem_closure_of_tendsto
      (diagonalSmoothed_graph_tendsto ε hε h hb hh x)
      (Eventually.of_forall (fun n =>
        diagonalSmoothed_pair_mem_staticRadialFullClockGraph ε hε h hb hh n x))

#print axioms gaussian_zero_norm_le
#print axioms static_gaussian_commute
#print axioms radial_gaussian_domain
#print axioms radial_gaussian_commute
#print axioms root_gaussian_domain
#print axioms root_gaussian_commute
#print axioms staticRoot_gaussian_graph
#print axioms staticRoot_gaussian_domain
#print axioms staticRoot_gaussian_commute
#print axioms rootAction_gaussian_commute
#print axioms gaussianStaticPoint_coe
#print axioms gaussianStaticPoint_apply
#print axioms gaussianStaticPoint_norm_le
#print axioms gaussianStaticPoint_apply_norm_le
#print axioms smoothedStaticVector_eq_gaussian_resolvent
#print axioms smoothedStaticVector_norm_le
#print axioms smoothedStaticVector_mem_radial_domain
#print axioms smoothedStaticVector_radial_apply
#print axioms smoothedStaticVector_mem_root_domain
#print axioms smoothedStaticVector_root_apply
#print axioms smoothedStaticVector_mem_clockOperator_domain_of_pos
#print axioms smoothedStaticVector_clockOperator_apply_of_pos
#print axioms smoothedStaticVector_mem_clockHalf_domain_of_pos
#print axioms smoothedStaticVector_mem_static_domain
#print axioms smoothedStaticVector_five_domains
#print axioms smoothedStaticVector_six_domains_of_pos
#print axioms smoothedYosida_four_domains_of_pos
#print axioms staticOperator_apply_resolvent_eq_add_staticCommutator
#print axioms smoothedStatic_operator_apply_via_gaussian_point
#print axioms smoothedStatic_operator_apply_eq_gaussian_of_resolvent
#print axioms smoothedStatic_operator_apply_via_commutator
#print axioms staticCommutator_gaussianStaticPoint
#print axioms staticCommutator_gaussianStaticPoint_norm_le
#print axioms staticCommutator_norm_bound
#print axioms staticCommutator_gaussianStaticPoint_bound
#print axioms smoothedStatic_operator_norm_le
#print axioms smoothedStaticVector_tendsto
#print axioms smoothedStatic_operator_tendsto
#print axioms staticCommutator_gaussian_tendsto
#print axioms smoothedStatic_radial_tendsto
#print axioms smoothedStatic_root_tendsto
#print axioms smoothedStatic_radial_limit_at_fixed_width
#print axioms diagonalSmoothedVector_six_domains
#print axioms diagonalSmoothedVector_tendsto
#print axioms diagonalSmoothed_operator_tendsto
#print axioms diagonalSmoothed_graph_tendsto
#print axioms diagonalSmoothed_pair_mem_staticRadialFullClockGraph
#print axioms static_radial_fullClock_graph_core
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticGaussianRadialSmoothing
