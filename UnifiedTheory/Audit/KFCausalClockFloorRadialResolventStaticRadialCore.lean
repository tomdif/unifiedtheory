/- Unconditional radial-resolvent smoothing, graph-core approximation, and
joint domain invariance on the maximal static and radial operator domains:
1. For every x ∈ Dom(T) and N > 0, both J_N x and M_N x = K_rad(J_N x) lie in
   Dom(T) ∩ Dom(clockHalf ε), and J_N x lies in
   Dom(T) ∩ Dom(K_rad) ∩ Dom(clockHalf ε) ∩ Dom(T_root) ∩ Dom(K_root).
2. The radial resolvent sequence x_n = J_{n+1} x ∈ Dom(T) ∩ Dom(K_rad) ∩ Dom(clockHalf ε)
   converges to x simultaneously in the Hilbert, T, T_root, and clockHalf ε
   norms with explicit O(N^{-1/2}) commutator rate, proving constructively that
   Dom(T) ∩ Dom(K_rad) and Dom(T) ∩ Dom(K_rad) ∩ Dom(clockHalf ε) are operator
   graph cores for T (and for the variational static Hamiltonian at every time t).
3. On Dom(T) ∩ Dom(K_rad), both J_N and M_N preserve
   Dom(T) ∩ Dom(K_rad) ∩ Dom(clockHalf ε), and as n → ∞ the sequence J_{n+1} x
   converges simultaneously in Hilbert, T, K_rad, T + e^{2t} K_rad, clockHalf ε,
   and T_root norms. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticDomain
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventClockCore
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticRadialCore
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaDomain (operator)
open KFCausalClockFloorRadialResolventRegularizer (action radial_domain radial_graph sequence_tendsto)
open KFCausalClockFloorRadialResolventRoot (action_root_domain)
open KFCausalClockFloorRadialResolventOperator
  (yosida_eq_action_on_graph operator_commute operator_norm_le
    self_sub_action_norm_le operator_sequence_tendsto)
open KFCausalClockFloorRadialResolventClockCommutation
  (resolvent_clockHalf_domain resolvent_clockHalf_commute
    resolvent_clockHalf_norm_le resolvent_clockHalf_tendsto
    yosida_clockHalf_domain yosida_clockHalf_commute)
open KFCausalClockFloorRadialResolventClockCore (static_root_sequence_tendsto)
open KFCausalClockFloorRadialResolventStaticRoot (static_root_domain_action)
open KFCausalClockFloorRadialResolventStaticDomain
  (domainFormLift commutatorVector
    staticOperator_resolvent_graph staticOperator_resolvent_domain
    staticOperator_yosida_domain staticOperator_resolvent_apply
    staticOperator_resolvent_commutator_eq staticOperator_resolvent_commutator_bound
    staticOperator_resolvent_commutator_tendsto staticOperator_resolvent_tendsto)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (static_domain_le_clockHalf_domain residual_form_domain_le_clockHalf_domain)

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi * ε / 3) (hh : h ≠ 0)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "Kr" => operator ε hε h
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "J" => action ε hε h N hN
local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN

/-! ### 1. Unconditional Smoothing from Dom(T) into Dom(T) ∩ Dom(K_rad) ∩ Dom(clockHalf ε) -/

theorem static_domain_subset_clockHalf_domain (f : Hilbert)
    (hf : f ∈ (T).domain) :
    f ∈ (clockHalf ε).domain :=
  static_domain_le_clockHalf_domain ε hε h hf

theorem static_radial_domain_le_clockHalf_domain :
    (T).domain ⊓ (Kr).domain ≤ (clockHalf ε).domain :=
  fun _ hx => static_domain_le_clockHalf_domain ε hε h hx.1

theorem static_radial_domain_inf_clockHalf_eq :
    ((T).domain ⊓ (Kr).domain) ⊓ (clockHalf ε).domain =
      (T).domain ⊓ (Kr).domain :=
  inf_of_le_left (static_radial_domain_le_clockHalf_domain ε hε h)

include hb hh in
theorem static_resolvent_domain (f : Hilbert) (hf : f ∈ (T).domain) :
    J f ∈ (T).domain :=
  staticOperator_resolvent_domain ε hε h N hN hb hh 0 0 0 f hf

include hb hh in
theorem static_yosida_domain (f : Hilbert) (hf : f ∈ (T).domain) :
    M f ∈ (T).domain :=
  staticOperator_yosida_domain ε hε h N hN hb hh 0 0 0 f hf

include hb hh in
theorem resolvent_maps_static_to_static_radial_clockHalf (f : Hilbert)
    (hf : f ∈ (T).domain) :
    J f ∈ (T).domain ∧
      J f ∈ (Kr).domain ∧
      J f ∈ (clockHalf ε).domain ∧
      J f ∈ (Tstat).domain ∧
      J f ∈ (Kroot).domain := by
  have hT : J f ∈ (T).domain := static_resolvent_domain ε hε h N hN hb hh f hf
  have hK : J f ∈ (Kr).domain := radial_domain ε hε h N hN f
  have hC : J f ∈ (clockHalf ε).domain :=
    static_domain_subset_clockHalf_domain ε hε h (J f) hT
  have hR : J f ∈ (Tstat).domain :=
    KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨J f, hT⟩
  have hKr : J f ∈ (Kroot).domain := action_root_domain ε hε h N hN f
  exact ⟨hT, hK, hC, hR, hKr⟩

include hb hh in
theorem resolvent_mem_static_inter_radial_domain (f : Hilbert)
    (hf : f ∈ (T).domain) :
    J f ∈ (T).domain ⊓ (Kr).domain :=
  ⟨static_resolvent_domain ε hε h N hN hb hh f hf, radial_domain ε hε h N hN f⟩

include hb hh in
theorem resolvent_mem_static_radial_clockHalf_domain (f : Hilbert)
    (hf : f ∈ (T).domain) :
    J f ∈ ((T).domain ⊓ (Kr).domain) ⊓ (clockHalf ε).domain :=
  ⟨resolvent_mem_static_inter_radial_domain ε hε h N hN hb hh f hf,
    static_domain_subset_clockHalf_domain ε hε h (J f)
      (static_resolvent_domain ε hε h N hN hb hh f hf)⟩

theorem resolvent_radial_apply_eq_yosida (f : Hilbert) :
    Kr ⟨J f, radial_domain ε hε h N hN f⟩ = M f :=
  (Kr).mem_graph_snd_inj'
    ((Kr).mem_graph ⟨J f, radial_domain ε hε h N hN f⟩)
    (radial_graph ε hε h N hN f) rfl

theorem resolvent_static_clockHalf_commute (f : Hilbert) (hf : f ∈ (T).domain) :
    clockHalf ε ⟨J f,
      resolvent_clockHalf_domain ε hε h N hN f
        (static_domain_subset_clockHalf_domain ε hε h f hf)⟩ =
      J (clockHalf ε ⟨f, static_domain_subset_clockHalf_domain ε hε h f hf⟩) :=
  resolvent_clockHalf_commute ε hε h N hN f
    (static_domain_subset_clockHalf_domain ε hε h f hf)

include hb hh in
theorem yosida_maps_static_to_static_clockHalf (f : Hilbert)
    (hf : f ∈ (T).domain) :
    M f ∈ (T).domain ∧
      M f ∈ (clockHalf ε).domain ∧
      M f ∈ (Tstat).domain := by
  have hT : M f ∈ (T).domain := static_yosida_domain ε hε h N hN hb hh f hf
  have hC : M f ∈ (clockHalf ε).domain :=
    static_domain_subset_clockHalf_domain ε hε h (M f) hT
  have hR : M f ∈ (Tstat).domain :=
    KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨M f, hT⟩
  exact ⟨hT, hC, hR⟩

include hb hh in
theorem yosida_mem_static_inter_clockHalf_domain (f : Hilbert)
    (hf : f ∈ (T).domain) :
    M f ∈ (T).domain ⊓ (clockHalf ε).domain :=
  ⟨static_yosida_domain ε hε h N hN hb hh f hf,
    static_domain_subset_clockHalf_domain ε hε h (M f)
      (static_yosida_domain ε hε h N hN hb hh f hf)⟩

theorem yosida_static_clockHalf_commute (f : Hilbert) (hf : f ∈ (T).domain) :
    clockHalf ε ⟨M f,
      yosida_clockHalf_domain ε hε h N hN f
        (static_domain_subset_clockHalf_domain ε hε h f hf)⟩ =
      M (clockHalf ε ⟨f, static_domain_subset_clockHalf_domain ε hε h f hf⟩) :=
  yosida_clockHalf_commute ε hε h N hN f
    (static_domain_subset_clockHalf_domain ε hε h f hf)

theorem resolvent_residual_radial_clockHalf_domain (m g k t : ℝ) (f : Hilbert)
    (hf : f ∈ (KFCausalClockFloorStaticPotentialOutputClosure.operator
      ε hε h hh hw m g k t).domain) :
    J f ∈ (Kr).domain ∧
      J f ∈ (KFCausalClockFloorStaticPotentialOutputClosure.operator
        ε hε h hh hw m g k t).domain ∧
      J f ∈ (clockHalf ε).domain := by
  have hres := KFCausalClockFloorRadialResolventResidual.domain_intersection_action
    ε hε h N hN hb hh m g k t f hf
  exact ⟨hres.1, hres.2,
    residual_form_domain_le_clockHalf_domain ε hε h hh hb m g k t hres.2⟩

/-! ### 2. Unconditional Graph-Core Theorem for Dom(T) ∩ Dom(K_rad) in Dom(T) -/

def staticRadialDomain : Submodule ℂ Hilbert :=
  (T).domain ⊓ (Kr).domain

def staticRadialClockDomain : Submodule ℂ Hilbert :=
  ((T).domain ⊓ (Kr).domain) ⊓ (clockHalf ε).domain

def staticRadialGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (T).graph ⊓ (staticRadialDomain ε hε h).comap (LinearMap.fst ℂ Hilbert Hilbert)

def staticRadialClockGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (T).graph ⊓ (staticRadialClockDomain ε hε h).comap (LinearMap.fst ℂ Hilbert Hilbert)

def staticHamiltonianRadialGraph (m g k t : ℝ) : Submodule ℂ (Hilbert × Hilbert) :=
  (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw m g k t).graph ⊓
    (staticRadialDomain ε hε h).comap (LinearMap.fst ℂ Hilbert Hilbert)

def staticHamiltonianRadialClockGraph (m g k t : ℝ) : Submodule ℂ (Hilbert × Hilbert) :=
  (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw m g k t).graph ⊓
    (staticRadialClockDomain ε hε h).comap (LinearMap.fst ℂ Hilbert Hilbert)

theorem staticRadialClockDomain_eq_staticRadialDomain :
    staticRadialClockDomain ε hε h = staticRadialDomain ε hε h :=
  static_radial_domain_inf_clockHalf_eq ε hε h

theorem staticRadialClockGraph_eq_staticRadialGraph :
    staticRadialClockGraph ε hε h = staticRadialGraph ε hε h := by
  unfold staticRadialClockGraph staticRadialGraph
  rw [staticRadialClockDomain_eq_staticRadialDomain ε hε h]

theorem resolvent_pair_mem_staticRadialGraph (x : (T).domain) :
    (J (x : Hilbert),
      T ⟨J (x : Hilbert),
        static_resolvent_domain ε hε h N hN hb hh (x : Hilbert) x.property⟩) ∈
      staticRadialGraph ε hε h :=
  ⟨(T).mem_graph ⟨J (x : Hilbert),
      static_resolvent_domain ε hε h N hN hb hh (x : Hilbert) x.property⟩,
    resolvent_mem_static_inter_radial_domain ε hε h N hN hb hh (x : Hilbert) x.property⟩

theorem resolvent_pair_mem_staticRadialClockGraph (x : (T).domain) :
    (J (x : Hilbert),
      T ⟨J (x : Hilbert),
        static_resolvent_domain ε hε h N hN hb hh (x : Hilbert) x.property⟩) ∈
      staticRadialClockGraph ε hε h :=
  ⟨(T).mem_graph ⟨J (x : Hilbert),
      static_resolvent_domain ε hε h N hN hb hh (x : Hilbert) x.property⟩,
    resolvent_mem_static_radial_clockHalf_domain ε hε h N hN hb hh (x : Hilbert) x.property⟩

theorem static_radial_core_commutator_bound (x : (T).domain) :
    ‖T ⟨J (x : Hilbert),
        static_resolvent_domain ε hε h N hN hb hh (x : Hilbert) x.property⟩ -
      J (T x)‖ ≤
      (3 * (N⁻¹ * (|h| * Real.sqrt (N / ε) * (Real.sqrt ε)⁻¹))) *
        Real.sqrt (‖T x‖ * ‖(x : Hilbert)‖) +
      (N⁻¹ * (6 * h ^ 2 / ε ^ 2)) * ‖(x : Hilbert)‖ :=
  staticOperator_resolvent_commutator_bound ε hε h N hN hb hh 0 0 0 x

include hb hh in
theorem static_resolvent_commutator_tendsto (x : (T).domain) :
    Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (x : Hilbert),
        static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity)
          hb hh (x : Hilbert) x.property⟩ -
        action ε hε h ((n : ℝ) + 1) (by positivity) (T x))
      atTop (𝓝 0) :=
  staticOperator_resolvent_commutator_tendsto ε hε h hb hh 0 0 0 x

include hb hh in
theorem static_resolvent_tendsto (x : (T).domain) :
    Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (x : Hilbert),
        static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity)
          hb hh (x : Hilbert) x.property⟩)
      atTop (𝓝 (T x)) :=
  staticOperator_resolvent_tendsto ε hε h hb hh 0 0 0 x

include hb hh in
theorem static_radial_graph_sequence_tendsto (x : (T).domain) :
    Tendsto (fun n : ℕ =>
      (action ε hε h ((n : ℝ) + 1) (by positivity) (x : Hilbert),
        T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (x : Hilbert),
          static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity)
            hb hh (x : Hilbert) x.property⟩))
      atTop (𝓝 ((x : Hilbert), T x)) :=
  (sequence_tendsto ε hε h (x : Hilbert)).prodMk_nhds
    (static_resolvent_tendsto ε hε h hb hh x)

include hb hh in
theorem static_resolvent_simultaneous_tendsto (x : (T).domain) :
    let hC := static_domain_subset_clockHalf_domain ε hε h (x : Hilbert) x.property
    let hR := KFCausalClockFloorStaticOperator.root_domain ε hε h x
    Tendsto (fun n : ℕ =>
      action ε hε h ((n : ℝ) + 1) (by positivity) (x : Hilbert))
      atTop (𝓝 (x : Hilbert)) ∧
    Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (x : Hilbert),
        static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity)
          hb hh (x : Hilbert) x.property⟩)
      atTop (𝓝 (T x)) ∧
    Tendsto (fun n : ℕ =>
      clockHalf ε ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (x : Hilbert),
        resolvent_clockHalf_domain ε hε h ((n : ℝ) + 1) (by positivity)
          (x : Hilbert) hC⟩)
      atTop (𝓝 (clockHalf ε ⟨(x : Hilbert), hC⟩)) ∧
    Tendsto (fun n : ℕ =>
      Tstat ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (x : Hilbert),
        static_root_domain_action ε hε h ((n : ℝ) + 1) (by positivity)
          hb hh (x : Hilbert) hR⟩)
      atTop (𝓝 (Tstat ⟨(x : Hilbert), hR⟩)) :=
  ⟨sequence_tendsto ε hε h (x : Hilbert),
    static_resolvent_tendsto ε hε h hb hh x,
    resolvent_clockHalf_tendsto ε hε h (x : Hilbert)
      (static_domain_subset_clockHalf_domain ε hε h (x : Hilbert) x.property),
    static_root_sequence_tendsto ε hε h hb hh (x : Hilbert)
      (KFCausalClockFloorStaticOperator.root_domain ε hε h x)⟩

include hb hh in
theorem static_radial_graph_core :
    (staticRadialGraph ε hε h).topologicalClosure = (T).graph := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ inf_le_left
      (KFCausalClockFloorStaticOperator.selfAdjoint ε hε h).isClosed
  · rintro ⟨f, y⟩ hfy
    let x : (T).domain := ⟨f, LinearPMap.mem_domain_of_mem_graph hfy⟩
    have hy : T x = y := (T).mem_graph_snd_inj' ((T).mem_graph x) hfy rfl
    rw [← hy]
    exact mem_closure_of_tendsto
      (static_radial_graph_sequence_tendsto ε hε h hb hh x)
      (Eventually.of_forall (fun n =>
        resolvent_pair_mem_staticRadialGraph ε hε h ((n : ℝ) + 1) (by positivity) hb hh x))

include hb hh in
theorem static_radial_clock_graph_core :
    (staticRadialClockGraph ε hε h).topologicalClosure = (T).graph := by
  rw [staticRadialClockGraph_eq_staticRadialGraph ε hε h]
  exact static_radial_graph_core ε hε h hb hh

theorem static_hamiltonian_radial_graph_core (m g k t : ℝ) :
    (staticHamiltonianRadialGraph ε hε h hb hh m g k t).topologicalClosure =
      (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw m g k t).graph := by
  unfold staticHamiltonianRadialGraph
  rw [KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hw m g k t]
  exact static_radial_graph_core ε hε h hb hh

theorem static_hamiltonian_radial_clock_graph_core (m g k t : ℝ) :
    (staticHamiltonianRadialClockGraph ε hε h hb hh m g k t).topologicalClosure =
      (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw m g k t).graph := by
  unfold staticHamiltonianRadialClockGraph
  rw [KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hw m g k t]
  exact static_radial_clock_graph_core ε hε h hb hh

include hb hh in
theorem static_radial_domain_dense :
    Dense (staticRadialDomain ε hε h : Set Hilbert) := by
  have hs : ((T).domain : Set Hilbert) ⊆
      closure (staticRadialDomain ε hε h : Set Hilbert) := by
    intro f hf
    exact mem_closure_of_tendsto (sequence_tendsto ε hε h f)
      (Eventually.of_forall (fun n =>
        resolvent_mem_static_inter_radial_domain
          ε hε h ((n : ℝ) + 1) (by positivity) hb hh f hf))
  intro f
  exact closure_minimal hs isClosed_closure
    ((KFCausalClockFloorStaticOperator.selfAdjoint ε hε h).dense_domain f)

include hb hh in
theorem static_radial_clock_domain_dense :
    Dense (staticRadialClockDomain ε hε h : Set Hilbert) := by
  rw [staticRadialClockDomain_eq_staticRadialDomain ε hε h]
  exact static_radial_domain_dense ε hε h hb hh

/-! ### 3. Unconditional Joint Invariance and Simultaneous Convergence on Dom(T) ∩ Dom(K_rad) -/

theorem yosida_radial_domain_of_radial_domain (f : Hilbert)
    (hK : f ∈ (Kr).domain) :
    M f ∈ (Kr).domain := by
  rw [yosida_eq_action_on_graph ε hε h N hN f (Kr ⟨f, hK⟩) ((Kr).mem_graph ⟨f, hK⟩)]
  exact radial_domain ε hε h N hN (Kr ⟨f, hK⟩)

theorem yosida_radial_apply_of_radial_domain (f : Hilbert)
    (hK : f ∈ (Kr).domain) :
    Kr ⟨M f, yosida_radial_domain_of_radial_domain ε hε h N hN f hK⟩ =
      M (Kr ⟨f, hK⟩) := by
  have heq : M f = J (Kr ⟨f, hK⟩) :=
    yosida_eq_action_on_graph ε hε h N hN f (Kr ⟨f, hK⟩) ((Kr).mem_graph ⟨f, hK⟩)
  have hg : (M f, M (Kr ⟨f, hK⟩)) ∈ (Kr).graph := by
    rw [heq]
    exact radial_graph ε hε h N hN (Kr ⟨f, hK⟩)
  exact (Kr).mem_graph_snd_inj'
    ((Kr).mem_graph ⟨M f, yosida_radial_domain_of_radial_domain ε hε h N hN f hK⟩)
    hg rfl

include hb hh in
theorem resolvent_preserves_static_radial_clockHalf_domain (f : Hilbert)
    (hT : f ∈ (T).domain) (_hK : f ∈ (Kr).domain) :
    J f ∈ (T).domain ∧ J f ∈ (Kr).domain ∧ J f ∈ (clockHalf ε).domain :=
  ⟨static_resolvent_domain ε hε h N hN hb hh f hT,
    radial_domain ε hε h N hN f,
    static_domain_subset_clockHalf_domain ε hε h (J f)
      (static_resolvent_domain ε hε h N hN hb hh f hT)⟩

include hb hh in
theorem yosida_preserves_static_radial_clockHalf_domain (f : Hilbert)
    (hT : f ∈ (T).domain) (hK : f ∈ (Kr).domain) :
    M f ∈ (T).domain ∧ M f ∈ (Kr).domain ∧ M f ∈ (clockHalf ε).domain :=
  ⟨static_yosida_domain ε hε h N hN hb hh f hT,
    yosida_radial_domain_of_radial_domain ε hε h N hN f hK,
    static_domain_subset_clockHalf_domain ε hε h (M f)
      (static_yosida_domain ε hε h N hN hb hh f hT)⟩

include hb hh in
theorem yosida_mem_staticRadialClockDomain (f : Hilbert)
    (hf : f ∈ staticRadialDomain ε hε h) :
    M f ∈ staticRadialClockDomain ε hε h := by
  have hm := yosida_preserves_static_radial_clockHalf_domain ε hε h N hN hb hh f hf.1 hf.2
  exact ⟨⟨hm.1, hm.2.1⟩, hm.2.2⟩

include hb hh in
theorem static_radial_resolvent_weighted_sum_tendsto (t : ℝ) (f : Hilbert)
    (hT : f ∈ (T).domain) (hK : f ∈ (Kr).domain) :
    Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity) hb hh f hT⟩ +
        (Real.exp (2 * t) : ℂ) •
          Kr ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
            radial_domain ε hε h ((n : ℝ) + 1) (by positivity) f⟩)
      atTop (𝓝 (T ⟨f, hT⟩ + (Real.exp (2 * t) : ℂ) • Kr ⟨f, hK⟩)) :=
  (static_resolvent_tendsto ε hε h hb hh ⟨f, hT⟩).add
    ((operator_sequence_tendsto ε hε h ⟨f, hK⟩).const_smul (Real.exp (2 * t) : ℂ))

include hb hh in
theorem static_radial_simultaneous_convergence (t : ℝ) (f : Hilbert)
    (hT : f ∈ (T).domain) (hK : f ∈ (Kr).domain) :
    let hC := static_domain_subset_clockHalf_domain ε hε h f hT
    let hR := KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨f, hT⟩
    Tendsto (fun n : ℕ =>
      action ε hε h ((n : ℝ) + 1) (by positivity) f)
      atTop (𝓝 f) ∧
    Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity) hb hh f hT⟩)
      atTop (𝓝 (T ⟨f, hT⟩)) ∧
    Tendsto (fun n : ℕ =>
      Kr ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        radial_domain ε hε h ((n : ℝ) + 1) (by positivity) f⟩)
      atTop (𝓝 (Kr ⟨f, hK⟩)) ∧
    Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity) hb hh f hT⟩ +
        (Real.exp (2 * t) : ℂ) •
          Kr ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
            radial_domain ε hε h ((n : ℝ) + 1) (by positivity) f⟩)
      atTop (𝓝 (T ⟨f, hT⟩ + (Real.exp (2 * t) : ℂ) • Kr ⟨f, hK⟩)) ∧
    Tendsto (fun n : ℕ =>
      clockHalf ε ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        resolvent_clockHalf_domain ε hε h ((n : ℝ) + 1) (by positivity) f hC⟩)
      atTop (𝓝 (clockHalf ε ⟨f, hC⟩)) ∧
    Tendsto (fun n : ℕ =>
      Tstat ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        static_root_domain_action ε hε h ((n : ℝ) + 1) (by positivity) hb hh f hR⟩)
      atTop (𝓝 (Tstat ⟨f, hR⟩)) :=
  ⟨sequence_tendsto ε hε h f,
    static_resolvent_tendsto ε hε h hb hh ⟨f, hT⟩,
    operator_sequence_tendsto ε hε h ⟨f, hK⟩,
    static_radial_resolvent_weighted_sum_tendsto ε hε h hb hh t f hT hK,
    resolvent_clockHalf_tendsto ε hε h f
      (static_domain_subset_clockHalf_domain ε hε h f hT),
    static_root_sequence_tendsto ε hε h hb hh f
      (KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨f, hT⟩)⟩

#print axioms static_domain_subset_clockHalf_domain
#print axioms static_radial_domain_le_clockHalf_domain
#print axioms static_radial_domain_inf_clockHalf_eq
#print axioms static_resolvent_domain
#print axioms static_yosida_domain
#print axioms resolvent_maps_static_to_static_radial_clockHalf
#print axioms resolvent_mem_static_inter_radial_domain
#print axioms resolvent_mem_static_radial_clockHalf_domain
#print axioms resolvent_radial_apply_eq_yosida
#print axioms resolvent_static_clockHalf_commute
#print axioms yosida_maps_static_to_static_clockHalf
#print axioms yosida_mem_static_inter_clockHalf_domain
#print axioms yosida_static_clockHalf_commute
#print axioms resolvent_residual_radial_clockHalf_domain
#print axioms staticRadialClockDomain_eq_staticRadialDomain
#print axioms staticRadialClockGraph_eq_staticRadialGraph
#print axioms resolvent_pair_mem_staticRadialGraph
#print axioms resolvent_pair_mem_staticRadialClockGraph
#print axioms static_radial_core_commutator_bound
#print axioms static_resolvent_commutator_tendsto
#print axioms static_resolvent_tendsto
#print axioms static_radial_graph_sequence_tendsto
#print axioms static_resolvent_simultaneous_tendsto
#print axioms static_radial_graph_core
#print axioms static_radial_clock_graph_core
#print axioms static_hamiltonian_radial_graph_core
#print axioms static_hamiltonian_radial_clock_graph_core
#print axioms static_radial_domain_dense
#print axioms static_radial_clock_domain_dense
#print axioms yosida_radial_domain_of_radial_domain
#print axioms yosida_radial_apply_of_radial_domain
#print axioms resolvent_preserves_static_radial_clockHalf_domain
#print axioms yosida_preserves_static_radial_clockHalf_domain
#print axioms yosida_mem_staticRadialClockDomain
#print axioms static_radial_resolvent_weighted_sum_tendsto
#print axioms static_radial_simultaneous_convergence
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticRadialCore
