/- The displaced-Gaussian static source core is a submodule of the
unconditional common operator domain
(Dom T ∩ Dom Kr ∩ Dom P) ∩ Dom Tres(0) = Dom H(t) ∩ Dom G and of its
intersection with Dom clockHalf for all real couplings m, g, κ. Consequently,
both (Dom T ∩ Dom Kr ∩ Dom P) ∩ Dom Tres(0) and its intersection with
Dom clockHalf are operator graph cores for the maximal static operator T and
for the variational static Hamiltonian at every physical time t. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedMultiOperatorDomain
import UnifiedTheory.Audit.KFCausalClockFloorStaticCommonSourceCore
import UnifiedTheory.Audit.KFCausalClockFloorStaticHamiltonian

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticThreeOperatorCore
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalChargeTransverseSplit (dualPhysical)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorStaticMultiplierForm (symbol symbol_continuous)
open KFCausalClockFloorStaticOperator (operator)
open KFCausalClockFloorDualModulatedDomain (formVector_dual formVector_embedding)
open KFCausalClockFloorDualGaussian (weight weight_memLp weight_ne_zero)
open KFCausalClockFloorStaticOperatorGaussianWeight (symbol_weight_memLp)
open KFCausalClockFloorDisplacedStates (rawState)
open KFCausalChargeDualDisplacement
  (displacementParameter clockParameter displacementParameter_clock)
open KFCausalUnitaryRealMultiplier (realPullback realPullback_graph)
open KFCausalClockFloorUnconditionalTwoTimeEvolution (commonOperatorDomain)
open KFCausalClockFloorDisplacedMultiOperatorDomain
  (rawState_mem_commonOperatorDomain rawState_clockHalf_domain)

private theorem restricted_multiplier_core {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure E))
    (v : E → ℝ) (hv : Measurable v) (w : E → ℂ) (hw : MemLp w 2)
    (hvw : MemLp (fun x => (v x : ℂ) * w x) 2) (hn : ∀ x, w x ≠ 0)
    (S : Submodule ℂ H)
    (hS : ∀ k, Ω.symm (KFCausalModulatedLpTotality.state w hw k) ∈ S) :
    ((realPullback Ω v hv).graph ⊓ S.comap (LinearMap.fst ℂ H H)).topologicalClosure =
      (realPullback Ω v hv).graph := by
  let K := (realPullback Ω v hv).graph ⊓ S.comap (LinearMap.fst ℂ H H)
  let R := (Ω.symm : Lp ℂ 2 (volume : Measure E) →L[ℂ] H).prodMap
    (Ω.symm : Lp ℂ 2 (volume : Measure E) →L[ℂ] H)
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ inf_le_left
      (KFCausalRealMultiplierSelfAdjoint.realPullback_selfAdjoint Ω v hv).isClosed
  · have hp : Submodule.span ℂ (Set.range (KFCausalModulatedGraphCore.packet v w hw hvw)) ≤
        K.topologicalClosure.comap R.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      apply K.le_topologicalClosure
      refine ⟨?_, hS k⟩
      change (Ω.symm (KFCausalModulatedLpTotality.state w hw k),
        Ω.symm (KFCausalModulatedLpTotality.state (fun x => (v x : ℂ) * w x) hvw k)) ∈
          (realPullback Ω v hv).graph
      apply (realPullback_graph Ω v hv _ _).mpr
      have h := (KFCausalMultiplierGraphCoordinates.graph_iff v hv _ _).mp
        (KFCausalModulatedGraphCore.packet_mem_graph v hv w hw hvw k)
      simpa only [LinearIsometryEquiv.apply_symm_apply] using h
    have hc := Submodule.topologicalClosure_minimal _ hp
      (K.isClosed_topologicalClosure.preimage R.continuous)
    rw [KFCausalModulatedGraphCore.graph_core v hv w hw hvw hn] at hc
    rintro ⟨f, g⟩ hfg
    have hg : (Ω f, Ω g) ∈ KFCausalMultiplierGraphCoordinates.graph v hv :=
      (KFCausalMultiplierGraphCoordinates.graph_iff v hv _ _).mpr
        ((realPullback_graph Ω v hv f g).mp hfg)
    have hh := hc hg
    change (Ω.symm (Ω f), Ω.symm (Ω g)) ∈ K.topologicalClosure at hh
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hh

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g κ t : ℝ) (a : ℝ) (ha : 0 < a)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "T" => operator ε hε h
local notation "Kr" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "Pot" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g κ
local notation "Tham" => KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw m g κ t

def packet (k : Joint 5 1) : Hilbert :=
  dualPhysical.symm
    (KFCausalModulatedLpTotality.state (weight ε a h) (weight_memLp ε a h hε ha hh) k)

def sourceCore : Submodule ℂ Hilbert :=
  Submodule.span ℂ (Set.range (packet ε hε h hh a ha))

include hb in
theorem packet_eq_rawState (k : Joint 5 1) :
    packet ε hε h hh a ha k =
      rawState ε a h hε ha hh (displacementParameter h k) (clockParameter k) := by
  apply dualPhysical.injective
  rw [packet, LinearIsometryEquiv.apply_symm_apply]
  have he := formVector_dual ε a h hε ha hh hw 0 0 0 0 k
  rw [formVector_embedding] at he
  exact he.symm

theorem packet_mem_commonOperatorDomain (k : Joint 5 1) :
    packet ε hε h hh a ha k ∈ commonOperatorDomain ε hε h hh hb m g κ := by
  rw [packet_eq_rawState ε hε h hh hb a ha k]
  exact rawState_mem_commonOperatorDomain ε a h hε ha hh hb
    (displacementParameter h k) (clockParameter k) (displacementParameter_clock h k) m g κ

include hb in
theorem packet_mem_clockHalf_domain (k : Joint 5 1) :
    packet ε hε h hh a ha k ∈ (clockHalf ε).domain := by
  rw [packet_eq_rawState ε hε h hh hb a ha k]
  exact rawState_clockHalf_domain ε a h hε ha hh hb
    (displacementParameter h k) (clockParameter k) (displacementParameter_clock h k)

theorem packet_mem_commonOperatorClockDomain (k : Joint 5 1) :
    packet ε hε h hh a ha k ∈
      commonOperatorDomain ε hε h hh hb m g κ ⊓ (clockHalf ε).domain :=
  ⟨packet_mem_commonOperatorDomain ε hε h hh hb m g κ a ha k,
    packet_mem_clockHalf_domain ε hε h hh hb a ha k⟩

theorem sourceCore_le_commonOperatorClockDomain :
    sourceCore ε hε h hh a ha ≤
      commonOperatorDomain ε hε h hh hb m g κ ⊓ (clockHalf ε).domain := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact packet_mem_commonOperatorClockDomain ε hε h hh hb m g κ a ha k

theorem sourceCore_le_commonOperatorDomain :
    sourceCore ε hε h hh a ha ≤ commonOperatorDomain ε hε h hh hb m g κ :=
  (sourceCore_le_commonOperatorClockDomain ε hε h hh hb m g κ a ha).trans inf_le_left

def sourceStaticGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (T).graph ⊓ (sourceCore ε hε h hh a ha).comap (LinearMap.fst ℂ Hilbert Hilbert)

def commonOperatorStaticGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (T).graph ⊓ (commonOperatorDomain ε hε h hh hb m g κ).comap (LinearMap.fst ℂ Hilbert Hilbert)

def commonOperatorClockStaticGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (T).graph ⊓
    (commonOperatorDomain ε hε h hh hb m g κ ⊓ (clockHalf ε).domain).comap
      (LinearMap.fst ℂ Hilbert Hilbert)

def threeOperatorStaticGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (T).graph ⊓
    ((T).domain ⊓ (Kr).domain ⊓ (Pot).domain).comap (LinearMap.fst ℂ Hilbert Hilbert)

def commonOperatorStaticHamiltonianGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (Tham).graph ⊓ (commonOperatorDomain ε hε h hh hb m g κ).comap (LinearMap.fst ℂ Hilbert Hilbert)

def commonOperatorClockStaticHamiltonianGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (Tham).graph ⊓
    (commonOperatorDomain ε hε h hh hb m g κ ⊓ (clockHalf ε).domain).comap
      (LinearMap.fst ℂ Hilbert Hilbert)

theorem source_static_graph_core :
    (sourceStaticGraph ε hε h hh a ha).topologicalClosure = (T).graph :=
  restricted_multiplier_core dualPhysical (symbol ε h)
    (symbol_continuous ε hε h).measurable (weight ε a h)
    (weight_memLp ε a h hε ha hh) (symbol_weight_memLp ε a h hε ha hh)
    (weight_ne_zero ε a h hε hh) (sourceCore ε hε h hh a ha)
    (fun k => Submodule.subset_span ⟨k, rfl⟩)

theorem common_operator_clock_static_graph_core :
    (commonOperatorClockStaticGraph ε hε h hh hb m g κ).topologicalClosure = (T).graph :=
  restricted_multiplier_core dualPhysical (symbol ε h)
    (symbol_continuous ε hε h).measurable (weight ε 1 h)
    (weight_memLp ε 1 h hε zero_lt_one hh) (symbol_weight_memLp ε 1 h hε zero_lt_one hh)
    (weight_ne_zero ε 1 h hε hh)
    (commonOperatorDomain ε hε h hh hb m g κ ⊓ (clockHalf ε).domain)
    (packet_mem_commonOperatorClockDomain ε hε h hh hb m g κ 1 zero_lt_one)

theorem common_operator_static_graph_core :
    (commonOperatorStaticGraph ε hε h hh hb m g κ).topologicalClosure = (T).graph :=
  restricted_multiplier_core dualPhysical (symbol ε h)
    (symbol_continuous ε hε h).measurable (weight ε 1 h)
    (weight_memLp ε 1 h hε zero_lt_one hh) (symbol_weight_memLp ε 1 h hε zero_lt_one hh)
    (weight_ne_zero ε 1 h hε hh)
    (commonOperatorDomain ε hε h hh hb m g κ)
    (packet_mem_commonOperatorDomain ε hε h hh hb m g κ 1 zero_lt_one)

theorem three_operator_static_graph_core :
    (threeOperatorStaticGraph ε hε h hh hb m g κ).topologicalClosure = (T).graph :=
  restricted_multiplier_core dualPhysical (symbol ε h)
    (symbol_continuous ε hε h).measurable (weight ε 1 h)
    (weight_memLp ε 1 h hε zero_lt_one hh) (symbol_weight_memLp ε 1 h hε zero_lt_one hh)
    (weight_ne_zero ε 1 h hε hh)
    ((T).domain ⊓ (Kr).domain ⊓ (Pot).domain)
    (fun k => (packet_mem_commonOperatorDomain ε hε h hh hb m g κ 1 zero_lt_one k).1)

theorem common_operator_static_hamiltonian_graph_core :
    (commonOperatorStaticHamiltonianGraph ε hε h hh hb m g κ t).topologicalClosure =
      (Tham).graph := by
  unfold commonOperatorStaticHamiltonianGraph
  rw [KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hw m g κ t]
  exact common_operator_static_graph_core ε hε h hh hb m g κ

theorem common_operator_clock_static_hamiltonian_graph_core :
    (commonOperatorClockStaticHamiltonianGraph ε hε h hh hb m g κ t).topologicalClosure =
      (Tham).graph := by
  unfold commonOperatorClockStaticHamiltonianGraph
  rw [KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hw m g κ t]
  exact common_operator_clock_static_graph_core ε hε h hh hb m g κ

theorem exists_common_operator_clock_seq_tendsto_static (x : (T).domain) :
    ∃ u : ℕ → Hilbert,
      ∃ hmem : ∀ n, u n ∈ commonOperatorDomain ε hε h hh hb m g κ ⊓ (clockHalf ε).domain,
        Tendsto u atTop (𝓝 (x : Hilbert)) ∧
        Tendsto (fun n => (T) ⟨u n, (hmem n).1.1.1.1⟩) atTop (𝓝 ((T) x)) := by
  have hcl : ((x : Hilbert), (T) x) ∈
      closure (commonOperatorClockStaticGraph ε hε h hh hb m g κ : Set (Hilbert × Hilbert)) := by
    change ((x : Hilbert), (T) x) ∈
      (commonOperatorClockStaticGraph ε hε h hh hb m g κ).topologicalClosure
    rw [common_operator_clock_static_graph_core ε hε h hh hb m g κ]
    exact (T).mem_graph x
  let hseq := mem_closure_iff_seq_limit.mp hcl
  let p := Classical.choose hseq
  have hp := Classical.choose_spec hseq
  have hmem : ∀ n, (p n).1 ∈ commonOperatorDomain ε hε h hh hb m g κ ⊓ (clockHalf ε).domain :=
    fun n => (hp.1 n).2
  refine ⟨fun n => (p n).1, hmem, ?_, ?_⟩
  · exact (continuous_fst.tendsto ((x : Hilbert), (T) x)).comp hp.2
  · have hval : ∀ n, (T) ⟨(p n).1, (hmem n).1.1.1.1⟩ = (p n).2 := fun n =>
      (T).mem_graph_snd_inj' ((T).mem_graph ⟨(p n).1, (hmem n).1.1.1.1⟩) (hp.1 n).1 rfl
    simp_rw [hval]
    exact (continuous_snd.tendsto ((x : Hilbert), (T) x)).comp hp.2

#print axioms packet_eq_rawState
#print axioms packet_mem_commonOperatorDomain
#print axioms packet_mem_clockHalf_domain
#print axioms packet_mem_commonOperatorClockDomain
#print axioms sourceCore_le_commonOperatorClockDomain
#print axioms sourceCore_le_commonOperatorDomain
#print axioms source_static_graph_core
#print axioms common_operator_clock_static_graph_core
#print axioms common_operator_static_graph_core
#print axioms three_operator_static_graph_core
#print axioms common_operator_static_hamiltonian_graph_core
#print axioms common_operator_clock_static_hamiltonian_graph_core
#print axioms exists_common_operator_clock_seq_tendsto_static
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticThreeOperatorCore
