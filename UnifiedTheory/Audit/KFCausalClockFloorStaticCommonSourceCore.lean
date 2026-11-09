/- The maximal static operator has an operator graph core contained in
both the actual full Hamiltonian and growing-operator domains, supplied by
ambient displaced Gaussians in the smaller strip. Density is in the
STATIC operator graph norm only; no joint H/G graph core is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedSecondDomain
import UnifiedTheory.Audit.KFCausalClockFloorStaticOperatorSourceCore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticCommonSourceCore
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalChargeTransverseSplit (dualPhysical)
open KFCausalClockFloorStaticMultiplierForm (symbol symbol_continuous)
open KFCausalClockFloorStaticOperator (operator)
open KFCausalClockFloorDualModulatedDomain
open KFCausalClockFloorDualGaussian (weight weight_memLp weight_ne_zero)
open KFCausalClockFloorStaticOperatorGaussianWeight (symbol_weight_memLp)
open KFCausalClockFloorDisplacedStates (rawState)
open KFCausalChargeDualDisplacement
open KFCausalUnitaryRealMultiplier (realPullback realPullback_graph)

private theorem restricted_multiplier_core {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure E))
    (v : E → ℝ) (hv : Measurable v) (w : E → ℂ) (hw : MemLp w 2)
    (hvw : MemLp (fun x => (v x : ℂ)*w x) 2) (hn : ∀ x, w x ≠ 0)
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
      rintro _ ⟨k,rfl⟩
      apply K.le_topologicalClosure
      refine ⟨?_,hS k⟩
      change (Ω.symm (KFCausalModulatedLpTotality.state w hw k),
        Ω.symm (KFCausalModulatedLpTotality.state (fun x => (v x : ℂ)*w x) hvw k)) ∈
          (realPullback Ω v hv).graph
      apply (realPullback_graph Ω v hv _ _).mpr
      have h := (KFCausalMultiplierGraphCoordinates.graph_iff v hv _ _).mp
        (KFCausalModulatedGraphCore.packet_mem_graph v hv w hw hvw k)
      simpa only [LinearIsometryEquiv.apply_symm_apply] using h
    have hc := Submodule.topologicalClosure_minimal _ hp
      (K.isClosed_topologicalClosure.preimage R.continuous)
    rw [KFCausalModulatedGraphCore.graph_core v hv w hw hvw hn] at hc
    rintro ⟨f,g⟩ hfg
    have hg : (Ω f,Ω g) ∈ KFCausalMultiplierGraphCoordinates.graph v hv :=
      (KFCausalMultiplierGraphCoordinates.graph_iff v hv _ _).mpr
        ((realPullback_graph Ω v hv f g).mp hfg)
    have hh := hc hg
    change (Ω.symm (Ω f),Ω.symm (Ω g)) ∈ K.topologicalClosure at hh
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hh

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g κ t : ℝ)
local notation "hb₀" => KFCausalGaussianVacuumSquare.original_strip ε h hε hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb₀ m g κ t
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb₀ m g κ
local notation "packet" => fun k => dualPhysical.symm
  (KFCausalModulatedLpTotality.state (weight ε a h) (weight_memLp ε a h hε ha hh) k)

include hb in
private theorem packet_eq_raw (k : Joint 5 1) :
    packet k = rawState ε a h hε ha hh (displacementParameter h k) (clockParameter k) := by
  apply dualPhysical.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  have he := formVector_dual ε a h hε ha hh hb₀ 0 0 0 0 k
  rw [formVector_embedding] at he
  exact he.symm

theorem packet_hamiltonian_domain (k : Joint 5 1) : packet k ∈ (H).domain := by
  rw [packet_eq_raw ε a h hε ha hh hb k]
  exact KFCausalClockFloorDisplacedSecondDomain.hamiltonian_domain ε a h hε ha hh hb
    (displacementParameter h k) (clockParameter k) (displacementParameter_clock h k) m g κ t

theorem packet_growing_domain (k : Joint 5 1) : packet k ∈ (G).domain := by
  rw [packet_eq_raw ε a h hε ha hh hb k]
  exact KFCausalClockFloorDisplacedSecondDomain.growing_domain ε a h hε ha hh hb
    (displacementParameter h k) (clockParameter k) (displacementParameter_clock h k) m g κ

def restrictedGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (operator ε hε h).graph ⊓ ((H).domain ⊓ (G).domain).comap (LinearMap.fst ℂ Hilbert Hilbert)

include ha in
theorem operator_common_source_core :
    (restrictedGraph ε h hε hh hb m g κ t).topologicalClosure = (operator ε hε h).graph := by
  exact restricted_multiplier_core dualPhysical (symbol ε h)
    (symbol_continuous ε hε h).measurable (weight ε a h)
    (weight_memLp ε a h hε ha hh) (symbol_weight_memLp ε a h hε ha hh)
    (weight_ne_zero ε a h hε hh) ((H).domain ⊓ (G).domain)
    (fun k => ⟨packet_hamiltonian_domain ε a h hε ha hh hb m g κ t k,
      packet_growing_domain ε a h hε ha hh hb m g κ k⟩)

#print axioms packet_hamiltonian_domain
#print axioms packet_growing_domain
#print axioms operator_common_source_core
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticCommonSourceCore
