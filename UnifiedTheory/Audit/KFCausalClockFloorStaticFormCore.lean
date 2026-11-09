/- The actual full interacting averaged-form sources are a graph core for
the maximal static square-root multiplier. This is density in the static
form norm only. It does not identify the full interacting form with an
intersection of separate maximal forms, or prove a common operator core. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticMultiplierForm
import UnifiedTheory.Audit.KFCausalClockFloorDualModulatedDomain
import UnifiedTheory.Audit.KFCausalModulatedGraphCore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticFormCore
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open KFCausalChargeTransverseSplit (dualPhysical)
open KFCausalClockFloorStaticMultiplierForm
open KFCausalClockFloorDualModulatedDomain
open KFCausalClockFloorDualGaussian (weight weight_memLp weight_ne_zero)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedEnergy
open KFCausalEuclideanFourierUniqueness (modulate)
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
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ t : ℝ)

include hε ha hh hb in
theorem root_weight_memLp :
    MemLp (fun x => (rootSymbol ε h x : ℂ)*weight ε a h x) 2 := by
  have hm := averaged_root_memLp ε hε h (hamiltonian_bound ε h hb) hh 0 0 0 0
    (formVector ε a h hε ha hh hb 0 0 0 0 0)
  apply hm.ae_eq
  filter_upwards [formVector_dual_coe ε a h hε ha hh hb 0 0 0 0 0] with x hx
  simp [modulate] at hx
  rw [hx]

def restrictedGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (rootOperator ε hε h).graph ⊓
    (energyOperator ε hε h (hamiltonian_bound ε h hb) hh m g κ t).domain.comap
      (LinearMap.fst ℂ Hilbert Hilbert)

include ha in
theorem static_form_core :
    (restrictedGraph ε h hε hh hb m g κ t).topologicalClosure =
      (rootOperator ε hε h).graph := by
  exact restricted_multiplier_core dualPhysical (rootSymbol ε h)
    ((symbol_continuous ε hε h).sqrt.measurable) (weight ε a h)
    (weight_memLp ε a h hε ha hh)
    (root_weight_memLp ε a h hε ha hh hb)
    (weight_ne_zero ε a h hε hh)
    (energyOperator ε hε h (hamiltonian_bound ε h hb) hh m g κ t).domain
    (modulated_source_mem_energy_domain ε a h hε ha hh hb m g κ t)

#print axioms root_weight_memLp
#print axioms static_form_core
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticFormCore
