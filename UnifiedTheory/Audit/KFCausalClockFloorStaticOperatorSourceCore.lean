/- The maximal static Hamiltonian multiplier has an operator graph core
whose inputs lie in the actual full interacting form domain. The density
uses the full sigma-weighted Gaussian estimate; a square-root core alone
would not suffice. No common full-Hamiltonian/growing-operator core is claimed. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticOperatorGaussianWeight
import UnifiedTheory.Audit.KFCausalClockFloorDualModulatedDomain
import UnifiedTheory.Audit.KFCausalModulatedGraphCore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticOperatorSourceCore
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalChargeTransverseSplit (dualPhysical)
open KFCausalClockFloorStaticMultiplierForm (symbol symbol_continuous)
open KFCausalClockFloorStaticOperator (operator)
open KFCausalClockFloorDualModulatedDomain
open KFCausalClockFloorDualGaussian (weight weight_memLp weight_ne_zero)
open KFCausalClockFloorStaticOperatorGaussianWeight (symbol_weight_memLp)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedEnergy
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

def restrictedGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (operator ε hε h).graph ⊓
    (energyOperator ε hε h (hamiltonian_bound ε h hb) hh m g κ t).domain.comap
      (LinearMap.fst ℂ Hilbert Hilbert)

include ha in
theorem operator_source_core :
    (restrictedGraph ε h hε hh hb m g κ t).topologicalClosure =
      (operator ε hε h).graph := by
  exact restricted_multiplier_core dualPhysical (symbol ε h)
    (symbol_continuous ε hε h).measurable (weight ε a h)
    (weight_memLp ε a h hε ha hh)
    (symbol_weight_memLp ε a h hε ha hh)
    (weight_ne_zero ε a h hε hh)
    (energyOperator ε hε h (hamiltonian_bound ε h hb) hh m g κ t).domain
    (modulated_source_mem_energy_domain ε a h hε ha hh hb m g κ t)

#print axioms operator_source_core
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticOperatorSourceCore
