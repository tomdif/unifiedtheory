/- A proved Gaussian core of the actual physical longitudinal exponential.
The core is transported from its full maximal spectral multiplier graph. -/
import UnifiedTheory.Audit.KFCausalEuclideanGaussianCore
import UnifiedTheory.Audit.KFCausalClockFloorExponential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianCore
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanGaussianCore
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorExponential

def spectralPacket (hbar : ℝ) (v : Space) : FrequencyHilbert × FrequencyHilbert :=
  KFCausalModulatedGraphCore.packet (exponentialWeight hbar) gaussian gaussian_memLp
    (weighted_gaussian_memLp hbar) v

def pairPullback (ε : ℝ) (hε : 0 < ε) :
    (FrequencyHilbert × FrequencyHilbert) →L[ℂ] (Hilbert × Hilbert) :=
  ((coupledFourier ε hε).symm : FrequencyHilbert →L[ℂ] Hilbert).prodMap
    ((coupledFourier ε hε).symm : FrequencyHilbert →L[ℂ] Hilbert)

def packet (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (v : Space) : Hilbert × Hilbert :=
  pairPullback ε hε (spectralPacket hbar v)

theorem graph_iff (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (f g : Hilbert) :
    (f,g) ∈ (longitudinalExponential ε hε hbar (1/2)).graph ↔
      (coupledFourier ε hε f,coupledFourier ε hε g) ∈
        KFCausalMultiplierGraphCoordinates.graph (exponentialWeight hbar) (exponentialWeight_measurable hbar) := by
  rw [longitudinal_exponential_graph,KFCausalMultiplierGraphCoordinates.graph_iff]
  have he (k : Space) : (1/2:ℝ)*KFCausalClockFloorFourierMultiplier.symbol hbar k = Real.pi*hbar*k 0 := by
    unfold KFCausalClockFloorFourierMultiplier.symbol
    ring
  simp only [he,exponentialWeight]

theorem packet_mem_graph (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (v : Space) :
    packet ε hε hbar v ∈ (longitudinalExponential ε hε hbar (1/2)).graph := by
  apply (graph_iff ε hε hbar _ _).mpr
  change (coupledFourier ε hε ((coupledFourier ε hε).symm (spectralPacket hbar v).1),
    coupledFourier ε hε ((coupledFourier ε hε).symm (spectralPacket hbar v).2)) ∈ _
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact KFCausalModulatedGraphCore.packet_mem_graph (exponentialWeight hbar)
    (exponentialWeight_measurable hbar) gaussian gaussian_memLp (weighted_gaussian_memLp hbar) v

theorem graph_core (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    (Submodule.span ℂ (Set.range (packet ε hε hbar))).topologicalClosure =
      (longitudinalExponential ε hε hbar (1/2)).graph := by
  let K := Submodule.span ℂ (Set.range (packet ε hε hbar))
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ _ (longitudinal_exponential_closed ε hε hbar (1/2))
    apply Submodule.span_le.mpr
    rintro _ ⟨v,rfl⟩
    exact packet_mem_graph ε hε hbar v
  · have hS : Submodule.span ℂ (Set.range (spectralPacket hbar)) ≤
        K.topologicalClosure.comap (pairPullback ε hε).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v,rfl⟩
      exact K.le_topologicalClosure (Submodule.subset_span ⟨v,rfl⟩)
    have hc := Submodule.topologicalClosure_minimal _ hS
      (K.isClosed_topologicalClosure.preimage (pairPullback ε hε).continuous)
    change (Submodule.span ℂ (Set.range (spectralPacket hbar))).topologicalClosure ≤ _ at hc
    have hd := gaussian_spectral_graph_core hbar
    change (Submodule.span ℂ (Set.range (spectralPacket hbar))).topologicalClosure = _ at hd
    rw [hd] at hc
    rintro ⟨f,g⟩ hfg
    have hh := hc ((graph_iff ε hε hbar f g).mp hfg)
    change ((coupledFourier ε hε).symm (coupledFourier ε hε f),
      (coupledFourier ε hε).symm (coupledFourier ε hε g)) ∈ K.topologicalClosure at hh
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hh

#print axioms graph_iff
#print axioms packet_mem_graph
#print axioms graph_core

end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianCore
