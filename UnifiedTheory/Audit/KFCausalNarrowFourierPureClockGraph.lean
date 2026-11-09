/- The exact narrow Fourier unitary commutes with pure-clock transport
on all L2 states and preserves the full maximal pure-clock momentum graph. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierClockCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNarrowFourierPureClockGraph
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalNarrowFourierCoordinates (mixedCoordinates pairedCoordinates)
open KFCausalNarrowFourierGeneralCoordinates (frequencyCoordinates)
open KFCausalNarrowFourierClockCoordinates
open KFCausalClockFloorPureClockCoordinates (coordinates)
open KFCausalConfigurationTranslation (translation)
open KFCausalClockFloorPureClockTransport (transport transport_apply)
open KFCausalClockFloorPureClockMomentum (pureGroup pureMomentum)
open KFCausalUnitaryMomentumEvolution (momentum_graph_iff)

def transform : Hilbert ≃ₗᵢ[ℂ] Hilbert := mixedCoordinates.trans frequencyCoordinates.symm

theorem frequency_transform (u : Hilbert) : frequencyCoordinates (transform u) = mixedCoordinates u :=
  frequencyCoordinates.apply_symm_apply _

theorem transform_coordinates (ε : ℝ) (hε : 0 < ε) (u : Hilbert) :
    transform (coordinates ε hε u) = coordinates ε hε (transform u) := by
  apply frequencyCoordinates.injective
  rw [frequency_transform,frequency_coordinates,frequency_transform]
  change KFCausalPartialFourier.leftFourier 2 4 (pairedCoordinates (coordinates ε hε u)) = _
  rw [paired_coordinates,KFCausalClockFloorPureClockPartialFourier.partialFourier_commutes]
  rfl

theorem transform_translation (t : ℝ) (u : Hilbert) :
    transform (translation t u) = translation t (transform u) := by
  apply frequencyCoordinates.injective
  rw [frequency_transform,frequency_translation,frequency_transform]
  change KFCausalPartialFourier.leftFourier 2 4 (pairedCoordinates (translation t u)) = _
  rw [paired_translation,KFCausalPartialFourierRightTranslation.leftFourier_rightTranslation]
  rfl

theorem transform_inverse_coordinates (ε : ℝ) (hε : 0 < ε) (u : Hilbert) :
    transform ((coordinates ε hε).symm u) = (coordinates ε hε).symm (transform u) := by
  apply (coordinates ε hε).injective
  rw [← transform_coordinates,LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.apply_symm_apply]

theorem transform_transport (ε : ℝ) (hε : 0 < ε) (t : ℝ) (u : Hilbert) :
    transform (transport ε hε t u) = transport ε hε t (transform u) := by
  simp only [transport_apply,transform_coordinates,transform_translation,transform_inverse_coordinates]

theorem inverse_transform_transport (ε : ℝ) (hε : 0 < ε) (t : ℝ) (u : Hilbert) :
    transform.symm (transport ε hε t u) = transport ε hε t (transform.symm u) := by
  apply transform.injective
  rw [LinearIsometryEquiv.apply_symm_apply,transform_transport,LinearIsometryEquiv.apply_symm_apply]

theorem graph_transform (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (u v : Hilbert)
    (huv : (u,v) ∈ (pureMomentum ε hε h).graph) :
    (transform u,transform v) ∈ (pureMomentum ε hε h).graph := by
  apply (momentum_graph_iff (pureGroup ε hε) h hh _ _).mpr
  have hd := (((transform : Hilbert →L[ℂ] Hilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((momentum_graph_iff (pureGroup ε hε) h hh u v).mp huv))
  change HasDerivAt (fun t : ℝ => transform (transport ε hε t u))
    (transform ((Complex.I/(h:ℂ)) • v)) 0 at hd
  change HasDerivAt (fun t : ℝ => transport ε hε t (transform u))
    ((Complex.I/(h:ℂ)) • transform v) 0
  simpa only [transform_transport,map_smul] using hd

theorem graph_inverse_transform (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (u v : Hilbert)
    (huv : (u,v) ∈ (pureMomentum ε hε h).graph) :
    (transform.symm u,transform.symm v) ∈ (pureMomentum ε hε h).graph := by
  apply (momentum_graph_iff (pureGroup ε hε) h hh _ _).mpr
  have hd := (((transform.symm : Hilbert →L[ℂ] Hilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((momentum_graph_iff (pureGroup ε hε) h hh u v).mp huv))
  change HasDerivAt (fun t : ℝ => transform.symm (transport ε hε t u))
    (transform.symm ((Complex.I/(h:ℂ)) • v)) 0 at hd
  change HasDerivAt (fun t : ℝ => transport ε hε t (transform.symm u))
    ((Complex.I/(h:ℂ)) • transform.symm v) 0
  simpa only [inverse_transform_transport,map_smul] using hd

theorem graph_transform_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (u v : Hilbert) :
    (transform u,transform v) ∈ (pureMomentum ε hε h).graph ↔ (u,v) ∈ (pureMomentum ε hε h).graph := by
  constructor
  · intro hg
    simpa only [LinearIsometryEquiv.symm_apply_apply] using
      graph_inverse_transform ε hε h hh _ _ hg
  · exact graph_transform ε hε h hh u v

theorem domain_transform_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (u : Hilbert) :
    transform u ∈ (pureMomentum ε hε h).domain ↔ u ∈ (pureMomentum ε hε h).domain := by
  constructor
  · intro hu
    obtain ⟨v,hv⟩ := LinearPMap.mem_domain_iff.mp hu
    have hg := graph_inverse_transform ε hε h hh _ _ hv
    rw [LinearIsometryEquiv.symm_apply_apply] at hg
    exact LinearPMap.mem_domain_of_mem_graph hg
  · intro hu
    obtain ⟨v,hv⟩ := LinearPMap.mem_domain_iff.mp hu
    exact LinearPMap.mem_domain_of_mem_graph (graph_transform ε hε h hh u v hv)

#print axioms frequency_transform
#print axioms transform_coordinates
#print axioms transform_translation
#print axioms transform_inverse_coordinates
#print axioms transform_transport
#print axioms inverse_transform_transport
#print axioms graph_transform
#print axioms graph_inverse_transform
#print axioms graph_transform_iff
#print axioms domain_transform_iff
end
end UnifiedTheory.Audit.KFCausalNarrowFourierPureClockGraph
