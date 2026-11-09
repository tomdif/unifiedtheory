/- Unitary equivalence of the full strong-generator graphs, including
their actual domains, for straight-clock and coupled longitudinal momentum.
This does not yet identify a Fourier multiplier or a spatial smooth core. -/
import UnifiedTheory.Audit.KFCausalCoupledLongitudinalMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalLongitudinalMomentumConjugacy
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalConfigurationTranslation
open UnifiedTheory.Audit.KFCausalCoupledUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalCoupledUnitaryTransport
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalMomentum

theorem coordinates_derivative_iff (ε : ℝ) (hε : 0 < ε) (f g : Hilbert) :
    HasDerivAt (fun t => transport ε hε t (coordinates ε hε f)) (coordinates ε hε g) 0 ↔
      HasDerivAt (fun t => translation t f) g 0 := by
  constructor
  · intro hd
    have hh := (((coordinates ε hε).symm : Hilbert →L[ℂ] Hilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
    change HasDerivAt (fun t => (coordinates ε hε).symm (transport ε hε t (coordinates ε hε f)))
      ((coordinates ε hε).symm (coordinates ε hε g)) 0 at hh
    simpa only [transport_apply,LinearIsometryEquiv.symm_apply_apply] using hh
  · intro hd
    have hh := ((coordinates ε hε : Hilbert →L[ℂ] Hilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
    change HasDerivAt (fun t => coordinates ε hε (translation t f)) (coordinates ε hε g) 0 at hh
    simpa only [transport_apply,LinearIsometryEquiv.symm_apply_apply] using hh

theorem momentum_graph_conjugacy (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
    (f g : Hilbert) :
    (f,g) ∈ (clockMomentum hbar).graph ↔
      (coordinates ε hε f,coordinates ε hε g) ∈ (longitudinalMomentum ε hε hbar).graph := by
  change (f,g) ∈ (KFCausalUnitaryMomentumSelfAdjoint.momentum clockGroup hbar).graph ↔
    (coordinates ε hε f,coordinates ε hε g) ∈
      (KFCausalUnitaryMomentumSelfAdjoint.momentum (coupledGroup ε hε) hbar).graph
  rw [momentum_graph_iff _ hbar hh,momentum_graph_iff _ hbar hh]
  change HasDerivAt (fun t => translation t f) ((Complex.I/(hbar:ℂ)) • g) 0 ↔
    HasDerivAt (fun t => transport ε hε t (coordinates ε hε f))
      ((Complex.I/(hbar:ℂ)) • coordinates ε hε g) 0
  rw [← map_smul (coordinates ε hε)]
  exact (coordinates_derivative_iff ε hε f ((Complex.I/(hbar:ℂ)) • g)).symm

theorem momentum_domain_conjugacy (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
    (f : Hilbert) :
    f ∈ (clockMomentum hbar).domain ↔
      coordinates ε hε f ∈ (longitudinalMomentum ε hε hbar).domain := by
  constructor
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph
      ((momentum_graph_conjugacy ε hε hbar hh f (clockMomentum hbar ⟨f,hf⟩)).mp
        ((clockMomentum hbar).mem_graph ⟨f,hf⟩))
  · intro hf
    let g := longitudinalMomentum ε hε hbar ⟨coordinates ε hε f,hf⟩
    have hg : (coordinates ε hε f,coordinates ε hε ((coordinates ε hε).symm g)) ∈
        (longitudinalMomentum ε hε hbar).graph := by
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact (longitudinalMomentum ε hε hbar).mem_graph ⟨coordinates ε hε f,hf⟩
    exact LinearPMap.mem_domain_of_mem_graph
      ((momentum_graph_conjugacy ε hε hbar hh f ((coordinates ε hε).symm g)).mpr hg)

#print axioms coordinates_derivative_iff
#print axioms momentum_graph_conjugacy
#print axioms momentum_domain_conjugacy

end
end UnifiedTheory.Audit.KFCausalLongitudinalMomentumConjugacy
