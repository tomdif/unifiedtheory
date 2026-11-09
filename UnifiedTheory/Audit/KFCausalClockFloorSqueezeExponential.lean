/- Paired squeeze preserves the full maximal graphs of the unbounded longitudinal
exponential and ordered vacuum factor. This is not Hamiltonian evolution. -/
import UnifiedTheory.Audit.KFCausalPairedSqueezeFourier
import UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorSqueezeExponential
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport (transport transport_reverse)
open UnifiedTheory.Audit.KFCausalPairedSqueezeEuclidean (linearFlow dual_clock)
open UnifiedTheory.Audit.KFCausalPairedSqueezeFourier (coupled_fourier_coe coefficient)
open UnifiedTheory.Audit.KFCausalFourierLinearChange (dual_quasiMeasurePreserving)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier (symbol)
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (ordered_graph_iff)

variable (ε : ℝ) (hε : 0 < ε)

theorem exponential_graph_squeeze (h a t : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h a).graph) :
    (transport t f,transport t g) ∈ (longitudinalExponential ε hε h a).graph := by
  rw [longitudinal_exponential_graph] at hfg ⊢
  filter_upwards [coupled_fourier_coe ε hε t f,coupled_fourier_coe ε hε t g,
    (dual_quasiMeasurePreserving (linearFlow t)).ae hfg] with k hf hg he
  rw [hg,hf,he]
  simp only [symbol,dual_clock]
  ring

theorem exponential_graph_squeeze_iff (h a t : ℝ) (f g : Hilbert) :
    (transport t f,transport t g) ∈ (longitudinalExponential ε hε h a).graph ↔
      (f,g) ∈ (longitudinalExponential ε hε h a).graph := by
  constructor
  · intro hfg
    simpa only [transport_reverse] using exponential_graph_squeeze ε hε h a (-t) _ _ hfg
  · exact exponential_graph_squeeze ε hε h a t f g

theorem exponential_domain_squeeze_iff (h a t : ℝ) (f : Hilbert) :
    transport t f ∈ (longitudinalExponential ε hε h a).domain ↔
      f ∈ (longitudinalExponential ε hε h a).domain := by
  constructor
  · intro hf
    obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf
    have he := exponential_graph_squeeze ε hε h a (-t) _ _ hg
    rw [transport_reverse] at he
    exact LinearPMap.mem_domain_of_mem_graph he
  · intro hf
    obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf
    exact LinearPMap.mem_domain_of_mem_graph (exponential_graph_squeeze ε hε h a t f g hg)

theorem exponential_output_norm (h a t : ℝ) (f g q : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h a).graph)
    (hfq : (transport t f,q) ∈ (longitudinalExponential ε hε h a).graph) : ‖q‖ = ‖g‖ := by
  have he := (longitudinalExponential ε hε h a).mem_graph_snd_inj'
    hfq (exponential_graph_squeeze ε hε h a t f g hfg) rfl
  dsimp only at he
  rw [he,LinearIsometryEquiv.norm_map]

theorem ordered_graph_squeeze (h t : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (orderedExponential ε hε h).graph) :
    (transport t f,transport t g) ∈ (orderedExponential ε hε h).graph := by
  rw [ordered_graph_iff] at hfg ⊢
  rw [← KFCausalPairedSqueezeClockCommutation.inverse_half_commutes]
  exact exponential_graph_squeeze ε hε h (1/2) t _ _ hfg

theorem ordered_graph_squeeze_iff (h t : ℝ) (f g : Hilbert) :
    (transport t f,transport t g) ∈ (orderedExponential ε hε h).graph ↔
      (f,g) ∈ (orderedExponential ε hε h).graph := by
  constructor
  · intro hfg
    simpa only [transport_reverse] using ordered_graph_squeeze ε hε h (-t) _ _ hfg
  · exact ordered_graph_squeeze ε hε h t f g

theorem ordered_domain_squeeze_iff (h t : ℝ) (f : Hilbert) :
    transport t f ∈ (orderedExponential ε hε h).domain ↔
      f ∈ (orderedExponential ε hε h).domain := by
  constructor
  · intro hf
    obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf
    have he := ordered_graph_squeeze ε hε h (-t) _ _ hg
    rw [transport_reverse] at he
    exact LinearPMap.mem_domain_of_mem_graph he
  · intro hf
    obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf
    exact LinearPMap.mem_domain_of_mem_graph (ordered_graph_squeeze ε hε h t f g hg)

theorem ordered_output_norm (h t : ℝ) (f g q : Hilbert)
    (hfg : (f,g) ∈ (orderedExponential ε hε h).graph)
    (hfq : (transport t f,q) ∈ (orderedExponential ε hε h).graph) : ‖q‖ = ‖g‖ := by
  have he := (orderedExponential ε hε h).mem_graph_snd_inj'
    hfq (ordered_graph_squeeze ε hε h t f g hfg) rfl
  dsimp only at he
  rw [he,LinearIsometryEquiv.norm_map]

#print axioms exponential_graph_squeeze
#print axioms exponential_graph_squeeze_iff
#print axioms exponential_domain_squeeze_iff
#print axioms exponential_output_norm
#print axioms ordered_graph_squeeze
#print axioms ordered_graph_squeeze_iff
#print axioms ordered_domain_squeeze_iff
#print axioms ordered_output_norm
end
end UnifiedTheory.Audit.KFCausalClockFloorSqueezeExponential
