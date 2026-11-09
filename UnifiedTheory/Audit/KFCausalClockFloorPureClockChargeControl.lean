/- Exact extraction of pure-clock momentum from its charge-orbit graph.
The squared output norm is unchanged by charge averaging. Tail and
family-tightness implications require actual output bounds; none are
claimed for the Hamiltonian trajectory in this module. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockProbability
import UnifiedTheory.Audit.KFCausalCanonicalClockControl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeControl
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeGraph (graph_charge graph_output_norm)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockProbability
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action action_reverse group)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure orbitState orbitState_coe)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

variable (ε : ℝ) (hε : 0 < ε)

theorem averaged_graph_norm (h : ℝ) (hh : h ≠ 0) (f : Hilbert)
    (q : Lp Hilbert 2 angleMeasure)
    (hq : ∀ᵐ θ ∂angleMeasure, (action h hh (2*Real.pi*θ) f,q θ) ∈ (pureMomentum ε hε h).graph) :
    ∃ g : Hilbert, (f,g) ∈ (pureMomentum ε hε h).graph ∧ ‖g‖^2 = ‖q‖^2 := by
  obtain ⟨θ,hθ⟩ := hq.exists
  let g := action h hh (-(2*Real.pi*θ)) (q θ)
  have hg : (f,g) ∈ (pureMomentum ε hε h).graph := by
    simpa only [action_reverse] using graph_charge ε hε h hh (-(2*Real.pi*θ)) _ _ hθ
  refine ⟨g,hg,?_⟩
  rw [l2_norm_square angleMeasure q]
  have he : (fun θ => ‖q θ‖^2) =ᵐ[angleMeasure] fun _ => ‖g‖^2 := by
    filter_upwards [hq] with φ hφ
    rw [graph_output_norm ε hε h hh (2*Real.pi*φ) f g (q φ) hg hφ]
  rw [integral_congr_ae he]
  simp

theorem domain_iff_orbit_graph (h : ℝ) (hh : h ≠ 0) (f : Hilbert) :
    f ∈ (pureMomentum ε hε h).domain ↔ ∃ q : Lp Hilbert 2 angleMeasure,
      ∀ᵐ θ ∂angleMeasure, (action h hh (2*Real.pi*θ) f,q θ) ∈ (pureMomentum ε hε h).graph := by
  constructor
  · intro hf
    obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf
    refine ⟨orbitState (group h hh) (2*Real.pi) g,?_⟩
    filter_upwards [orbitState_coe (group h hh) (2*Real.pi) g] with θ hθ
    rw [hθ]
    exact graph_charge ε hε h hh (2*Real.pi*θ) f g hg
  · rintro ⟨q,hq⟩
    obtain ⟨g,hg,_⟩ := averaged_graph_norm ε hε h hh f q hq
    exact LinearPMap.mem_domain_of_mem_graph hg

theorem averaged_graph_tail_bound (h : ℝ) (hh : h ≠ 0) (R : ℝ) (f : Hilbert)
    (q : Lp Hilbert 2 angleMeasure)
    (hq : ∀ᵐ θ ∂angleMeasure, (action h hh (2*Real.pi*θ) f,q θ) ∈ (pureMomentum ε hε h).graph) :
    R^2*tail ε hε h R f ≤ ‖q‖^2 := by
  obtain ⟨g,hg,he⟩ := averaged_graph_norm ε hε h hh f q hq
  exact (graph_tail_bound ε hε h hh R f g hg).trans_eq he

theorem bounded_graph_family_tight {I : Type*} (eps : I → ℝ) (heps : ∀ i, 0 < eps i)
    (h : I → ℝ) (hne : ∀ i, h i ≠ 0) (f g : I → Hilbert)
    (hg : ∀ i, (f i,g i) ∈ (pureMomentum (eps i) (heps i) (h i)).graph)
    (M : ℝ) (hM : ∀ i, ‖g i‖^2 ≤ M) :
    IsTightMeasureSet (Set.range (fun i => law (eps i) (heps i) (h i) (f i))) := by
  apply KFCausalCanonicalClockControl.bounded_graph_family_tight h hne
    (fun i => (coordinates (eps i) (heps i)).symm (f i))
    (fun i => (coordinates (eps i) (heps i)).symm (g i))
    (fun i => inverse_graph (eps i) (heps i) (h i) (hne i) (f i) (g i) (hg i)) M
  intro i
  simpa only [LinearIsometryEquiv.norm_map] using hM i

#print axioms averaged_graph_norm
#print axioms domain_iff_orbit_graph
#print axioms averaged_graph_tail_bound
#print axioms bounded_graph_family_tight
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeControl
