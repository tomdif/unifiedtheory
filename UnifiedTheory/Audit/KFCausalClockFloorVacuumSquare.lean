/- Exact second-action graph for the ordered vacuum factor E_(1/2) D.
The natural reversed product represents its energy pairing on every
factor-domain test. This is one component, not the full Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
import UnifiedTheory.Audit.KFCausalClockFloorCommonDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorVacuumSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf
open KFCausalClockFloorBoundedInverse
open KFCausalClockFloorExponential
open KFCausalClockFloorTrialSpectralDomain (orderedExponential reversedExponential)
open KFCausalOrderedOperatorComposition

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ)

def square : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (reversedExponential ε hε h) (orderedExponential ε hε h)

theorem reversed_graph (f g : Hilbert) :
    (f,g) ∈ (reversedExponential ε hε h).graph ↔
      ∃ z, (f,z) ∈ (longitudinalExponential ε hε h (1/2)).graph ∧
        g = inverseL ε hε z := by
  rw [reversedExponential,composition_graph]
  exact exists_congr (fun z => and_congr_right (fun _ => inverseL_graph ε hε z g))

theorem square_graph (f g : Hilbert) :
    (f,g) ∈ (square ε hε h).graph ↔
      ∃ z, (inverseL ε hε f,z) ∈ (longitudinalExponential ε hε h 1).graph ∧
        g = inverseL ε hε z := by
  rw [square,composition_graph]
  constructor
  · rintro ⟨u,hu,hr⟩
    obtain ⟨z,hz,hg⟩ := (reversed_graph ε hε h u g).mp hr
    exact ⟨z,(longitudinal_exponential_square ε hε h _ _).mpr
      ⟨u,(ordered_graph_iff ε hε h f u).mp hu,hz⟩,hg⟩
  · rintro ⟨z,hz,hg⟩
    obtain ⟨u,hu,huz⟩ := (longitudinal_exponential_square ε hε h _ _).mp hz
    exact ⟨u,(ordered_graph_iff ε hε h f u).mpr hu,
      (reversed_graph ε hε h u g).mpr ⟨z,huz,hg⟩⟩

theorem square_domain (f : Hilbert) :
    f ∈ (square ε hε h).domain ↔
      inverseL ε hε f ∈ (longitudinalExponential ε hε h 1).domain := by
  constructor
  · intro hf
    obtain ⟨z,hz,_⟩ := (square_graph ε hε h f _).mp ((square ε hε h).mem_graph ⟨f,hf⟩)
    exact LinearPMap.mem_domain_of_mem_graph hz
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph
      ((square_graph ε hε h f _).mpr
        ⟨_,(longitudinalExponential ε hε h 1).mem_graph ⟨_,hf⟩,rfl⟩)

theorem ordered_reversed_pairing (f u v z : Hilbert)
    (hfu : (f,u) ∈ (orderedExponential ε hε h).graph)
    (hvz : (v,z) ∈ (reversedExponential ε hε h).graph) :
    inner ℂ v u = inner ℂ z f := by
  obtain ⟨d,hd,hu⟩ := (composition_graph _ _ _ _).mp hfu
  obtain ⟨e,he,hz⟩ := (composition_graph _ _ _ _).mp hvz
  exact ((selfAdjoint_graph_pairing _ (longitudinal_exponential_selfAdjoint ε hε h (1/2))
    v e d u he hu).symm).trans
      ((selfAdjoint_graph_pairing _ (inverseClockHalf_selfAdjoint ε) e z f d hz hd).symm)

theorem square_pairing (f z u v : Hilbert)
    (huf : (f,u) ∈ (orderedExponential ε hε h).graph)
    (hfz : (f,z) ∈ (square ε hε h).graph)
    (hv : v ∈ (orderedExponential ε hε h).domain) :
    inner ℂ u (orderedExponential ε hε h ⟨v,hv⟩) = inner ℂ z v := by
  obtain ⟨u',hu',hz⟩ := (composition_graph _ _ _ _).mp hfz
  have he := (orderedExponential ε hε h).mem_graph_snd_inj' hu' huf rfl
  dsimp only at he
  rw [he] at hz
  exact ordered_reversed_pairing ε hε h v _ u z
    ((orderedExponential ε hε h).mem_graph ⟨v,hv⟩) hz

theorem square_energy (f z u : Hilbert)
    (hfu : (f,u) ∈ (orderedExponential ε hε h).graph)
    (hfz : (f,z) ∈ (square ε hε h).graph) :
    (inner ℂ z f).re = ‖u‖^2 := by
  have hd := LinearPMap.mem_domain_of_mem_graph hfu
  have hp := square_pairing ε hε h f z u f hfu hfz hd
  have he := (orderedExponential ε hε h).mem_graph_snd_inj'
    ((orderedExponential ε hε h).mem_graph ⟨f,hd⟩) hfu rfl
  dsimp only at he
  rw [he] at hp
  rw [← hp]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) u

theorem square_graph_smul (c : ℂ) (f z : Hilbert)
    (hfz : (f,z) ∈ (square ε hε h).graph) :
    (c • f,c • z) ∈ (square ε hε h).graph :=
  (square ε hε h).graph.smul_mem c hfz

theorem exponential_rescale (c a : ℝ) (f g : Hilbert) :
    (f,g) ∈ (longitudinalExponential ε hε (c*h) a).graph ↔
      (f,g) ∈ (longitudinalExponential ε hε h (a*c)).graph := by
  rw [longitudinal_exponential_graph,longitudinal_exponential_graph]
  have he (k) : a*KFCausalClockFloorFourierMultiplier.symbol (c*h) k =
      (a*c)*KFCausalClockFloorFourierMultiplier.symbol h k := by
    unfold KFCausalClockFloorFourierMultiplier.symbol
    ring
  simp_rw [he]

theorem reversed_le_adjoint (hb : |h| ≤ Real.pi*ε) :
    reversedExponential ε hε h ≤ (orderedExponential ε hε h).adjoint := by
  have hd : Dense ((orderedExponential ε hε h).domain : Set Hilbert) :=
    KFCausalClockFloorCommonDensity.energyFactor_domain_dense ε h hε hb
      0 0 7
  exact (composition_formalAdjoint _ _
    (longitudinal_exponential_selfAdjoint ε hε h (1/2))
    (inverseClockHalf_selfAdjoint ε)).le_adjoint hd

theorem square_adjoint_graph (hb : |h| ≤ Real.pi*ε) (f z : Hilbert)
    (hfz : (f,z) ∈ (square ε hε h).graph) :
    (f,z) ∈ (composition (orderedExponential ε hε h).adjoint
      (orderedExponential ε hε h)).graph := by
  obtain ⟨u,hu,hz⟩ := (composition_graph _ _ _ _).mp hfz
  exact (composition_graph _ _ _ _).mpr
    ⟨u,hu,LinearPMap.le_graph_of_le (reversed_le_adjoint ε hε h hb) hz⟩

#print axioms reversed_graph
#print axioms square_graph
#print axioms square_domain
#print axioms ordered_reversed_pairing
#print axioms square_pairing
#print axioms square_energy
#print axioms square_graph_smul
#print axioms exponential_rescale
#print axioms reversed_le_adjoint
#print axioms square_adjoint_graph
end
end UnifiedTheory.Audit.KFCausalClockFloorVacuumSquare
