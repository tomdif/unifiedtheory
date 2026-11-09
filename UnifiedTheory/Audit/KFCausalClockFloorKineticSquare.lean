/- The natural second kinetic action is D P_v P_v D. Its two momentum
graphs provide an actual Hilbert representative of the kinetic form. -/
import UnifiedTheory.Audit.KFCausalClockFloorVacuumSquare
import UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorKineticSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalClockFloorClockHalf
open KFCausalClockFloorBoundedInverse
open KFCausalClockFloorTrialMomentum (clockMomentum)
open KFCausalPhysicalTransverseMomentum (transverseMomentum transverseMomentum_selfAdjoint)
open KFCausalOrderedOperatorComposition

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (v : Transverse)

def reverse : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (inverseClockHalf ε) (transverseMomentum h v)

def square : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (reverse ε h v) (clockMomentum ε h v)

theorem square_graph (f z : Hilbert) :
    (f,z) ∈ (square ε h v).graph ↔ ∃ u q,
      (inverseL ε hε f,u) ∈ (transverseMomentum h v).graph ∧
      (u,q) ∈ (transverseMomentum h v).graph ∧ z = inverseL ε hε q := by
  rw [square,composition_graph]
  constructor
  · rintro ⟨u,hu,hr⟩
    obtain ⟨d,hd,hdu⟩ := (composition_graph _ _ _ _).mp hu
    obtain ⟨q,huq,hq⟩ := (composition_graph _ _ _ _).mp hr
    rw [(inverseL_graph ε hε f d).mp hd] at hdu
    exact ⟨u,q,hdu,huq,(inverseL_graph ε hε q z).mp hq⟩
  · rintro ⟨u,q,hdu,huq,hq⟩
    exact ⟨u,(composition_graph _ _ _ _).mpr
      ⟨_,(inverseL_graph ε hε f _).mpr rfl,hdu⟩,
      (composition_graph _ _ _ _).mpr ⟨q,huq,(inverseL_graph ε hε q z).mpr hq⟩⟩

include hε in
theorem reverse_le_adjoint (hb : |h| ≤ Real.pi*ε) :
    reverse ε h v ≤ (clockMomentum ε h v).adjoint := by
  have hd : Dense ((clockMomentum ε h v).domain : Set Hilbert) :=
    KFCausalClockFloorCommonDensity.energyFactor_domain_dense ε h hε hb
      (fun _ => v) 0 1
  exact (composition_formalAdjoint _ _ (transverseMomentum_selfAdjoint h v)
    (inverseClockHalf_selfAdjoint ε)).le_adjoint hd

include hε in
theorem square_adjoint_graph (hb : |h| ≤ Real.pi*ε) (f z : Hilbert)
    (hfz : (f,z) ∈ (square ε h v).graph) :
    (f,z) ∈ (composition (clockMomentum ε h v).adjoint (clockMomentum ε h v)).graph := by
  obtain ⟨u,hu,hz⟩ := (composition_graph _ _ _ _).mp hfz
  exact (composition_graph _ _ _ _).mpr
    ⟨u,hu,LinearPMap.le_graph_of_le (reverse_le_adjoint ε hε h v hb) hz⟩

theorem square_pairing (f z u q r : Hilbert)
    (hfu : (f,u) ∈ (clockMomentum ε h v).graph)
    (hfz : (f,z) ∈ (square ε h v).graph)
    (hqr : (q,r) ∈ (clockMomentum ε h v).graph) :
    inner ℂ u r = inner ℂ z q := by
  obtain ⟨u',hu',hz⟩ := (composition_graph _ _ _ _).mp hfz
  have he := (clockMomentum ε h v).mem_graph_snd_inj' hu' hfu rfl
  dsimp only at he
  rw [he] at hz
  obtain ⟨d,hd,hr⟩ := (composition_graph _ _ _ _).mp hqr
  obtain ⟨p,hp,hz'⟩ := (composition_graph _ _ _ _).mp hz
  exact ((selfAdjoint_graph_pairing _ (transverseMomentum_selfAdjoint h v)
    u p d r hp hr).symm).trans
      ((selfAdjoint_graph_pairing _ (inverseClockHalf_selfAdjoint ε) p z q d hz' hd).symm)

#print axioms square_graph
#print axioms reverse_le_adjoint
#print axioms square_adjoint_graph
#print axioms square_pairing
end
end UnifiedTheory.Audit.KFCausalClockFloorKineticSquare
