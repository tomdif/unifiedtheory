/- The natural second kinetic action D P P D has an actual pure-clock
graph whenever the state and its pure-clock momentum have that second
action. The commutator is twice the existing bounded clock correction. -/
import UnifiedTheory.Audit.KFCausalClockFloorKineticSquare
import UnifiedTheory.Audit.KFCausalClockFloorPureClockKinetic
import UnifiedTheory.Audit.KFCausalClockFloorPureClockClockResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockKineticSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorTrialMomentum (clockMomentum)
open KFCausalClockFloorAntisymmetricGraph (clockMomentum_graph_iff)
open KFCausalClockFloorKineticSquare (square square_graph)
open KFCausalClockFloorPureClockKinetic (correction kinetic_momentum_graph transverse_correction)
open KFCausalClockFloorPureClockTransverse (transverse_interchange)
open KFCausalClockFloorPureClockInverseHalf (inverse_momentum_graph)
open KFCausalClockFloorPureClockClockResponse (inverse_correction)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (v : Transverse)
local notation "B" => pureMomentum ε hε h
local notation "S" => square ε h v
local notation "D" => inverseL ε hε
local notation "K" => correction ε hε h

include hh

theorem square_momentum_graph (f b z w : Hilbert)
    (hb : (f,b) ∈ (B).graph) (hz : (f,z) ∈ (S).graph) (hw : (b,w) ∈ (S).graph) :
    (z,w+K z+K z) ∈ (B).graph := by
  obtain ⟨g,q,hfg,hgq,hz⟩ := (square_graph ε hε h v f z).mp hz
  obtain ⟨k,r,hbk,hkr,hw⟩ := (square_graph ε hε h v b w).mp hw
  have hbg := kinetic_momentum_graph ε hε h v hh f g b k
    ((clockMomentum_graph_iff ε hε h v f g).mpr hfg) hb
    ((clockMomentum_graph_iff ε hε h v b k).mpr hbk)
  have hp : (k+K g,r+K q) ∈ (transverseMomentum h v).graph :=
    (transverseMomentum h v).graph.add_mem hkr (transverse_correction ε hε h v g q hgq)
  have hq := (transverse_interchange ε hε h hh v g q (k+K g) (r+K q) hgq hbg).mp hp
  have hd := inverse_momentum_graph ε hε h hh q (r+K q) hq
  change (D q,D (r+K q)+K (D q)) ∈ (B).graph at hd
  simpa only [map_add,inverse_correction,← hz,← hw] using hd

theorem square_momentum_domain (f b z w : Hilbert)
    (hb : (f,b) ∈ (B).graph) (hz : (f,z) ∈ (S).graph) (hw : (b,w) ∈ (S).graph) :
    z ∈ (B).domain :=
  LinearPMap.mem_domain_of_mem_graph (square_momentum_graph ε hε h hh v f b z w hb hz hw)

theorem square_commutator (f b z w bz : Hilbert)
    (hb : (f,b) ∈ (B).graph) (hz : (f,z) ∈ (S).graph) (hw : (b,w) ∈ (S).graph)
    (hbz : (z,bz) ∈ (B).graph) : bz-w=K z+K z := by
  have he := (B).mem_graph_snd_inj' hbz (square_momentum_graph ε hε h hh v f b z w hb hz hw) rfl
  change bz=w+K z+K z at he
  rw [he]
  abel

#print axioms square_momentum_graph
#print axioms square_momentum_domain
#print axioms square_commutator
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockKineticSquare
