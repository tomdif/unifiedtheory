/- The actual pure-clock/kinetic commutator on natural composition
domains. The kinetic factor is P_v C^(-1/2), with its original ordering.
Both directions of composition-domain interchange are derived. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockInverseHalf
import UnifiedTheory.Audit.KFCausalClockFloorPureClockTransverse
import UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockKinetic
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockInverseHalf (inverse_momentum_graph)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockTransverse (transverse_interchange)
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum (transverseMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph (clockMomentum_graph_iff)
open UnifiedTheory.Audit.KFCausalClockFloorKineticDefect (transverse_graph_defect)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse (responseOperator)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (v : Transverse)
local notation "B" => pureMomentum ε hε h
local notation "P" => transverseMomentum h v
local notation "K" => clockMomentum ε h v
local notation "R" => inverseL ε hε
local notation "D" => defectOperator ε hε
local notation "Q" => responseOperator ε hε

def correction : Hilbert →L[ℂ] Hilbert :=
  (Complex.I*(h:ℂ)/(2*(ε:ℂ))) • (D).comp Q

theorem transverse_correction (f g : Hilbert) (hfg : (f,g) ∈ (P).graph) :
    (correction ε hε h f,correction ε hε h g) ∈ (P).graph := by
  have hq : (Q f,Q g) ∈ (P).graph := (P).graph.sub_mem hfg (transverse_graph_defect ε hε h v f g hfg)
  exact (P).graph.smul_mem (Complex.I*(h:ℂ)/(2*(ε:ℂ))) (transverse_graph_defect ε hε h v _ _ hq)

theorem kinetic_interchange (hh : h ≠ 0) (f g b k : Hilbert)
    (hg : (f,g) ∈ (K).graph) (hb : (f,b) ∈ (B).graph) :
    (b,k) ∈ (K).graph ↔ (g,k+correction ε hε h g) ∈ (B).graph := by
  have hr := inverse_momentum_graph ε hε h hh f b hb
  change (R f,R b+correction ε hε h (R f)) ∈ (B).graph at hr
  have hp := (clockMomentum_graph_iff ε hε h v f g).mp hg
  have hc := transverse_correction ε hε h v _ _ hp
  constructor
  · intro hk
    have hsum := (P).graph.add_mem ((clockMomentum_graph_iff ε hε h v b k).mp hk) hc
    exact (transverse_interchange ε hε h hh v _ _ _ _ hp hr).mp hsum
  · intro hk
    have hsum := (transverse_interchange ε hε h hh v _ _ _ _ hp hr).mpr hk
    have hd := (P).graph.sub_mem hsum hc
    apply (clockMomentum_graph_iff ε hε h v b k).mpr
    simpa only [Prod.sub_def,add_sub_cancel_right] using hd

theorem kinetic_momentum_graph (hh : h ≠ 0) (f g b k : Hilbert)
    (hg : (f,g) ∈ (K).graph) (hb : (f,b) ∈ (B).graph) (hk : (b,k) ∈ (K).graph) :
    (g,k+correction ε hε h g) ∈ (B).graph :=
  (kinetic_interchange ε hε h v hh f g b k hg hb).mp hk

theorem momentum_kinetic_graph (hh : h ≠ 0) (f g b bg : Hilbert)
    (hg : (f,g) ∈ (K).graph) (hb : (f,b) ∈ (B).graph) (hbg : (g,bg) ∈ (B).graph) :
    (b,bg-correction ε hε h g) ∈ (K).graph :=
  (kinetic_interchange ε hε h v hh f g b _ hg hb).mpr (by simpa only [sub_add_cancel] using hbg)

theorem composition_domain_iff (hh : h ≠ 0) (f g b : Hilbert)
    (hg : (f,g) ∈ (K).graph) (hb : (f,b) ∈ (B).graph) :
    b ∈ (K).domain ↔ g ∈ (B).domain := by
  constructor
  · intro hk
    obtain ⟨k,hk⟩ := LinearPMap.mem_domain_iff.mp hk
    exact LinearPMap.mem_domain_of_mem_graph (kinetic_momentum_graph ε hε h v hh f g b k hg hb hk)
  · intro hbg
    obtain ⟨bg,hbg⟩ := LinearPMap.mem_domain_iff.mp hbg
    exact LinearPMap.mem_domain_of_mem_graph (momentum_kinetic_graph ε hε h v hh f g b bg hg hb hbg)

theorem commutator (hh : h ≠ 0) (f g b k bg : Hilbert)
    (hg : (f,g) ∈ (K).graph) (hb : (f,b) ∈ (B).graph)
    (hk : (b,k) ∈ (K).graph) (hbg : (g,bg) ∈ (B).graph) :
    bg-k = correction ε hε h g := by
  have he := (B).mem_graph_snd_inj' hbg (kinetic_momentum_graph ε hε h v hh f g b k hg hb hk) rfl
  change bg = k+correction ε hε h g at he
  rw [he,add_sub_cancel_left]

#print axioms transverse_correction
#print axioms kinetic_interchange
#print axioms kinetic_momentum_graph
#print axioms momentum_kinetic_graph
#print axioms composition_domain_iff
#print axioms commutator
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockKinetic
