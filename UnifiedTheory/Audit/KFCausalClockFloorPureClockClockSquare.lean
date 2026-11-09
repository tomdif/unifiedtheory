/- Identify the pure-clock derivative of the full clock square on its
existing composition domain. Finite packet derivative domains discharge
the output-domain premise; bounded corrections then survive limits. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockClockResponse
import UnifiedTheory.Audit.KFCausalInverseClockSpectralRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockClockSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorPureClockInverseHalf (inverse_momentum_graph)
open KFCausalClockFloorPureClockKinetic (correction)
open KFCausalClockFloorPureClockClockResponse (half_graph inverse_correction)
open KFCausalInverseClockSpectralRecovery (inverseL_injective)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
local notation "B" => pureMomentum ε hε h
local notation "S" => composition (clockHalf ε) (clockHalf ε)
local notation "D" => inverseL ε hε
local notation "K" => correction ε hε h

omit h hh in
theorem square_graph (f z : Hilbert) : (f,z) ∈ (S).graph ↔ f=D (D z) := by
  rw [composition_graph]
  constructor
  · rintro ⟨g,hfg,hgz⟩
    rw [(half_graph ε hε f g).mp hfg,(half_graph ε hε g z).mp hgz]
  · intro he
    exact ⟨D z,(half_graph ε hε f (D z)).mpr he,(half_graph ε hε (D z) z).mpr rfl⟩

include hh

theorem square_derivative (f b z w bz : Hilbert)
    (hb : (f,b) ∈ (B).graph) (hz : (f,z) ∈ (S).graph) (hw : (b,w) ∈ (S).graph)
    (hbz : (z,bz) ∈ (B).graph) : bz=w-K z-K z := by
  have hd := inverse_momentum_graph ε hε h hh z bz hbz
  change (D z,D bz+K (D z)) ∈ (B).graph at hd
  have hd₂ := inverse_momentum_graph ε hε h hh (D z) (D bz+K (D z)) hd
  have he := (B).mem_graph_snd_inj' hd₂ hb ((square_graph ε hε f z).mp hz).symm
  change D (D bz+K (D z))+K (D (D z))=b at he
  rw [map_add,inverse_correction,(square_graph ε hε b w).mp hw] at he
  apply inverseL_injective ε hε
  apply inverseL_injective ε hε
  simpa only [map_sub,inverse_correction] using
    (eq_sub_iff_add_eq.mpr (eq_sub_iff_add_eq.mpr he))

theorem square_momentum_graph_of_domain (f b z w : Hilbert)
    (hb : (f,b) ∈ (B).graph) (hz : (f,z) ∈ (S).graph) (hw : (b,w) ∈ (S).graph)
    (hzB : z ∈ (B).domain) : (z,w-K z-K z) ∈ (B).graph := by
  have hg := (B).mem_graph ⟨z,hzB⟩
  have he := square_derivative ε hε h hh f b z w _ hb hz hw hg
  exact he ▸ hg

#print axioms square_graph
#print axioms square_derivative
#print axioms square_momentum_graph_of_domain
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockClockSquare
