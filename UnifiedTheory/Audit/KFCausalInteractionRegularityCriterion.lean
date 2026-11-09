/- An exact bounded-operator certificate for the remaining strong-domain
regularity problem. Existence of the certificate is not assumed or proved. -/
import UnifiedTheory.Audit.KFCausalCircularInteractingBridge
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianClockCore
import Mathlib.Analysis.Normed.Operator.Banach

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000

namespace UnifiedTheory.Audit.KFCausalInteractionRegularityCriterion
noncomputable section
open Filter
open scoped Topology

theorem closed_composition_iff_bounded {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (P : X →ₗ.[ℂ] X) (hP : P.IsClosed) (R : X →L[ℂ] X) :
    (∀ f, R f ∈ P.domain) ↔ ∃ B : X →L[ℂ] X, ∀ f, (R f,B f) ∈ P.graph := by
  constructor
  · intro hr
    let L : X →ₗ[ℂ] X := P.toFun.comp (R.toLinearMap.codRestrict P.domain hr)
    have hg (f : X) : (R f,L f) ∈ P.graph := P.mem_graph ⟨R f,hr f⟩
    have hc : Continuous L := L.continuous_of_seq_closed_graph (by
      intro u x y hu hy
      have ht : Tendsto (fun n => (R (u n),L (u n))) atTop (𝓝 (R x,y)) :=
        ((R.continuous.tendsto x).comp hu).prodMk_nhds hy
      have hm : (R x,y) ∈ P.graph := hP.mem_of_tendsto ht (Eventually.of_forall (fun n => hg (u n)))
      exact P.mem_graph_snd_inj' hm (hg x) rfl)
    exact ⟨⟨L,hc⟩,hg⟩
  · rintro ⟨B,hB⟩ f
    exact LinearPMap.mem_domain_of_mem_graph (hB f)

open KFCausalConfigurationTestSpace (Hilbert)
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb m g k t
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hb m g k
local notation "R" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hb m g k t 1

/-- A single, fixed shifted resolvent suffices; no limit over shifts is required. -/
theorem domain_inclusion_iff_resolvent_range :
    (H).domain ≤ (P).domain ↔ ∀ f : Hilbert, R f ∈ (P).domain := by
  constructor
  · intro hi f
    exact hi (KFCausalClockFloorHamiltonianClockCore.resolves
      ε hε h hh hb m g k t 1 (by norm_num) f).1
  · intro hr f hf
    have he := KFCausalClockFloorHamiltonianClockCore.left_inverse
      ε hε h hh hb m g k t 1 (by norm_num) ⟨f,hf⟩
    have hm := hr ((H) ⟨f,hf⟩+(1:ℝ) • f)
    rwa [he] at hm

/-- The missing regularity theorem is equivalent to boundedness of P(H+1)⁻¹,
with the actual potential graph retained on the right. -/
theorem domain_inclusion_iff_bounded_certificate :
    (H).domain ≤ (P).domain ↔
      ∃ B : Hilbert →L[ℂ] Hilbert, ∀ f : Hilbert, (R f,B f) ∈ (P).graph := by
  rw [domain_inclusion_iff_resolvent_range]
  exact closed_composition_iff_bounded P
    (KFCausalClockFloorPotentialHamiltonian.hamiltonian_selfAdjoint ε hε h hh hb m g k).isClosed R

theorem domain_inclusion_iff_uniform_bound :
    (H).domain ≤ (P).domain ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Hilbert, ∃ y : Hilbert,
        (R f,y) ∈ (P).graph ∧ ‖y‖ ≤ C*‖f‖ := by
  constructor
  · intro hi
    obtain ⟨B,hB⟩ := (domain_inclusion_iff_bounded_certificate ε hε h hh hb m g k t).mp hi
    exact ⟨‖B‖,norm_nonneg B,fun f => ⟨B f,hB f,B.le_opNorm f⟩⟩
  · rintro ⟨C,hC,hb'⟩
    apply (domain_inclusion_iff_resolvent_range ε hε h hh hb m g k t).mpr
    intro f
    obtain ⟨y,hy,_⟩ := hb' f
    exact LinearPMap.mem_domain_of_mem_graph hy

#print axioms closed_composition_iff_bounded
#print axioms domain_inclusion_iff_resolvent_range
#print axioms domain_inclusion_iff_bounded_certificate
#print axioms domain_inclusion_iff_uniform_bound
end
end UnifiedTheory.Audit.KFCausalInteractionRegularityCriterion
