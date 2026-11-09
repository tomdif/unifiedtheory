/- The residual Hamiltonian is associated to the completion of the
original static and time-weighted ordered-potential rows. Its reference
sources are dense by the literal graph closure, not by a presumed
intersection of separate operator domains. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticPotentialOutputClosure

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticPotentialHamiltonian
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorStaticPotentialOutputClosure

private theorem source_dense {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (J : X →L[ℂ] Hilbert) (A : X →L[ℂ] EnergyOutputSpace)
    (F : X → KFCausalClosedGraphForm.FormSpace D)
    (hF : ∀ u, WithLp.ofLp (F u).val=(J u,A u))
    (hgraph : D.operator.graph=(J.prod A).toLinearMap.range.topologicalClosure) :
    DenseRange F := by
  intro w
  have hw : WithLp.ofLp w.val ∈ (J.prod A).toLinearMap.range.topologicalClosure := by
    rw [← hgraph]
    exact w.property
  obtain ⟨z,hz,ht⟩ := mem_closure_iff_seq_limit.mp
    (show WithLp.ofLp w.val ∈ closure ((J.prod A).toLinearMap.range : Set (Hilbert × EnergyOutputSpace)) from hw)
  have hex (n : ℕ) : ∃ u : X, (J u,A u)=z n := hz n
  choose u hu using hex
  have hu' : Tendsto (fun n => WithLp.ofLp (F (u n)).val) atTop (𝓝 (WithLp.ofLp w.val)) := by
    simpa only [hF,hu] using ht
  have hl : Tendsto (fun n => F (u n)) atTop (𝓝 w) := by
    apply tendsto_subtype_rng.mpr
    exact ((WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert EnergyOutputSpace).symm.continuous.tendsto
      (WithLp.ofLp w.val)).comp hu'
  exact mem_closure_of_tendsto hl (Eventually.of_forall (fun n => Set.mem_range_self (u n)))

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
local notation "V" => FormSpace ε hε h hh hb m g k 0
local notation "J" => embedding ε hε h hh hb m g k 0
local notation "A" => sourceMap ε hε h hh hb m g k t

def formData : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace where
  operator := operator ε hε h hh hb m g k t
  closed := operator_closed ε hε h hh hb m g k t
  dense := operator_dense ε hε h hh hb m g k t

local notation "D" => formData ε hε h hh hb m g k t
abbrev ResidualForm := KFCausalClosedGraphForm.FormSpace D

def referenceLift (u : V) : ResidualForm ε hε h hh hb m g k t :=
  ⟨WithLp.toLp 2 (J u,A u),reference_graph ε hε h hh hb m g k t u⟩

theorem referenceLift_embedding (u : V) :
    KFCausalClosedGraphForm.embedding D (referenceLift ε hε h hh hb m g k t u)=J u := rfl

theorem referenceLift_output (u : V) :
    KFCausalClosedGraphForm.energyOutput D (referenceLift ε hε h hh hb m g k t u)=A u := rfl

theorem referenceLift_dense : DenseRange (referenceLift ε hε h hh hb m g k t) := by
  exact source_dense D J A (referenceLift ε hε h hh hb m g k t) (fun _ => rfl)
    (operator_graph ε hε h hh hb m g k t)

def hamiltonian : Hilbert →ₗ.[ℂ] Hilbert := KFCausalClosedGraphForm.hamiltonian D

theorem hamiltonian_selfAdjoint : IsSelfAdjoint (hamiltonian ε hε h hh hb m g k t) :=
  KFCausalClosedGraphForm.hamiltonian_selfAdjoint D

#print axioms referenceLift_embedding
#print axioms referenceLift_output
#print axioms referenceLift_dense
#print axioms hamiltonian_selfAdjoint
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticPotentialHamiltonian
