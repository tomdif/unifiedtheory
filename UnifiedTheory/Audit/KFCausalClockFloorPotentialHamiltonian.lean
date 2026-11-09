/- The potential Hamiltonian comes from completion of the literal three
ordered rows of the original reference form. Reference sources are dense
in that graph norm by construction. The growing form maps into it by an
actual graph projection, not by an assumed maximal-domain identity. -/
import UnifiedTheory.Audit.KFCausalClockFloorPotentialOutputClosure

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPotentialHamiltonian
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorPotentialOutputClosure
open KFCausalClockFloorChartPhasePairing (orderedOutputLp)

private def projectForm (D E : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (L : EnergyOutputSpace →L[ℂ] EnergyOutputSpace)
    (hg : ∀ f z, (f,z) ∈ D.operator.graph → (f,L z) ∈ E.operator.graph)
    (u : KFCausalClosedGraphForm.FormSpace D) : KFCausalClosedGraphForm.FormSpace E :=
  ⟨WithLp.toLp 2 (KFCausalClosedGraphForm.embedding D u,
    L (KFCausalClosedGraphForm.energyOutput D u)),
    hg _ _ u.property⟩

private theorem projectForm_embedding (D E : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (L : EnergyOutputSpace →L[ℂ] EnergyOutputSpace)
    (hg : ∀ f z, (f,z) ∈ D.operator.graph → (f,L z) ∈ E.operator.graph)
    (u : KFCausalClosedGraphForm.FormSpace D) :
    KFCausalClosedGraphForm.embedding E (projectForm D E L hg u)=
      KFCausalClosedGraphForm.embedding D u := rfl

private theorem projectForm_output (D E : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (L : EnergyOutputSpace →L[ℂ] EnergyOutputSpace)
    (hg : ∀ f z, (f,z) ∈ D.operator.graph → (f,L z) ∈ E.operator.graph)
    (u : KFCausalClosedGraphForm.FormSpace D) :
    KFCausalClosedGraphForm.energyOutput E (projectForm D E L hg u)=
      L (KFCausalClosedGraphForm.energyOutput D u) := rfl

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
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hh hb m g k 0
local notation "J" => embedding ε hε h hh hb m g k 0
local notation "A" => potentialMap ε hε h hh hb m g k

def formData : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace where
  operator := operator ε hε h hh hb m g k
  closed := operator_closed ε hε h hh hb m g k
  dense := operator_dense ε hε h hh hb m g k

local notation "D" => formData ε hε h hh hb m g k
abbrev PotentialForm := KFCausalClosedGraphForm.FormSpace D

def referenceLift (u : V) : PotentialForm ε hε h hh hb m g k :=
  ⟨WithLp.toLp 2 (J u,A u),reference_graph ε hε h hh hb m g k u⟩

theorem referenceLift_embedding (u : V) :
    KFCausalClosedGraphForm.embedding D (referenceLift ε hε h hh hb m g k u)=J u := rfl

theorem referenceLift_output (u : V) :
    KFCausalClosedGraphForm.energyOutput D (referenceLift ε hε h hh hb m g k u)=A u := rfl

theorem referenceLift_dense : DenseRange (referenceLift ε hε h hh hb m g k) := by
  exact source_dense D J A (referenceLift ε hε h hh hb m g k) (fun _ => rfl)
    (operator_graph ε hε h hh hb m g k)

local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hb m g k
local notation "GV" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hb m g k
local notation "GJ" => KFCausalClosedGraphForm.embedding GD
local notation "GB" => KFCausalClosedGraphForm.energyOutput GD

def growingLift (u : GV) : PotentialForm ε hε h hh hb m g k :=
  projectForm GD D orderedOutputLp (growing_graph ε hε h hh hb m g k) u

theorem growingLift_embedding (u : GV) :
    KFCausalClosedGraphForm.embedding D (growingLift ε hε h hh hb m g k u)=GJ u :=
  projectForm_embedding GD D orderedOutputLp (growing_graph ε hε h hh hb m g k) u

theorem growingLift_output (u : GV) :
    KFCausalClosedGraphForm.energyOutput D (growingLift ε hε h hh hb m g k u)=
      orderedOutputLp (GB u) :=
  projectForm_output GD D orderedOutputLp (growing_graph ε hε h hh hb m g k) u

def hamiltonian : Hilbert →ₗ.[ℂ] Hilbert := KFCausalClosedGraphForm.hamiltonian D

theorem hamiltonian_selfAdjoint : IsSelfAdjoint (hamiltonian ε hε h hh hb m g k) :=
  KFCausalClosedGraphForm.hamiltonian_selfAdjoint D

#print axioms referenceLift_embedding
#print axioms referenceLift_output
#print axioms referenceLift_dense
#print axioms growingLift_embedding
#print axioms growingLift_output
#print axioms hamiltonian_selfAdjoint
end
end UnifiedTheory.Audit.KFCausalClockFloorPotentialHamiltonian
