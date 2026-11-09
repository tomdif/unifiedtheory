/- The original interacting averaged sources embed densely into the
complete maximal static-root graph. This preserves the physical embedding
and the norm of the original three static energy rows. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticFormCore
import Mathlib.Analysis.Normed.Operator.Extend

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticRootSource
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorStaticMultiplierForm
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedEnergy
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp)

private def graphLift {H K V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (D : KFCausalClosedGraphForm.Data H K) (J : V →L[ℂ] H)
    (hJ : ∀ u, J u ∈ D.operator.domain) :
    V →ₗ[ℂ] KFCausalClosedGraphForm.FormSpace D where
  toFun u := KFCausalClosedGraphForm.graphVector D ⟨J u,hJ u⟩
  map_add' u v := by
    apply KFCausalClosedGraphForm.embedding_injective D
    exact (J.map_add u v).trans ((KFCausalClosedGraphForm.embedding D).map_add
      (KFCausalClosedGraphForm.graphVector D ⟨J u,hJ u⟩)
      (KFCausalClosedGraphForm.graphVector D ⟨J v,hJ v⟩)).symm
  map_smul' c u := by
    apply KFCausalClosedGraphForm.embedding_injective D
    exact (J.map_smul c u).trans ((KFCausalClosedGraphForm.embedding D).map_smul c
      (KFCausalClosedGraphForm.graphVector D ⟨J u,hJ u⟩)).symm

private theorem graphLift_dense {H K V : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (D : KFCausalClosedGraphForm.Data H K) (J : V →L[ℂ] H)
    (hJ : ∀ u, J u ∈ D.operator.domain)
    (hcore : (D.operator.graph ⊓ J.toLinearMap.range.comap
      (LinearMap.fst ℂ H K)).topologicalClosure = D.operator.graph) :
    DenseRange (graphLift D J hJ) := by
  intro w
  have hw : WithLp.ofLp w.val ∈ (D.operator.graph ⊓ J.toLinearMap.range.comap
      (LinearMap.fst ℂ H K)).topologicalClosure := by
    rw [hcore]
    exact w.property
  obtain ⟨z,hz,ht⟩ := mem_closure_iff_seq_limit.mp
    (show WithLp.ofLp w.val ∈ closure ((D.operator.graph ⊓ J.toLinearMap.range.comap
      (LinearMap.fst ℂ H K)) : Set (H × K)) from hw)
  have hex (n : ℕ) : ∃ u : V, (J u,D.operator ⟨J u,hJ u⟩) = z n := by
    obtain ⟨u,hu⟩ := (hz n).2
    have ho := D.operator.mem_graph_snd_inj' (D.operator.mem_graph ⟨J u,hJ u⟩)
      (hz n).1 hu
    refine ⟨u,Prod.ext hu ?_⟩
    exact ho
  choose u hu using hex
  have hu' : Tendsto (fun n => (J (u n),D.operator ⟨J (u n),hJ (u n)⟩))
      atTop (𝓝 (WithLp.ofLp w.val)) := by simpa only [hu] using ht
  have hl : Tendsto (fun n => graphLift D J hJ (u n)) atTop (𝓝 w) := by
    apply tendsto_subtype_rng.mpr
    exact ((WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.continuous.tendsto
      (WithLp.ofLp w.val)).comp hu'
  exact mem_closure_of_tendsto hl (Eventually.of_forall (fun n => Set.mem_range_self (u n)))

def rootData (ε : ℝ) (hε : 0 < ε) (h : ℝ) : KFCausalClosedGraphForm.Data Hilbert Hilbert where
  operator := rootOperator ε hε h
  closed := (rootOperator_selfAdjoint ε hε h).isClosed
  dense := (rootOperator_selfAdjoint ε hε h).dense_domain

abbrev RootForm (ε : ℝ) (hε : 0 < ε) (h : ℝ) :=
  KFCausalClosedGraphForm.FormSpace (rootData ε hε h)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ t : ℝ)
local notation "V" => AveragedSpace ε hε h (hamiltonian_bound ε h hb) hh m g κ t
local notation "J" => embedding ε hε h (hamiltonian_bound ε h hb) hh m g κ t
local notation "A" => energyOutput ε hε h (hamiltonian_bound ε h hb) hh m g κ t

def staticOutput : V →L[ℂ] EnergyOutputSpace := staticOutputLp.comp A

def source : V →ₗ[ℂ] RootForm ε hε h :=
  graphLift (rootData ε hε h) J
    (averaged_root_domain ε hε h (hamiltonian_bound ε h hb) hh m g κ t)

theorem source_embedding (u : V) :
    KFCausalClosedGraphForm.embedding (rootData ε hε h)
      (source ε hε h hh hb m g κ t u) = J u := rfl

theorem source_output (u : V) :
    KFCausalClosedGraphForm.energyOutput (rootData ε hε h)
      (source ε hε h hh hb m g κ t u) =
      rootOperator ε hε h ⟨J u,averaged_root_domain ε hε h
        (hamiltonian_bound ε h hb) hh m g κ t u⟩ := rfl

theorem source_output_norm (u : V) :
    ‖KFCausalClosedGraphForm.energyOutput (rootData ε hε h)
      (source ε hε h hh hb m g κ t u)‖ = ‖staticOutput ε hε h hh hb m g κ t u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact averaged_root_norm ε hε h (hamiltonian_bound ε h hb) hh m g κ t u

theorem source_norm (u : V) :
    ‖source ε hε h hh hb m g κ t u‖^2 =
      ‖J u‖^2 + ‖staticOutput ε hε h hh hb m g κ t u‖^2 := by
  exact (KFCausalClosedGraphForm.form_norm_identity (rootData ε hε h)
    (source ε hε h hh hb m g κ t u)).trans
    (congrArg₂ (fun x y : ℝ => x^2+y^2)
      (congrArg norm (source_embedding ε hε h hh hb m g κ t u))
      (source_output_norm ε hε h hh hb m g κ t u))

theorem source_dense : DenseRange (source ε hε h hh hb m g κ t) := by
  have he : (energyOperator ε hε h (hamiltonian_bound ε h hb) hh m g κ t).domain =
      (J).toLinearMap.range := by
    ext f
    exact energy_domain ε hε h (hamiltonian_bound ε h hb) hh m g κ t f
  have hc := KFCausalClockFloorStaticFormCore.static_form_core ε 1 h hε (by norm_num) hh hb m g κ t
  change ((rootOperator ε hε h).graph ⊓
    (energyOperator ε hε h (hamiltonian_bound ε h hb) hh m g κ t).domain.comap
      (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = _ at hc
  have hd := (congrArg (fun E : Submodule ℂ Hilbert =>
    ((rootOperator ε hε h).graph ⊓ E.comap (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure)
    he).symm.trans hc
  exact graphLift_dense (rootData ε hε h) J
    (averaged_root_domain ε hε h (hamiltonian_bound ε h hb) hh m g κ t) hd

#print axioms source_embedding
#print axioms source_output
#print axioms source_output_norm
#print axioms source_norm
#print axioms source_dense
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticRootSource
