/- Completion of the ORIGINAL static output on the interacting averaged
form. The extension is constructed from its actual dense root-graph
sources; its graph is proved equal to the closure of that original graph.
It is not defined by replacing the energy outputs with a multiplier. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticRootSource

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticOutputClosure
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorStaticRootSource
open KFCausalClockFloorStaticMultiplierForm (rootOperator)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedEnergy
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)

private theorem equal_norm_inner {V H K : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (A : V →L[ℂ] H) (B : V →L[ℂ] K) (hn : ∀ u, ‖A u‖ = ‖B u‖) (u v : V) :
    inner ℂ (A u) (A v) = inner ℂ (B u) (B v) := by
  rw [inner_eq_sum_norm_sq_div_four,inner_eq_sum_norm_sq_div_four]
  simp only [← map_add,← map_sub,← map_smul,hn]

private theorem closed_pair_range {H K F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (D : KFCausalClosedGraphForm.Data H K)
    (L : KFCausalClosedGraphForm.FormSpace D →L[ℂ] F)
    (hn : ∀ u, ‖L u‖ = ‖KFCausalClosedGraphForm.energyOutput D u‖) :
    IsClosed (Set.range ((KFCausalClosedGraphForm.embedding D).prod L)) := by
  let T := (KFCausalClosedGraphForm.embedding D).prod L
  have hb (u : KFCausalClosedGraphForm.FormSpace D) : ‖u‖ ≤ 2*‖T u‖ := by
    have h0 := norm_fst_le (T u)
    have h1 := norm_snd_le (T u)
    have hs := KFCausalClosedGraphForm.form_norm_identity D u
    rw [← hn u] at hs
    have h0s := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h0
    have h1s := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h1
    change ‖KFCausalClosedGraphForm.embedding D u‖^2 ≤ ‖T u‖^2 at h0s
    change ‖L u‖^2 ≤ ‖T u‖^2 at h1s
    nlinarith [norm_nonneg u,norm_nonneg (T u)]
  have ha : AntilipschitzWith 2 T := T.antilipschitz_of_bound hb
  exact ha.isClosed_range T.uniformContinuous

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ t : ℝ)
local notation "V" => AveragedSpace ε hε h (hamiltonian_bound ε h hb) hh m g κ t
local notation "J" => embedding ε hε h (hamiltonian_bound ε h hb) hh m g κ t
local notation "A" => staticOutput ε hε h hh hb m g κ t
local notation "D" => rootData ε hε h
local notation "S" => source ε hε h hh hb m g κ t

private theorem source_bound (u : V) : ‖A u‖ ≤ ‖S u‖ := by
  exact (source_output_norm ε hε h hh hb m g κ t u).symm.le.trans
    (WithLp.norm_snd_le Hilbert (S u).val)

def extension : RootForm ε hε h →L[ℂ] EnergyOutputSpace :=
  (A).toLinearMap.extendOfNorm S

theorem extension_source (u : V) : extension ε hε h hh hb m g κ t (S u) = A u :=
  LinearMap.extendOfNorm_eq (source_dense ε hε h hh hb m g κ t)
    ⟨1,fun v => by simpa only [one_mul] using source_bound ε hε h hh hb m g κ t v⟩ u

theorem extension_norm (u : RootForm ε hε h) :
    ‖extension ε hε h hh hb m g κ t u‖ = ‖KFCausalClosedGraphForm.energyOutput D u‖ := by
  have he := (source_dense ε hε h hh hb m g κ t).equalizer
    (continuous_norm.comp (extension ε hε h hh hb m g κ t).continuous)
    (continuous_norm.comp (KFCausalClosedGraphForm.energyOutput D).continuous)
    (funext (fun v => (congrArg norm (extension_source ε hε h hh hb m g κ t v)).trans
      (source_output_norm ε hε h hh hb m g κ t v).symm))
  exact congrFun he u

theorem extension_inner (u v : RootForm ε hε h) :
    inner ℂ (extension ε hε h hh hb m g κ t u) (extension ε hε h hh hb m g κ t v) =
      inner ℂ (KFCausalClosedGraphForm.energyOutput D u) (KFCausalClosedGraphForm.energyOutput D v) :=
  equal_norm_inner _ _ (extension_norm ε hε h hh hb m g κ t) u v

def graphMap : RootForm ε hε h →L[ℂ] (Hilbert × EnergyOutputSpace) :=
  (KFCausalClosedGraphForm.embedding D).prod (extension ε hε h hh hb m g κ t)

def initialGraph : Submodule ℂ (Hilbert × EnergyOutputSpace) := ((J).prod A).toLinearMap.range

theorem graphMap_closed_range : IsClosed (Set.range (graphMap ε hε h hh hb m g κ t)) :=
  closed_pair_range D (extension ε hε h hh hb m g κ t) (extension_norm ε hε h hh hb m g κ t)

theorem initialGraph_closure : (initialGraph ε hε h hh hb m g κ t).topologicalClosure =
    (graphMap ε hε h hh hb m g κ t).toLinearMap.range := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ ?_ (graphMap_closed_range ε hε h hh hb m g κ t)
    rintro z ⟨u,rfl⟩
    refine ⟨S u,Prod.ext (source_embedding ε hε h hh hb m g κ t u)
      (extension_source ε hε h hh hb m g κ t u)⟩
  · rintro z ⟨u,rfl⟩
    refine (source_dense ε hε h hh hb m g κ t).induction_on
      (p := fun v => graphMap ε hε h hh hb m g κ t v ∈
        (initialGraph ε hε h hh hb m g κ t).topologicalClosure) u ?_ ?_
    · exact (initialGraph ε hε h hh hb m g κ t).isClosed_topologicalClosure.preimage
        (graphMap ε hε h hh hb m g κ t).continuous
    · intro v
      apply (initialGraph ε hε h hh hb m g κ t).le_topologicalClosure
      refine ⟨v,?_⟩
      exact (Prod.ext (source_embedding ε hε h hh hb m g κ t v)
        (extension_source ε hε h hh hb m g κ t v)).symm

def operator : Hilbert →ₗ.[ℂ] EnergyOutputSpace :=
  (graphMap ε hε h hh hb m g κ t).toLinearMap.range.toLinearPMap

theorem operator_graph : (operator ε hε h hh hb m g κ t).graph =
    (initialGraph ε hε h hh hb m g κ t).topologicalClosure := by
  rw [initialGraph_closure]
  apply Submodule.toLinearPMap_graph_eq
  rintro z ⟨u,rfl⟩ hz
  have hu : u = 0 := KFCausalClosedGraphForm.embedding_injective D
    (hz.trans (map_zero _).symm)
  change extension ε hε h hh hb m g κ t u = 0
  rw [hu,map_zero]

theorem operator_closed : (operator ε hε h hh hb m g κ t).IsClosed := by
  rw [LinearPMap.IsClosed,operator_graph]
  exact (initialGraph ε hε h hh hb m g κ t).isClosed_topologicalClosure

theorem root_form_graph (u : RootForm ε hε h) :
    (KFCausalClosedGraphForm.embedding D u,extension ε hε h hh hb m g κ t u) ∈
      (operator ε hε h hh hb m g κ t).graph := by
  rw [operator_graph,initialGraph_closure]
  exact ⟨u,rfl⟩

theorem operator_domain (f : Hilbert) :
    f ∈ (operator ε hε h hh hb m g κ t).domain ↔ f ∈ (rootOperator ε hε h).domain := by
  constructor
  · intro hf
    have hg := (operator ε hε h hh hb m g κ t).mem_graph ⟨f,hf⟩
    rw [operator_graph,initialGraph_closure] at hg
    obtain ⟨u,hu⟩ := hg
    have he := congrArg Prod.fst hu
    change KFCausalClosedGraphForm.embedding D u = f at he
    have hd : KFCausalClosedGraphForm.embedding D u ∈ (rootOperator ε hε h).domain :=
      LinearPMap.mem_domain_of_mem_graph u.property
    exact he ▸ hd
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph
      (root_form_graph ε hε h hh hb m g κ t (KFCausalClosedGraphForm.graphVector D ⟨f,hf⟩))

theorem operator_dense : Dense ((operator ε hε h hh hb m g κ t).domain : Set Hilbert) := by
  have he : ((operator ε hε h hh hb m g κ t).domain : Set Hilbert) =
      (rootOperator ε hε h).domain := Set.ext (operator_domain ε hε h hh hb m g κ t)
  rw [he]
  exact (KFCausalClockFloorStaticMultiplierForm.rootOperator_selfAdjoint ε hε h).dense_domain

#print axioms extension_source
#print axioms extension_norm
#print axioms extension_inner
#print axioms graphMap_closed_range
#print axioms initialGraph_closure
#print axioms operator_graph
#print axioms operator_closed
#print axioms root_form_graph
#print axioms operator_domain
#print axioms operator_dense
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticOutputClosure
