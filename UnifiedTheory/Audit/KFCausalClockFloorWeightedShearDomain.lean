/- The signed response extends to the natural graph of JQ, where Q is
the derived clock weight. A shear-regular graph core is constructed by
unitary averaging. This graph is not the Hamiltonian energy form domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorSignedShearResponse
import UnifiedTheory.Audit.KFCausalClosedOperatorUnitaryCommutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorWeightedShearDomain
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight
open UnifiedTheory.Audit.KFCausalClockFloorSignedShearResponse
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum
open UnifiedTheory.Audit.KFCausalTransverseShearTransport (transport transport_compose)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse (response)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hbound : |h| ≤ 2*Real.pi*ε/3) (hne : h ≠ 0)
local notation "Q" => root ε hε h hbound hne
local notation "J" => shearMomentum h
local notation "responseL" => KFCausalClockFloorVacuumMomentumResponse.response ε hε h hbound

def weightedGraph : Submodule ℂ (Hilbert × Hilbert) where
  carrier := {z | (Q z.1,z.2) ∈ (J).graph}
  zero_mem' := by
    change (Q 0,0) ∈ (J).graph
    rw [map_zero]
    exact (J).graph.zero_mem
  add_mem' := by
    intro z w hz hw
    simpa using (J).graph.add_mem hz hw
  smul_mem' := by
    intro c z hz
    simpa using (J).graph.smul_mem c hz

def weightedMomentum : Hilbert →ₗ.[ℂ] Hilbert := (weightedGraph ε hε h hbound hne).toLinearPMap
local notation "M" => weightedMomentum ε hε h hbound hne

theorem weighted_graph_eq : (M).graph = weightedGraph ε hε h hbound hne := by
  apply Submodule.toLinearPMap_graph_eq
  intro z hz hzero
  change (Q z.1,z.2) ∈ (J).graph at hz
  rw [hzero,map_zero] at hz
  exact (J).mem_graph_snd_inj hz (J).graph.zero_mem rfl

theorem weighted_graph (g k : Hilbert) : (g,k) ∈ (M).graph ↔ (Q g,k) ∈ (J).graph := by
  rw [weighted_graph_eq]
  rfl

theorem weighted_domain (g : Hilbert) : g ∈ (M).domain ↔ Q g ∈ (J).domain := by
  simp only [LinearPMap.mem_domain_iff,weighted_graph ε hε h hbound hne]

theorem weighted_closed : (M).IsClosed := by
  change IsClosed ((M).graph : Set (Hilbert × Hilbert))
  have hc : Continuous (fun z : Hilbert × Hilbert => (Q z.1,z.2)) :=
    ((Q).continuous.comp continuous_fst).prodMk continuous_snd
  convert (shear_closed h hne).preimage hc using 1
  ext z
  exact weighted_graph ε hε h hbound hne z.1 z.2

theorem shear_domain_included (g : Hilbert) (hg : g ∈ (J).domain) : g ∈ (M).domain := by
  obtain ⟨j,hj⟩ := LinearPMap.mem_domain_iff.mp hg
  exact LinearPMap.mem_domain_of_mem_graph ((weighted_graph ε hε h hbound hne g (Q j)).mpr
    (root_shear_graph ε hε h hbound hne g j hj))

theorem weighted_dense : Dense ((M).domain : Set Hilbert) :=
  (shear_dense h).mono (shear_domain_included ε hε h hbound hne)

theorem weighted_transport (t : ℝ) (g k : Hilbert) (hg : (g,k) ∈ (M).graph) :
    (transport t g,transport t k) ∈ (M).graph := by
  have hj := (weighted_graph ε hε h hbound hne g k).mp hg
  have ho := KFCausalStrongUnitaryProductDerivative.graph_of_commutes shearGroup h hne
    (transport t) (fun u f => by
      change transport u (transport t f) = transport t (transport u f)
      rw [transport_compose,transport_compose,add_comm t u]) (Q g) k hj
  change (transport t (Q g),transport t k) ∈ (J).graph at ho
  rw [KFCausalTransverseShearClockCommutation.clock_multiplier _
    (fun s => (rootValue ε h s:ℂ)) (root_coe ε hε h hbound hne) t g] at ho
  exact (weighted_graph ε hε h hbound hne _ _).mpr ho

def regularGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (M).graph ⊓ (J).domain.prod (J).domain
local notation "G" => regularGraph ε hε h hbound hne

theorem regular_graph_core : (G).topologicalClosure = (M).graph :=
  KFCausalClosedOperatorUnitaryCommutation.regular_graph_core shearGroup (M)
    (weighted_closed ε hε h hbound hne) (weighted_transport ε hε h hbound hne) h

theorem graph_approximation (g k : Hilbert) (hg : (g,k) ∈ (M).graph) :
    ∃ z : ℕ → Hilbert × Hilbert, (∀ n, z n ∈ G) ∧ Tendsto z atTop (𝓝 (g,k)) := by
  apply mem_closure_iff_seq_limit.mp
  change (g,k) ∈ (G).topologicalClosure
  rw [regular_graph_core]
  exact hg

def graphResponse (z : Hilbert × Hilbert) : ℝ :=
  responseL z.1+(4/ε^2)*(inner ℂ (Q z.1) z.2).re

theorem graphResponse_continuous : Continuous (graphResponse ε hε h hbound hne) :=
  ((KFCausalClockFloorVacuumMomentumResponse.response_continuous ε hε h hbound).comp continuous_fst).add
    (continuous_const.mul (Complex.continuous_re.comp
      (((Q).continuous.comp continuous_fst).inner continuous_snd)))

theorem graphResponse_matches (g j : Hilbert) (hj : (g,j) ∈ (J).graph) :
    response ε hε h hbound g j = graphResponse ε hε h hbound hne (g,Q j) :=
  response_weighted_shear ε hε h hbound hne g j hj

theorem graphResponse_bound (g k : Hilbert) :
    |graphResponse ε hε h hbound hne (g,k)-responseL g| ≤
      (4/ε^2)*‖KFCausalClockFloorDefectOperator.defectOperator ε hε g‖*‖k‖ := by
  change |responseL g+(4/ε^2)*(inner ℂ (Q g) k).re-responseL g| ≤ _
  rw [add_sub_cancel_left,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 4/ε^2)]
  have hi := (Complex.abs_re_le_norm (inner ℂ (Q g) k)).trans
    ((norm_inner_le_norm (𝕜 := ℂ) (Q g) k).trans
      (mul_le_mul_of_nonneg_right (root_norm_le_defect ε hε h hbound hne g) (norm_nonneg k)))
  exact (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 4/ε^2)).trans_eq (by ring)

def coreMomentum (z : G) : Hilbert := (J) ⟨z.val.1,z.property.2.1⟩
def coreResponse (z : G) : ℝ := response ε hε h hbound z.val.1 (coreMomentum ε hε h hbound hne z)

theorem coreResponse_eq (z : G) :
    coreResponse ε hε h hbound hne z = graphResponse ε hε h hbound hne z.val := by
  have hj := (J).mem_graph ⟨z.val.1,z.property.2.1⟩
  have hk := (weighted_graph ε hε h hbound hne z.val.1 z.val.2).mp z.property.1
  have he := (J).mem_graph_snd_inj hk (root_shear_graph ε hε h hbound hne _ _ hj) rfl
  change z.val.2 = Q (coreMomentum ε hε h hbound hne z) at he
  change response ε hε h hbound z.val.1 _ = _
  rw [graphResponse,he]
  exact response_weighted_shear ε hε h hbound hne _ _ hj

theorem core_response_approximation (g k : Hilbert) (hg : (g,k) ∈ (M).graph) :
    ∃ z : ℕ → G, Tendsto (fun n => (z n).val) atTop (𝓝 (g,k)) ∧
      Tendsto (fun n => coreResponse ε hε h hbound hne (z n)) atTop
        (𝓝 (graphResponse ε hε h hbound hne (g,k))) := by
  obtain ⟨w,hw,ht⟩ := graph_approximation ε hε h hbound hne g k hg
  let z : ℕ → G := fun n => ⟨w n,hw n⟩
  refine ⟨z,ht,?_⟩
  have hc := (graphResponse_continuous ε hε h hbound hne).continuousAt.tendsto.comp ht
  exact hc.congr' (Eventually.of_forall fun n => (coreResponse_eq ε hε h hbound hne (z n)).symm)

theorem extension_unique (F : Hilbert × Hilbert → ℝ)
    (hF : ContinuousOn F ((M).graph : Set (Hilbert × Hilbert)))
    (hagree : ∀ z : G, F z.val = coreResponse ε hε h hbound hne z) :
    ∀ z ∈ (M).graph, F z = graphResponse ε hε h hbound hne z := by
  rintro ⟨g,k⟩ hg
  obtain ⟨z,hz,hr⟩ := core_response_approximation ε hε h hbound hne g k hg
  have ht : Tendsto (fun n => (z n).val) atTop (𝓝[((M).graph : Set (Hilbert × Hilbert))] (g,k)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz,Eventually.of_forall (fun n => (z n).property.1)⟩
  exact tendsto_nhds_unique ((hF (g,k) hg).tendsto.comp ht)
    (hr.congr' (Eventually.of_forall fun n => (hagree (z n)).symm))

#print axioms weighted_graph_eq
#print axioms weighted_graph
#print axioms weighted_domain
#print axioms weighted_closed
#print axioms shear_domain_included
#print axioms weighted_dense
#print axioms weighted_transport
#print axioms regular_graph_core
#print axioms graph_approximation
#print axioms graphResponse_continuous
#print axioms graphResponse_matches
#print axioms graphResponse_bound
#print axioms coreResponse_eq
#print axioms core_response_approximation
#print axioms extension_unique
end
end UnifiedTheory.Audit.KFCausalClockFloorWeightedShearDomain
