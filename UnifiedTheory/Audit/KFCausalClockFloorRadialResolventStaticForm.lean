/- The radial resolvent regularizer lifts to a bounded operator on the
completed static form for all real couplings, preserving the static-output
closure domain, intertwining with the static projection from the completed
residual form, and converging strongly to the identity in the completed
static-form norm. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventResidual
import UnifiedTheory.Audit.KFCausalClockFloorResidualFormSplit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticForm
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalFiniteOutputRescaling (selected_apply)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp)
open KFCausalPhysicalEnergyTransport (staticOutput)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorRadialYosidaEnergy (energy_bound factorOutput)
open KFCausalClockFloorRadialYosidaForm (outputAction)
open KFCausalClockFloorRadialYosidaReference (wide_bound averagedAction averagedAction_embedding)
open KFCausalClockFloorRadialResolventRegularizer (action radial_domain)
open KFCausalClockFloorRadialResolventLeibniz (orbitExtra scaledOrbitExtra
  referenceOutputActionLp staticOutputLp_orbitExtra averagedAction_output
  reference_full_stability)
open KFCausalClockFloorRadialResolventResidual (referenceOutputResolventLp
  graph_sequence_tendsto)
open KFCausalClockFloorResidualFormSplit (staticLift staticLift_embedding)
open KFCausalUnitIntervalOrbit (angleMeasure)

private theorem range_closure_transport_correction
    {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (j : V →L[ℂ] X) (b : V →L[ℂ] Y) (d : X →L[ℂ] X) (l : Y →L[ℂ] Y) (c : X →L[ℂ] Y)
    (hs : ∀ u, ∃ v, j v=d (j u) ∧ b v=l (b u)+c (j u))
    (x : X) (y : Y) (hxy : (x,y) ∈ (j.prod b).toLinearMap.range.topologicalClosure) :
    (d x,l y+c x) ∈ (j.prod b).toLinearMap.range.topologicalClosure := by
  let S := (j.prod b).toLinearMap.range
  let P : X × Y →L[ℂ] X × Y :=
    (d.comp (ContinuousLinearMap.fst ℂ X Y)).prod
      (l.comp (ContinuousLinearMap.snd ℂ X Y)+c.comp (ContinuousLinearMap.fst ℂ X Y))
  have hS : S ≤ S.topologicalClosure.comap P.toLinearMap := by
    rintro z ⟨u,rfl⟩
    obtain ⟨v,hvJ,hvB⟩ := hs u
    exact S.le_topologicalClosure ⟨v,Prod.ext hvJ hvB⟩
  exact S.topologicalClosure_minimal hS (S.isClosed_topologicalClosure.preimage P.continuous) hxy

private def triangularGraphMap {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (D : H →L[ℂ] H) (R : K →L[ℂ] K) (C : H →L[ℂ] K) :
    WithLp 2 (H × K) →L[ℂ] WithLp 2 (H × K) :=
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ H K
  let b := (D.comp (ContinuousLinearMap.fst ℂ H K)).prod
    (R.comp (ContinuousLinearMap.snd ℂ H K)+C.comp (ContinuousLinearMap.fst ℂ H K))
  e.symm.toContinuousLinearMap.comp (b.comp e.toContinuousLinearMap)

private def triangularAction {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (G : KFCausalClosedGraphForm.Data H K)
    (D : H →L[ℂ] H) (R : K →L[ℂ] K) (C : H →L[ℂ] K)
    (hg : ∀ f g, (f,g) ∈ G.operator.graph → (D f,R g+C f) ∈ G.operator.graph) :
    KFCausalClosedGraphForm.FormSpace G →L[ℂ] KFCausalClosedGraphForm.FormSpace G where
  toFun u := ⟨triangularGraphMap D R C u.val,
    hg (KFCausalClosedGraphForm.embedding G u) (KFCausalClosedGraphForm.energyOutput G u) u.property⟩
  map_add' u v := by apply Subtype.ext; exact (triangularGraphMap D R C).map_add u.val v.val
  map_smul' a u := by apply Subtype.ext; exact (triangularGraphMap D R C).map_smul a u.val
  cont := ((triangularGraphMap D R C).continuous.comp continuous_subtype_val).subtype_mk _

private theorem triangularAction_embedding {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (G : KFCausalClosedGraphForm.Data H K)
    (D : H →L[ℂ] H) (R : K →L[ℂ] K) (C : H →L[ℂ] K)
    (hg : ∀ f g, (f,g) ∈ G.operator.graph → (D f,R g+C f) ∈ G.operator.graph)
    (u : KFCausalClosedGraphForm.FormSpace G) :
    KFCausalClosedGraphForm.embedding G (triangularAction G D R C hg u)=
      D (KFCausalClosedGraphForm.embedding G u) := rfl

private theorem triangularAction_output {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (G : KFCausalClosedGraphForm.Data H K)
    (D : H →L[ℂ] H) (R : K →L[ℂ] K) (C : H →L[ℂ] K)
    (hg : ∀ f g, (f,g) ∈ G.operator.graph → (D f,R g+C f) ∈ G.operator.graph)
    (u : KFCausalClosedGraphForm.FormSpace G) :
    KFCausalClosedGraphForm.energyOutput G (triangularAction G D R C hg u)=
      R (KFCausalClosedGraphForm.energyOutput G u)+C (KFCausalClosedGraphForm.embedding G u) := rfl

private theorem static_linear
    (L : EnergyOutputSpace →L[ℂ] EnergyOutputSpace)
    (a b c : EnergyOutputSpace) (s0 s1 : EnergyOutputSpace)
    (hs0 : s0=staticOutputLp a)
    (hs1 : s1=staticOutputLp b)
    (ha : a=L b+c)
    (hL : staticOutputLp (L b)=L (staticOutputLp b))
    (hc : staticOutputLp c=c) :
    s0=L s1+c := by
  rw [hs0,hs1,ha,map_add,hL,hc]

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi*ε/3) (hh : h ≠ 0) (m g k t : ℝ)

private theorem outputAction_apply (z : Output (Fin 8) Hilbert) (i : Fin 8) :
    outputAction ε hε h N hN hb z i=factorOutput ε hε h N hN hb i (z i) := rfl

private theorem staticOutput_apply (z : Output (Fin 8) Hilbert) (i : Fin 8) :
    staticOutput z i=if i.val < 3 then z i else 0 :=
  selected_apply (fun j : Fin 8 => j.val < 3) z i

private theorem point_static_outputAction (z : Output (Fin 8) Hilbert) :
    staticOutput (outputAction ε hε h N hN hb z)=
      outputAction ε hε h N hN hb (staticOutput z) := by
  apply PiLp.ext
  intro i
  rw [staticOutput_apply,outputAction_apply,outputAction_apply,staticOutput_apply]
  by_cases h3 : i.val < 3
  · simp only [h3,if_true]
  · simp only [h3,if_false,map_zero]

theorem staticOutputLp_referenceOutputActionLp (z : EnergyOutputSpace) :
    staticOutputLp (referenceOutputActionLp ε hε h N hN hb z)=
      referenceOutputActionLp ε hε h N hN hb (staticOutputLp z) := by
  let w1 := referenceOutputActionLp ε hε h N hN hb z
  let w2 := staticOutputLp z
  apply Lp.ext
  filter_upwards [staticOutput.coeFn_compLp w1,
    (outputAction ε hε h N hN hb).coeFn_compLp z,
    (outputAction ε hε h N hN hb).coeFn_compLp w2,
    staticOutput.coeFn_compLp z] with θ h1 h2 h3 h4
  change staticOutput.compLp w1 θ=(outputAction ε hε h N hN hb).compLp w2 θ
  rw [h1,h3]
  change staticOutput ((outputAction ε hε h N hN hb).compLp z θ)=
    outputAction ε hε h N hN hb (staticOutput.compLp z θ)
  rw [h2,h4,point_static_outputAction]

local notation "hw" => wide_bound ε hε h hb
local notation "hs" => energy_bound ε hε h hb
local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN
local notation "AV" => KFCausalClockFloorAveragedEnergy.AveragedSpace ε hε h (hamiltonian_bound ε h hw) hh m g k 0
local notation "AJ" => KFCausalClockFloorAveragedEnergy.embedding ε hε h (hamiltonian_bound ε h hw) hh m g k 0
local notation "AA" => KFCausalClockFloorAveragedEnergy.energyOutput ε hε h (hamiltonian_bound ε h hw) hh m g k 0
local notation "AS0" => KFCausalClockFloorStaticRootSource.staticOutput ε hε h hh hw m g k 0
local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k 0
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k 0
local notation "RA" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hw m g k 0
local notation "SM" => KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hw m g k 0
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw m g k 0
local notation "TV" => KFCausalClockFloorStaticHamiltonian.StaticForm ε hε h hh hw m g k 0
local notation "TJ" => KFCausalClosedGraphForm.embedding TD
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hw m g k t
local notation "Kr" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h

private theorem staticMap_apply (u : RV) :
    SM u=staticOutputLp (RA u) :=
  ContinuousLinearMap.comp_apply staticOutputLp RA u

private theorem averaged_staticOutput_apply (a : AV) :
    AS0 a=staticOutputLp (AA a) :=
  ContinuousLinearMap.comp_apply staticOutputLp AA a

theorem reference_static_stability (u : RV) :
    ∃ v : RV, RJ v=M (RJ u) ∧
      SM v=referenceOutputActionLp ε hε h N hN hb (SM u)+
        orbitExtra ε hε h N hN hh m g k (RJ u) := by
  have hfull := reference_full_stability ε hε h N hN hb hh m g k u
  let v : RV := Classical.choose hfull
  have hv := Classical.choose_spec hfull
  refine ⟨v,hv.1,?_⟩
  exact static_linear (referenceOutputActionLp ε hε h N hN hb)
    (RA v) (RA u) (orbitExtra ε hε h N hN hh m g k (RJ u)) (SM v) (SM u)
    (staticMap_apply ε hε h hb hh m g k v)
    (staticMap_apply ε hε h hb hh m g k u)
    hv.2
    (staticOutputLp_referenceOutputActionLp ε hε h N hN hb (RA u))
    (staticOutputLp_orbitExtra ε hε h N hN hh m g k (RJ u))

private theorem averaged_static_stability (a : AV) :
    ∃ b : AV, AJ b=M (AJ a) ∧
      AS0 b=referenceOutputActionLp ε hε h N hN hb (AS0 a)+
        orbitExtra ε hε h N hN hh m g k (AJ a) := by
  let b : AV := averagedAction ε hε h N hN hb hh m g k a
  refine ⟨b,averagedAction_embedding ε hε h N hN hb hh m g k a,?_⟩
  exact static_linear (referenceOutputActionLp ε hε h N hN hb)
    (AA b) (AA a) (orbitExtra ε hε h N hN hh m g k (AJ a)) (AS0 b) (AS0 a)
    (averaged_staticOutput_apply ε hε h hb hh m g k b)
    (averaged_staticOutput_apply ε hε h hb hh m g k a)
    (averagedAction_output ε hε h N hN hb hh m g k a)
    (staticOutputLp_referenceOutputActionLp ε hε h N hN hb (AA a))
    (staticOutputLp_orbitExtra ε hε h N hN hh m g k (AJ a))

theorem yosida_graph (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (Tstat).graph) :
    (M f,referenceOutputActionLp ε hε h N hN hb z+
      orbitExtra ε hε h N hN hh m g k f) ∈ (Tstat).graph := by
  rw [KFCausalClockFloorStaticOutputClosure.operator_graph,
    KFCausalClockFloorStaticOutputClosure.initialGraph] at hz ⊢
  exact range_closure_transport_correction (AJ) (AS0) (M)
    (referenceOutputActionLp ε hε h N hN hb)
    (orbitExtra ε hε h N hN hh m g k)
    (averaged_static_stability ε hε h N hN hb hh m g k) f z hz

theorem graph_action (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (Tstat).graph) :
    (action ε hε h N hN f,
      referenceOutputResolventLp ε hε h N hN hb z+
        (-scaledOrbitExtra ε hε h N hN hh m g k) f) ∈ (Tstat).graph := by
  have hm := yosida_graph ε hε h N hN hb hh m g k f z hz
  have he := (Tstat).graph.sub_mem hz ((Tstat).graph.smul_mem (N⁻¹:ℂ) hm)
  change (action ε hε h N hN f,
    z-(N⁻¹:ℂ) • (referenceOutputActionLp ε hε h N hN hb z+
      orbitExtra ε hε h N hN hh m g k f)) ∈ (Tstat).graph at he
  have hout : z-(N⁻¹:ℂ) • (referenceOutputActionLp ε hε h N hN hb z+
      orbitExtra ε hε h N hN hh m g k f)=
      referenceOutputResolventLp ε hε h N hN hb z+
        (-scaledOrbitExtra ε hε h N hN hh m g k) f := by
    change z-(N⁻¹:ℂ) • (referenceOutputActionLp ε hε h N hN hb z+
      orbitExtra ε hε h N hN hh m g k f)=
      (z-(N⁻¹:ℂ) • referenceOutputActionLp ε hε h N hN hb z)+
        -((N⁻¹:ℂ) • orbitExtra ε hε h N hN hh m g k f)
    rw [smul_add]
    abel
  exact (congrArg (fun y : EnergyOutputSpace =>
    (action ε hε h N hN f,y) ∈ (Tstat).graph) hout).mp he

def formAction : TV →L[ℂ] TV :=
  triangularAction TD (action ε hε h N hN)
    (referenceOutputResolventLp ε hε h N hN hb)
    (-scaledOrbitExtra ε hε h N hN hh m g k)
    (graph_action ε hε h N hN hb hh m g k)

theorem formAction_embedding (w : TV) :
    TJ (formAction ε hε h N hN hb hh m g k w)=action ε hε h N hN (TJ w) :=
  triangularAction_embedding TD (action ε hε h N hN)
    (referenceOutputResolventLp ε hε h N hN hb)
    (-scaledOrbitExtra ε hε h N hN hh m g k)
    (graph_action ε hε h N hN hb hh m g k) w

theorem formAction_output (w : TV) :
    TB (formAction ε hε h N hN hb hh m g k w)=
      referenceOutputResolventLp ε hε h N hN hb (TB w)+
        (-scaledOrbitExtra ε hε h N hN hh m g k) (TJ w) :=
  triangularAction_output TD (action ε hε h N hN)
    (referenceOutputResolventLp ε hε h N hN hb)
    (-scaledOrbitExtra ε hε h N hN hh m g k)
    (graph_action ε hε h N hN hb hh m g k) w

theorem domain_action (f : Hilbert) (hf : f ∈ (Tstat).domain) :
    action ε hε h N hN f ∈ (Tstat).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (graph_action ε hε h N hN hb hh m g k f _ ((Tstat).mem_graph ⟨f,hf⟩))

theorem domain_intersection_action (f : Hilbert) (hf : f ∈ (Tstat).domain) :
    action ε hε h N hN f ∈ (Kr).domain ∧ action ε hε h N hN f ∈ (Tstat).domain :=
  ⟨radial_domain ε hε h N hN f,domain_action ε hε h N hN hb hh m g k f hf⟩

theorem staticLift_formAction (w : SV) :
    staticLift ε hε h hh hw m g k t
      (KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m g k t w)=
    formAction ε hε h N hN hb hh m g k
      (staticLift ε hε h hh hw m g k t w) :=
  KFCausalClosedGraphForm.embedding_injective TD
    ((staticLift_embedding ε hε h hh hw m g k t
      (KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m g k t w)).trans
      ((KFCausalClockFloorRadialResolventResidual.formAction_embedding
        ε hε h N hN hb hh m g k t w).trans
        ((congrArg (action ε hε h N hN)
          (staticLift_embedding ε hε h hh hw m g k t w).symm).trans
          (formAction_embedding ε hε h N hN hb hh m g k
            (staticLift ε hε h hh hw m g k t w)).symm)))

theorem form_sequence_tendsto (w : TV) :
    Tendsto (fun n : ℕ =>
      formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k w) atTop (𝓝 w) := by
  have hg := graph_sequence_tendsto ε hε h hb hh m g k (TJ w) (TB w)
  apply tendsto_subtype_rng.mpr
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert EnergyOutputSpace).symm.continuous.tendsto
    (WithLp.ofLp w.val)).comp hg

theorem energy_sequence_tendsto (w : TV) :
    Tendsto (fun n : ℕ =>
      ‖TB (formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k w)‖^2)
      atTop (𝓝 (‖TB w‖^2)) :=
  (((TB).continuous.tendsto w).comp
    (form_sequence_tendsto ε hε h hb hh m g k w)).norm.pow 2

#print axioms staticOutputLp_referenceOutputActionLp
#print axioms reference_static_stability
#print axioms yosida_graph
#print axioms graph_action
#print axioms formAction_embedding
#print axioms formAction_output
#print axioms domain_action
#print axioms domain_intersection_action
#print axioms staticLift_formAction
#print axioms form_sequence_tendsto
#print axioms energy_sequence_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticForm
