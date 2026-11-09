/- The radial resolvent regularizer lifts to a bounded operator on the full
completed eight-row interacting form space at every time t and for all real
couplings, compatible with both the growing-form and residual-form
projections, mapping Dom Eavg(t) into Dom Kr ∩ Dom Eavg(t), and converging
strongly to the identity in the full interacting form norm. -/
import UnifiedTheory.Audit.KFCausalClockFloorResidualFormReconstruction

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventAveragedForm
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer (action radial_domain)
open KFCausalClockFloorRadialResolventLeibniz (orbitExtra scaledOrbitExtra
  referenceOutputActionLp timeOutputLp_orbitExtra reference_full_stability)
open KFCausalClockFloorRadialResolventResidual (referenceOutputResolventLp
  timeOutputLp_referenceOutputActionLp graph_sequence_tendsto)

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

private theorem pair_embedding (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (f : Hilbert) (z : EnergyOutputSpace) (hz : (f,z) ∈ D.operator.graph) :
    KFCausalClosedGraphForm.embedding D ⟨WithLp.toLp 2 (f,z),hz⟩=f := rfl

private theorem pair_output (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (f : Hilbert) (z : EnergyOutputSpace) (hz : (f,z) ∈ D.operator.graph) :
    KFCausalClosedGraphForm.energyOutput D ⟨WithLp.toLp 2 (f,z),hz⟩=z := rfl

private theorem time_linear (t : ℝ)
    (L : EnergyOutputSpace →L[ℂ] EnergyOutputSpace)
    (C : Hilbert →L[ℂ] EnergyOutputSpace)
    (a b : EnergyOutputSpace) (s0 s1 : EnergyOutputSpace)
    (f0 f1 : Hilbert)
    (hs0 : s0=timeOutputLp 0 t a)
    (hs1 : timeOutputLp 0 t b=s1)
    (hf : f0=f1)
    (ha : a=L b+C f0)
    (hL1 : timeOutputLp 0 t (L b)=L (timeOutputLp 0 t b))
    (hc1 : timeOutputLp 0 t (C f0)=C f0) :
    s0=L s1+C f1 := by
  rw [hs0,ha,map_add,hL1,hs1,hc1,hf]

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi*ε/3) (hh : h ≠ 0) (m g k t : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN
local notation "TD" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hw m g k t
local notation "VT" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k t
local notation "JT" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k t
local notation "AT" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hw m g k t
local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k 0
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k 0
local notation "RA" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hw m g k 0
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hw) hh m g k t
local notation "Kr" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h

theorem averaged_time_stability (u : VT) :
    ∃ v : VT, JT v=M (JT u) ∧
      AT v=referenceOutputActionLp ε hε h N hN hb (AT u)+
        orbitExtra ε hε h N hN hh m g k (JT u) := by
  let u0 := KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hw m g k t 0 u
  have hfull := reference_full_stability ε hε h N hN hb hh m g k u0
  let v0 : RV := Classical.choose hfull
  have hv0 := Classical.choose_spec hfull
  let v := KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hw m g k 0 t v0
  have hju : RJ u0=JT u :=
    KFCausalClockFloorAveragedFormTransport.transfer_embedding ε hε h hh hw m g k t 0 u
  refine ⟨v,?_ ,?_⟩
  · exact (KFCausalClockFloorAveragedFormTransport.transfer_embedding ε hε h hh hw m g k 0 t v0).trans
      (hv0.1.trans (congrArg M hju))
  · have hau : timeOutputLp 0 t (RA u0)=AT u :=
      (KFCausalClockFloorAveragedFormTransport.transfer_energyOutput
        ε hε h hh hw m g k 0 t u0).symm.trans
        (congrArg AT (KFCausalClockFloorAveragedFormTransport.transfer_inverse ε hε h hh hw m g k t 0 u))
    exact time_linear t (referenceOutputActionLp ε hε h N hN hb)
      (orbitExtra ε hε h N hN hh m g k)
      (RA v0) (RA u0) (AT v) (AT u) (RJ u0) (JT u)
      (KFCausalClockFloorAveragedFormTransport.transfer_energyOutput ε hε h hh hw m g k 0 t v0)
      hau hju hv0.2
      (timeOutputLp_referenceOutputActionLp ε hε h N hN hb t (RA u0))
      (timeOutputLp_orbitExtra ε hε h N hN hh m g k t (RJ u0))

theorem yosida_graph (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (Eavg).graph) :
    (M f,referenceOutputActionLp ε hε h N hN hb z+
      orbitExtra ε hε h N hN hh m g k f) ∈ (Eavg).graph := by
  let u : VT := ⟨WithLp.toLp 2 (f,z),hz⟩
  have hst := averaged_time_stability ε hε h N hN hb hh m g k t u
  let v : VT := Classical.choose hst
  have hv := Classical.choose_spec hst
  have hj' : JT v=M f := hv.1.trans (congrArg M (pair_embedding TD f z hz))
  have ha' : AT v=referenceOutputActionLp ε hε h N hN hb z+
      orbitExtra ε hε h N hN hh m g k f :=
    hv.2.trans (congrArg₂ (·+·)
      (congrArg (referenceOutputActionLp ε hε h N hN hb) (pair_output TD f z hz))
      (congrArg (orbitExtra ε hε h N hN hh m g k) (pair_embedding TD f z hz)))
  exact (congrArg₂ (fun x y => (x,y) ∈ (Eavg).graph) hj' ha').mp v.property

theorem graph_action (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (Eavg).graph) :
    (action ε hε h N hN f,
      referenceOutputResolventLp ε hε h N hN hb z+
        (-scaledOrbitExtra ε hε h N hN hh m g k) f) ∈ (Eavg).graph := by
  have hm := yosida_graph ε hε h N hN hb hh m g k t f z hz
  have he := (Eavg).graph.sub_mem hz ((Eavg).graph.smul_mem (N⁻¹:ℂ) hm)
  change (action ε hε h N hN f,
    z-(N⁻¹:ℂ) • (referenceOutputActionLp ε hε h N hN hb z+
      orbitExtra ε hε h N hN hh m g k f)) ∈ (Eavg).graph at he
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
    (action ε hε h N hN f,y) ∈ (Eavg).graph) hout).mp he

def formAction : VT →L[ℂ] VT :=
  triangularAction TD (action ε hε h N hN)
    (referenceOutputResolventLp ε hε h N hN hb)
    (-scaledOrbitExtra ε hε h N hN hh m g k)
    (graph_action ε hε h N hN hb hh m g k t)

theorem formAction_embedding (u : VT) :
    JT (formAction ε hε h N hN hb hh m g k t u)=action ε hε h N hN (JT u) :=
  triangularAction_embedding TD (action ε hε h N hN)
    (referenceOutputResolventLp ε hε h N hN hb)
    (-scaledOrbitExtra ε hε h N hN hh m g k)
    (graph_action ε hε h N hN hb hh m g k t) u

theorem formAction_output (u : VT) :
    AT (formAction ε hε h N hN hb hh m g k t u)=
      referenceOutputResolventLp ε hε h N hN hb (AT u)+
        (-scaledOrbitExtra ε hε h N hN hh m g k) (JT u) :=
  triangularAction_output TD (action ε hε h N hN)
    (referenceOutputResolventLp ε hε h N hN hb)
    (-scaledOrbitExtra ε hε h N hN hh m g k)
    (graph_action ε hε h N hN hb hh m g k t) u

theorem domain_action (f : Hilbert) (hf : f ∈ (Eavg).domain) :
    action ε hε h N hN f ∈ (Eavg).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (graph_action ε hε h N hN hb hh m g k t f _ ((Eavg).mem_graph ⟨f,hf⟩))

theorem domain_intersection_action (f : Hilbert) (hf : f ∈ (Eavg).domain) :
    action ε hε h N hN f ∈ (Kr).domain ∧ action ε hε h N hN f ∈ (Eavg).domain :=
  ⟨radial_domain ε hε h N hN f,domain_action ε hε h N hN hb hh m g k t f hf⟩

theorem residualLift_formAction (u : RV) :
    KFCausalClockFloorStaticPotentialHamiltonian.referenceLift ε hε h hh hw m g k t
      (formAction ε hε h N hN hb hh m g k 0 u)=
      KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m g k t
        (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift ε hε h hh hw m g k t u) := by
  let SD := KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k t
  apply KFCausalClosedGraphForm.embedding_injective SD
  exact (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding ε hε h hh hw m g k t
    (formAction ε hε h N hN hb hh m g k 0 u)).trans
    ((formAction_embedding ε hε h N hN hb hh m g k 0 u).trans
      ((congrArg (action ε hε h N hN)
        (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding ε hε h hh hw m g k t u).symm).trans
        (KFCausalClockFloorRadialResolventResidual.formAction_embedding ε hε h N hN hb hh m g k t
          (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift ε hε h hh hw m g k t u)).symm))

theorem growingLift_formAction (u : RV) :
    KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k
      (formAction ε hε h N hN hb hh m g k 0 u)=
      KFCausalClockFloorRadialResolventGrowing.formAction ε hε h N hN hb hh m g k
        (KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k u) := by
  let GD := KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
  apply KFCausalClosedGraphForm.embedding_injective GD
  exact (KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding ε hε h hh hw m g k
    (formAction ε hε h N hN hb hh m g k 0 u)).trans
    ((formAction_embedding ε hε h N hN hb hh m g k 0 u).trans
      ((congrArg (action ε hε h N hN)
        (KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding ε hε h hh hw m g k u).symm).trans
        (KFCausalClockFloorRadialResolventGrowing.formAction_embedding ε hε h N hN hb hh m g k
          (KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k u)).symm))

theorem form_sequence_tendsto (u : VT) :
    Tendsto (fun n : ℕ =>
      formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k t u) atTop (𝓝 u) := by
  have hg := graph_sequence_tendsto ε hε h hb hh m g k (JT u) (AT u)
  apply tendsto_subtype_rng.mpr
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert EnergyOutputSpace).symm.continuous.tendsto
    (WithLp.ofLp u.val)).comp hg

theorem energy_sequence_tendsto (u : VT) :
    Tendsto (fun n : ℕ =>
      ‖AT (formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k t u)‖^2)
      atTop (𝓝 (‖AT u‖^2)) :=
  (((AT).continuous.tendsto u).comp
    (form_sequence_tendsto ε hε h hb hh m g k t u)).norm.pow 2

#print axioms averaged_time_stability
#print axioms yosida_graph
#print axioms graph_action
#print axioms formAction_embedding
#print axioms formAction_output
#print axioms domain_action
#print axioms domain_intersection_action
#print axioms residualLift_formAction
#print axioms growingLift_formAction
#print axioms form_sequence_tendsto
#print axioms energy_sequence_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventAveragedForm
