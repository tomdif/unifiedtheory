/- The radial resolvent regularizer lifts to a bounded operator on the
completed residual form (static plus time-weighted potential rows) for all
real couplings and times, preserving the residual-output closure domain and
converging strongly to the identity in the completed residual-form norm. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventLeibniz
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventPotentialForm
import UnifiedTheory.Audit.KFCausalClockFloorResidualFormSplit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventResidual
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalFiniteOutputRescaling (selected_apply)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalPhysicalEnergyTransport (timeOutput timeOutput_apply)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalClockFloorChartPhasePairing (orderedOutput orderedOutputLp)
open KFCausalClockFloorStaticPotentialOutputClosure (retained selectedOutput selectedOutputLp sourceMap)
open KFCausalClockFloorRadialYosidaEnergy (factorOutput)
open KFCausalClockFloorRadialYosidaForm (outputAction)
open KFCausalClockFloorRadialYosidaOrderedTransport (shift_bound shifted_zero)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer (action radial_domain sequence_tendsto)
open KFCausalClockFloorRadialResolventSections (outputActionLp output_section_tendsto)
open KFCausalClockFloorRadialResolventLeibniz (orbitExtra scaledOrbitExtra
  scaledOrbitExtra_tendsto referenceOutputActionLp timeOutputLp_orbitExtra
  selectedOutputLp_orbitExtra reference_full_stability)
open KFCausalJointGraphBoundedCorrection (outputMap)
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

private theorem selected_time_linear (t : ℝ)
    (L : EnergyOutputSpace →L[ℂ] EnergyOutputSpace)
    (a b c : EnergyOutputSpace) (s0 s1 : EnergyOutputSpace)
    (hs0 : s0=selectedOutputLp (timeOutputLp 0 t a))
    (hs1 : s1=selectedOutputLp (timeOutputLp 0 t b))
    (ha : a=L b+c)
    (hL1 : timeOutputLp 0 t (L b)=L (timeOutputLp 0 t b))
    (hL2 : selectedOutputLp (L (timeOutputLp 0 t b))=
      L (selectedOutputLp (timeOutputLp 0 t b)))
    (hc1 : timeOutputLp 0 t c=c)
    (hc2 : selectedOutputLp c=c) :
    s0=L s1+c := by
  rw [hs0,hs1,ha,map_add,map_add,hL1,hL2,hc1,hc2]

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi*ε/3) (hh : h ≠ 0) (m g k t : ℝ)

include hε in
theorem zero_shift_bound : |(0:ℝ)| ≤ Real.pi*ε/6 := by
  rw [abs_zero]
  positivity

def referenceOutputResolventLp : EnergyOutputSpace →L[ℂ] EnergyOutputSpace :=
  ContinuousLinearMap.id ℂ EnergyOutputSpace-
    (N⁻¹:ℂ) • referenceOutputActionLp ε hε h N hN hb

private theorem outputAction_apply (z : Output (Fin 8) Hilbert) (i : Fin 8) :
    outputAction ε hε h N hN hb z i=factorOutput ε hε h N hN hb i (z i) := rfl

private theorem selectedOutput_apply (z : Output (Fin 8) Hilbert) (i : Fin 8) :
    selectedOutput z i=if retained i then z i else 0 :=
  selected_apply retained z i

private theorem point_time_outputAction (z : Output (Fin 8) Hilbert) :
    timeOutput 0 t (outputAction ε hε h N hN hb z)=
      outputAction ε hε h N hN hb (timeOutput 0 t z) := by
  apply PiLp.ext
  intro i
  change (if i.val < 3 then (1:ℂ) else (Real.exp (t-0):ℂ)) •
      factorOutput ε hε h N hN hb i (z i)=
    factorOutput ε hε h N hN hb i
      ((if i.val < 3 then (1:ℂ) else (Real.exp (t-0):ℂ)) • z i)
  exact ((factorOutput ε hε h N hN hb i).map_smul _ (z i)).symm

private theorem point_selected_outputAction (z : Output (Fin 8) Hilbert) :
    selectedOutput (outputAction ε hε h N hN hb z)=
      outputAction ε hε h N hN hb (selectedOutput z) := by
  apply PiLp.ext
  intro i
  rw [selectedOutput_apply,outputAction_apply,outputAction_apply,selectedOutput_apply]
  by_cases hr : retained i
  · simp only [hr,if_true]
  · simp only [hr,if_false,map_zero]

theorem timeOutputLp_referenceOutputActionLp (z : EnergyOutputSpace) :
    timeOutputLp 0 t (referenceOutputActionLp ε hε h N hN hb z)=
      referenceOutputActionLp ε hε h N hN hb (timeOutputLp 0 t z) := by
  let w1 := referenceOutputActionLp ε hε h N hN hb z
  let w2 := timeOutputLp 0 t z
  apply Lp.ext
  filter_upwards [(timeOutput 0 t).coeFn_compLp w1,
    (outputAction ε hε h N hN hb).coeFn_compLp z,
    (outputAction ε hε h N hN hb).coeFn_compLp w2,
    (timeOutput 0 t).coeFn_compLp z] with θ h1 h2 h3 h4
  change (timeOutput 0 t).compLp w1 θ=(outputAction ε hε h N hN hb).compLp w2 θ
  rw [h1,h3]
  change timeOutput 0 t ((outputAction ε hε h N hN hb).compLp z θ)=
    outputAction ε hε h N hN hb ((timeOutput 0 t).compLp z θ)
  rw [h2,h4,point_time_outputAction]

theorem selectedOutputLp_referenceOutputActionLp (z : EnergyOutputSpace) :
    selectedOutputLp (referenceOutputActionLp ε hε h N hN hb z)=
      referenceOutputActionLp ε hε h N hN hb (selectedOutputLp z) := by
  let w1 := referenceOutputActionLp ε hε h N hN hb z
  let w2 := selectedOutputLp z
  apply Lp.ext
  filter_upwards [selectedOutput.coeFn_compLp w1,
    (outputAction ε hε h N hN hb).coeFn_compLp z,
    (outputAction ε hε h N hN hb).coeFn_compLp w2,
    selectedOutput.coeFn_compLp z] with θ h1 h2 h3 h4
  change selectedOutput.compLp w1 θ=(outputAction ε hε h N hN hb).compLp w2 θ
  rw [h1,h3]
  change selectedOutput ((outputAction ε hε h N hN hb).compLp z θ)=
    outputAction ε hε h N hN hb (selectedOutput.compLp z θ)
  rw [h2,h4,point_selected_outputAction]

private theorem point_resolvent_split (z : Output (Fin 8) Hilbert) :
    z-(N⁻¹:ℂ) • outputAction ε hε h N hN hb z=
      KFCausalClockFloorRadialResolventSections.outputAction
        ε hε h N hN 0 (zero_shift_bound ε hε) (z-orderedOutput z)+
      KFCausalClockFloorRadialResolventSections.outputAction
        ε hε h N hN (-h/2) (shift_bound ε h hb) (orderedOutput z) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [outputAction,KFCausalClockFloorRadialResolventSections.outputAction,
      outputMap,factorOutput,orderedOutput,selected_apply,shifted_zero,
      KFCausalClockFloorRadialResolventShifted.shifted]

theorem referenceOutputResolventLp_split (z : EnergyOutputSpace) :
    referenceOutputResolventLp ε hε h N hN hb z=
      outputActionLp ε hε h N hN 0 (zero_shift_bound ε hε) (z-orderedOutputLp z)+
      outputActionLp ε hε h N hN (-h/2) (shift_bound ε h hb) (orderedOutputLp z) := by
  let wA := referenceOutputActionLp ε hε h N hN hb z
  let u1 := z-orderedOutputLp z
  let u2 := orderedOutputLp z
  let r1 := outputActionLp ε hε h N hN 0 (zero_shift_bound ε hε) u1
  let r2 := outputActionLp ε hε h N hN (-h/2) (shift_bound ε h hb) u2
  change z-(N⁻¹:ℂ) • wA=r1+r2
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub z ((N⁻¹:ℂ) • wA),Lp.coeFn_smul (N⁻¹:ℂ) wA,
    (outputAction ε hε h N hN hb).coeFn_compLp z,
    Lp.coeFn_add r1 r2,
    (KFCausalClockFloorRadialResolventSections.outputAction
      ε hε h N hN 0 (zero_shift_bound ε hε)).coeFn_compLp u1,
    Lp.coeFn_sub z u2,
    (KFCausalClockFloorRadialResolventSections.outputAction
      ε hε h N hN (-h/2) (shift_bound ε h hb)).coeFn_compLp u2,
    orderedOutput.coeFn_compLp z] with θ hsub hsmul hA hadd h1 hsub2 h2 ho
  change (z-(N⁻¹:ℂ) • wA) θ=(r1+r2) θ
  rw [hsub,hadd]
  simp only [Pi.sub_apply,Pi.add_apply]
  rw [hsmul]
  simp only [Pi.smul_apply]
  change z θ-(N⁻¹:ℂ) • (outputAction ε hε h N hN hb).compLp z θ=
    (KFCausalClockFloorRadialResolventSections.outputAction
      ε hε h N hN 0 (zero_shift_bound ε hε)).compLp u1 θ+
    (KFCausalClockFloorRadialResolventSections.outputAction
      ε hε h N hN (-h/2) (shift_bound ε h hb)).compLp u2 θ
  rw [hA,h1,h2]
  have hu1 : u1 θ=z θ-orderedOutput (z θ) := by
    rw [hsub2]
    simp only [Pi.sub_apply]
    exact congrArg (fun y => z θ-y) ho
  change z θ-(N⁻¹:ℂ) • outputAction ε hε h N hN hb (z θ)=
    KFCausalClockFloorRadialResolventSections.outputAction
      ε hε h N hN 0 (zero_shift_bound ε hε) (u1 θ)+
    KFCausalClockFloorRadialResolventSections.outputAction
      ε hε h N hN (-h/2) (shift_bound ε h hb) (orderedOutput.compLp z θ)
  rw [hu1,ho]
  exact point_resolvent_split ε hε h N hN hb (z θ)

theorem referenceOutputResolventLp_tendsto (z : EnergyOutputSpace) :
    Tendsto (fun n : ℕ =>
      referenceOutputResolventLp ε hε h ((n:ℝ)+1) (by positivity) hb z) atTop (𝓝 z) := by
  have h1 := output_section_tendsto ε hε h 0 (zero_shift_bound ε hε) (z-orderedOutputLp z)
  have h2 := output_section_tendsto ε hε h (-h/2) (shift_bound ε h hb) (orderedOutputLp z)
  have hsum : Tendsto (fun n : ℕ =>
      outputActionLp ε hε h ((n:ℝ)+1) (by positivity) 0 (zero_shift_bound ε hε) (z-orderedOutputLp z)+
      outputActionLp ε hε h ((n:ℝ)+1) (by positivity) (-h/2) (shift_bound ε h hb) (orderedOutputLp z))
      atTop (𝓝 z) := by
    simpa only [sub_add_cancel] using h1.add h2
  exact hsum.congr' (Eventually.of_forall (fun n =>
    (referenceOutputResolventLp_split ε hε h ((n:ℝ)+1) (by positivity) hb z).symm))

local notation "hw" => wide_bound ε hε h hb
local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN
local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k 0
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k 0
local notation "RA" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hw m g k 0
local notation "SB0" => sourceMap ε hε h hh hw m g k t
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k t
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k t
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hw m g k t
local notation "SJ" => KFCausalClosedGraphForm.embedding SD
local notation "SB" => KFCausalClosedGraphForm.energyOutput SD
local notation "Kr" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h

private theorem sourceMap_apply (u : RV) :
    SB0 u=selectedOutputLp (timeOutputLp 0 t (RA u)) :=
  (ContinuousLinearMap.comp_apply selectedOutputLp ((timeOutputLp 0 t).comp RA) u).trans
    (congrArg selectedOutputLp (ContinuousLinearMap.comp_apply (timeOutputLp 0 t) RA u))

theorem reference_residual_stability (u : RV) :
    ∃ v : RV, RJ v=M (RJ u) ∧
      SB0 v=referenceOutputActionLp ε hε h N hN hb (SB0 u)+
        orbitExtra ε hε h N hN hh m g k (RJ u) := by
  have hfull := reference_full_stability ε hε h N hN hb hh m g k u
  let v : RV := Classical.choose hfull
  have hv := Classical.choose_spec hfull
  refine ⟨v,hv.1,?_⟩
  exact selected_time_linear t (referenceOutputActionLp ε hε h N hN hb)
    (RA v) (RA u) (orbitExtra ε hε h N hN hh m g k (RJ u)) (SB0 v) (SB0 u)
    (sourceMap_apply ε hε h hb hh m g k t v)
    (sourceMap_apply ε hε h hb hh m g k t u)
    hv.2
    (timeOutputLp_referenceOutputActionLp ε hε h N hN hb t (RA u))
    (selectedOutputLp_referenceOutputActionLp ε hε h N hN hb (timeOutputLp 0 t (RA u)))
    (timeOutputLp_orbitExtra ε hε h N hN hh m g k t (RJ u))
    (selectedOutputLp_orbitExtra ε hε h N hN hh m g k (RJ u))

theorem yosida_graph (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (Tres).graph) :
    (M f,referenceOutputActionLp ε hε h N hN hb z+
      orbitExtra ε hε h N hN hh m g k f) ∈ (Tres).graph := by
  rw [KFCausalClockFloorStaticPotentialOutputClosure.operator_graph,
    KFCausalClockFloorStaticPotentialOutputClosure.initialGraph] at hz ⊢
  exact range_closure_transport_correction (RJ) (SB0) (M)
    (referenceOutputActionLp ε hε h N hN hb)
    (orbitExtra ε hε h N hN hh m g k)
    (reference_residual_stability ε hε h N hN hb hh m g k t) f z hz

theorem graph_action (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (Tres).graph) :
    (action ε hε h N hN f,
      referenceOutputResolventLp ε hε h N hN hb z+
        (-scaledOrbitExtra ε hε h N hN hh m g k) f) ∈ (Tres).graph := by
  have hm := yosida_graph ε hε h N hN hb hh m g k t f z hz
  have he := (Tres).graph.sub_mem hz ((Tres).graph.smul_mem (N⁻¹:ℂ) hm)
  change (action ε hε h N hN f,
    z-(N⁻¹:ℂ) • (referenceOutputActionLp ε hε h N hN hb z+
      orbitExtra ε hε h N hN hh m g k f)) ∈ (Tres).graph at he
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
    (action ε hε h N hN f,y) ∈ (Tres).graph) hout).mp he

def formAction : SV →L[ℂ] SV :=
  triangularAction SD (action ε hε h N hN)
    (referenceOutputResolventLp ε hε h N hN hb)
    (-scaledOrbitExtra ε hε h N hN hh m g k)
    (graph_action ε hε h N hN hb hh m g k t)

theorem formAction_embedding (w : SV) :
    SJ (formAction ε hε h N hN hb hh m g k t w)=action ε hε h N hN (SJ w) :=
  triangularAction_embedding SD (action ε hε h N hN)
    (referenceOutputResolventLp ε hε h N hN hb)
    (-scaledOrbitExtra ε hε h N hN hh m g k)
    (graph_action ε hε h N hN hb hh m g k t) w

theorem formAction_output (w : SV) :
    SB (formAction ε hε h N hN hb hh m g k t w)=
      referenceOutputResolventLp ε hε h N hN hb (SB w)+
        (-scaledOrbitExtra ε hε h N hN hh m g k) (SJ w) :=
  triangularAction_output SD (action ε hε h N hN)
    (referenceOutputResolventLp ε hε h N hN hb)
    (-scaledOrbitExtra ε hε h N hN hh m g k)
    (graph_action ε hε h N hN hb hh m g k t) w

theorem domain_action (f : Hilbert) (hf : f ∈ (Tres).domain) :
    action ε hε h N hN f ∈ (Tres).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (graph_action ε hε h N hN hb hh m g k t f _ ((Tres).mem_graph ⟨f,hf⟩))

theorem domain_intersection_action (f : Hilbert) (hf : f ∈ (Tres).domain) :
    action ε hε h N hN f ∈ (Kr).domain ∧ action ε hε h N hN f ∈ (Tres).domain :=
  ⟨radial_domain ε hε h N hN f,domain_action ε hε h N hN hb hh m g k t f hf⟩

theorem graph_sequence_tendsto (f : Hilbert) (z : EnergyOutputSpace) :
    Tendsto (fun n : ℕ =>
      (action ε hε h ((n:ℝ)+1) (by positivity) f,
        referenceOutputResolventLp ε hε h ((n:ℝ)+1) (by positivity) hb z+
          (-scaledOrbitExtra ε hε h ((n:ℝ)+1) (by positivity) hh m g k) f))
      atTop (𝓝 (f,z)) := by
  have h1 := sequence_tendsto ε hε h f
  have h2 := referenceOutputResolventLp_tendsto ε hε h hb z
  have h3 : Tendsto (fun n : ℕ =>
      (-scaledOrbitExtra ε hε h ((n:ℝ)+1) (by positivity) hh m g k) f) atTop (𝓝 0) := by
    simpa only [ContinuousLinearMap.neg_apply,neg_zero] using
      (scaledOrbitExtra_tendsto ε hε h hh m g k f).neg
  have h23 : Tendsto (fun n : ℕ =>
      referenceOutputResolventLp ε hε h ((n:ℝ)+1) (by positivity) hb z+
        (-scaledOrbitExtra ε hε h ((n:ℝ)+1) (by positivity) hh m g k) f) atTop (𝓝 z) := by
    simpa only [add_zero] using h2.add h3
  exact h1.prodMk_nhds h23

theorem form_sequence_tendsto (w : SV) :
    Tendsto (fun n : ℕ =>
      formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k t w) atTop (𝓝 w) := by
  have hg := graph_sequence_tendsto ε hε h hb hh m g k (SJ w) (SB w)
  apply tendsto_subtype_rng.mpr
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert EnergyOutputSpace).symm.continuous.tendsto
    (WithLp.ofLp w.val)).comp hg

theorem energy_sequence_tendsto (w : SV) :
    Tendsto (fun n : ℕ =>
      ‖SB (formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k t w)‖^2)
      atTop (𝓝 (‖SB w‖^2)) :=
  (((SB).continuous.tendsto w).comp
    (form_sequence_tendsto ε hε h hb hh m g k t w)).norm.pow 2

#print axioms zero_shift_bound
#print axioms timeOutputLp_referenceOutputActionLp
#print axioms selectedOutputLp_referenceOutputActionLp
#print axioms referenceOutputResolventLp_split
#print axioms referenceOutputResolventLp_tendsto
#print axioms reference_residual_stability
#print axioms yosida_graph
#print axioms graph_action
#print axioms formAction_embedding
#print axioms formAction_output
#print axioms domain_action
#print axioms domain_intersection_action
#print axioms graph_sequence_tendsto
#print axioms form_sequence_tendsto
#print axioms energy_sequence_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventResidual
