/- Unconditional Residual Form Reconstruction for all real couplings and
times: every regularized residual-form vector lifts to the completed
reference form, the range of the reference-to-residual form projection is the
intersection with the maximal radial square-root domain, and the completed
full-energy domain at time t equals both Dom(Kr^{1/2}) ∩ Dom Tres(t) and
Dom Tgrow ∩ Dom Tres(t). -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingFormReconstruction
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventResidual

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorResidualFormReconstruction
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalFiniteOutputRescaling (selected_apply)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalPhysicalEnergyTransport (timeOutput timeOutput_apply)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)
open KFCausalClockFloorStaticPotentialOutputClosure (retained selectedOutput selectedOutputLp sourceMap)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer (action radial_domain sequence_tendsto)
open KFCausalClockFloorRadialResolventRoot (rootAction root_graph rootAction_sequence_tendsto)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOperator rootOutput
  rootOutput_graph rootOutput_inner)
open KFCausalUnitIntervalOrbit (angleMeasure)

private theorem closed_isometric_range {V X Y Z : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (J : V →ₗ[ℂ] X) (R : V →ₗ[ℂ] Y) (P : V →ₗ[ℂ] Z)
    (hnorm : ∀ u : V, ‖u‖^2=‖J u‖^2+(‖R u‖^2+‖P u‖^2)) :
    IsClosed {q : X × Y × Z | ∃ u : V, (J u,R u,P u)=q} := by
  let W := WithLp 2 (X × WithLp 2 (Y × Z))
  let e1 := WithLp.prodContinuousLinearEquiv 2 ℂ X (WithLp 2 (Y × Z))
  let e2 := WithLp.prodContinuousLinearEquiv 2 ℂ Y Z
  let Φlin : V →ₗ[ℂ] W :=
    e1.symm.toLinearMap.comp (J.prod (e2.symm.toLinearMap.comp (R.prod P)))
  have hΦ : ∀ u : V, ‖Φlin u‖=‖u‖ := by
    intro u
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hnorm u,WithLp.prod_norm_sq_eq_of_L2 (Φlin u)]
    exact congrArg (fun s : ℝ => ‖J u‖^2+s)
      (WithLp.prod_norm_sq_eq_of_L2 ((Φlin u).ofLp.2))
  let Φ : V →ₗᵢ[ℂ] W := ⟨Φlin,hΦ⟩
  let ψ : X × Y × Z → W := fun q => e1.symm (q.1,e2.symm q.2)
  have hψ : Continuous ψ :=
    e1.symm.continuous.comp (continuous_fst.prodMk (e2.symm.continuous.comp continuous_snd))
  have hset : {q : X × Y × Z | ∃ u : V, (J u,R u,P u)=q}=ψ ⁻¹' (Set.range Φ) := by
    ext ⟨x,y,z⟩
    constructor
    · rintro ⟨u,hu⟩
      refine ⟨u,?_⟩
      have hx : J u=x := congrArg (Prod.fst : X × Y × Z → X) hu
      have hy : R u=y := congrArg (fun p : X × Y × Z => p.2.1) hu
      have hz : P u=z := congrArg (fun p : X × Y × Z => p.2.2) hu
      change e1.symm (J u,e2.symm (R u,P u))=e1.symm (x,e2.symm (y,z))
      rw [hx,hy,hz]
    · rintro ⟨u,hu⟩
      have h1 := e1.symm.injective hu
      have h2 := e2.symm.injective (congrArg (Prod.snd : X × WithLp 2 (Y × Z) → WithLp 2 (Y × Z)) h1)
      exact ⟨u,Prod.ext (congrArg (Prod.fst : X × WithLp 2 (Y × Z) → X) h1) h2⟩
  rw [hset]
  exact Φ.isometry.isUniformInducing.isComplete_range.isClosed.preimage hψ

private theorem norm_sq_of_inner_sum {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (x z : X) (y : Y)
    (h : inner ℂ x x=inner ℂ y y+inner ℂ z z) :
    ‖x‖^2=‖y‖^2+‖z‖^2 := by
  have hi := congrArg Complex.re h
  rw [Complex.add_re] at hi
  exact ((inner_self_eq_norm_sq (𝕜 := ℂ) x).symm.trans hi).trans
    (congrArg₂ (·+·) (inner_self_eq_norm_sq (𝕜 := ℂ) y) (inner_self_eq_norm_sq (𝕜 := ℂ) z))

private theorem point_omitted_split (z w : Output (Fin 8) Hilbert) :
    inner ℂ z w=(inner ℂ (z 3) (w 3)+inner ℂ (z 4) (w 4))+
      inner ℂ (selectedOutput z) (selectedOutput w) := by
  simp only [PiLp.inner_apply,Fin.sum_univ_succ,selectedOutput,
    selected_apply,retained,Fin.val_zero,Fin.val_succ]
  norm_num only [Nat.reduceLT,or_true,true_or,or_false,false_or,
    if_true,if_false,inner_zero_left,Finset.sum_empty,add_zero]
  change inner ℂ (z 0) (w 0)+(inner ℂ (z 1) (w 1)+(inner ℂ (z 2) (w 2)+
    (inner ℂ (z 3) (w 3)+(inner ℂ (z 4) (w 4)+(inner ℂ (z 5) (w 5)+
    (inner ℂ (z 6) (w 6)+inner ℂ (z 7) (w 7)))))))=
    (inner ℂ (z 3) (w 3)+inner ℂ (z 4) (w 4))+
    (inner ℂ (z 0) (w 0)+(inner ℂ (z 1) (w 1)+(inner ℂ (z 2) (w 2)+
    (0+(0+(inner ℂ (z 5) (w 5)+(inner ℂ (z 6) (w 6)+inner ℂ (z 7) (w 7))))))))
  abel

private theorem lp_omitted_split (z w : EnergyOutputSpace) :
    inner ℂ z w=(inner ℂ (coordinateLp 3 z) (coordinateLp 3 w)+
        inner ℂ (coordinateLp 4 z) (coordinateLp 4 w))+
      inner ℂ (selectedOutputLp z) (selectedOutputLp w) := by
  have he : (fun θ => inner ℂ (z θ) (w θ)) =ᵐ[angleMeasure]
      fun θ => (inner ℂ (coordinateLp 3 z θ) (coordinateLp 3 w θ)+
          inner ℂ (coordinateLp 4 z θ) (coordinateLp 4 w θ))+
        inner ℂ (selectedOutputLp z θ) (selectedOutputLp w θ) := by
    filter_upwards [(coordinate 3).coeFn_compLp z,(coordinate 3).coeFn_compLp w,
      (coordinate 4).coeFn_compLp z,(coordinate 4).coeFn_compLp w,
      selectedOutput.coeFn_compLp z,selectedOutput.coeFn_compLp w]
      with θ h3z h3w h4z h4w hsz hsw
    change inner ℂ (z θ) (w θ)=
      (inner ℂ ((coordinate 3).compLp z θ) ((coordinate 3).compLp w θ)+
        inner ℂ ((coordinate 4).compLp z θ) ((coordinate 4).compLp w θ))+
      inner ℂ (selectedOutput.compLp z θ) (selectedOutput.compLp w θ)
    rw [h3z,h3w,h4z,h4w,hsz,hsw]
    exact point_omitted_split (z θ) (w θ)
  have h3 := L2.integrable_inner (𝕜 := ℂ) (coordinateLp 3 z) (coordinateLp 3 w)
  have h4 := L2.integrable_inner (𝕜 := ℂ) (coordinateLp 4 z) (coordinateLp 4 w)
  have h34 : Integrable (fun θ =>
      inner ℂ (coordinateLp 3 z θ) (coordinateLp 3 w θ)+
        inner ℂ (coordinateLp 4 z θ) (coordinateLp 4 w θ)) angleMeasure := h3.add h4
  have hs := L2.integrable_inner (𝕜 := ℂ) (selectedOutputLp z) (selectedOutputLp w)
  rw [L2.inner_def,integral_congr_ae he,integral_add h34 hs,integral_add h3 h4]
  rfl

private theorem point_selected_time (s t : ℝ) (z : Output (Fin 8) Hilbert) :
    selectedOutput (timeOutput s t z)=timeOutput s t (selectedOutput z) := by
  apply PiLp.ext
  intro i
  by_cases hr : retained i <;>
    simp [selectedOutput,selected_apply,timeOutput_apply,hr]

private theorem lp_selected_time (s t : ℝ) (z : EnergyOutputSpace) :
    selectedOutputLp (timeOutputLp s t z)=timeOutputLp s t (selectedOutputLp z) := by
  let w1 := timeOutputLp s t z
  let w2 := selectedOutputLp z
  apply Lp.ext
  filter_upwards [selectedOutput.coeFn_compLp w1,(timeOutput s t).coeFn_compLp z,
    (timeOutput s t).coeFn_compLp w2,selectedOutput.coeFn_compLp z] with θ h1 h2 h3 h4
  change selectedOutput.compLp w1 θ=(timeOutput s t).compLp w2 θ
  rw [h1,h3]
  change selectedOutput ((timeOutput s t).compLp z θ)=
    timeOutput s t (selectedOutput.compLp z θ)
  rw [h2,h4,point_selected_time]

private theorem point_time_inv (s t : ℝ) (z : Output (Fin 8) Hilbert) :
    timeOutput t s (timeOutput s t z)=z := by
  have he : Complex.exp ((s:ℂ)-(t:ℂ))*Complex.exp ((t:ℂ)-(s:ℂ))=1 := by
    rw [← Complex.exp_add,show (s:ℂ)-(t:ℂ)+((t:ℂ)-(s:ℂ))=0 by ring,Complex.exp_zero]
  apply PiLp.ext
  intro i
  by_cases h3 : i.val < 3
  · simp [timeOutput_apply,h3]
  · simp [timeOutput_apply,h3,smul_smul,he]

private theorem lp_time_inv (s t : ℝ) (z : EnergyOutputSpace) :
    timeOutputLp t s (timeOutputLp s t z)=z := by
  let w := timeOutputLp s t z
  apply Lp.ext
  filter_upwards [(timeOutput t s).coeFn_compLp w,
    (timeOutput s t).coeFn_compLp z] with θ h1 h2
  change (timeOutput t s).compLp w θ=z θ
  rw [h1]
  change timeOutput t s ((timeOutput s t).compLp z θ)=z θ
  rw [h2,point_time_inv]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k 0
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k 0
local notation "RA" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hw m g k 0
local notation "GL" => KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k
local notation "R" => rootOutput ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k t
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hw m g k t
local notation "SJ" => KFCausalClosedGraphForm.embedding SD
local notation "SB" => KFCausalClosedGraphForm.energyOutput SD
local notation "SR" => KFCausalClockFloorStaticPotentialHamiltonian.referenceLift ε hε h hh hw m g k t
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k t
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hw) hh m g k t
local notation "Kr" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h

def referenceRoot (u : RV) : Hilbert := R (GL u)

theorem referenceRoot_graph (u : RV) :
    (RJ u,referenceRoot ε hε h hh hb m g k u) ∈ (rootOperator ε hε h).graph :=
  rootOutput_graph ε hε h hh hw m g k (GL u)

def referenceRootLinear : RV →ₗ[ℂ] Hilbert where
  toFun := referenceRoot ε hε h hh hb m g k
  map_add' u v :=
    (rootOperator ε hε h).mem_graph_snd_inj'
      (referenceRoot_graph ε hε h hh hb m g k (u+v))
      ((rootOperator ε hε h).graph.add_mem
        (referenceRoot_graph ε hε h hh hb m g k u)
        (referenceRoot_graph ε hε h hh hb m g k v))
      ((RJ).map_add u v)
  map_smul' c u :=
    (rootOperator ε hε h).mem_graph_snd_inj'
      (referenceRoot_graph ε hε h hh hb m g k (c • u))
      ((rootOperator ε hε h).graph.smul_mem c
        (referenceRoot_graph ε hε h hh hb m g k u))
      ((RJ).map_smul c u)

theorem reference_output_norm_sq (u : RV) :
    ‖RA u‖^2=‖referenceRoot ε hε h hh hb m g k u‖^2+‖selectedOutputLp (RA u)‖^2 := by
  let GD := KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
  have hs := lp_omitted_split (RA u) (RA u)
  have hr := rootOutput_inner ε hε h hh hw m g k (GL u) (GL u)
  have hg : KFCausalClosedGraphForm.energyOutput GD (GL u)=
      KFCausalAveragedOutputRescaling.growingOutputLp (RA u) :=
    (KFCausalClockFloorGrowingHamiltonian.referenceLift_output ε hε h hh hw m g k u).trans
      (ContinuousLinearMap.comp_apply KFCausalAveragedOutputRescaling.growingOutputLp RA u)
  have hc3 : coordinateLp 3 (KFCausalClosedGraphForm.energyOutput GD (GL u))=
      coordinateLp 3 (RA u) :=
    (congrArg (coordinateLp 3) hg).trans
      ((KFCausalClockFloorOrbitFactorGraphs.coordinate_growing 3 (RA u)).trans
        (if_neg (by decide : ¬ (3:ℕ)<3)))
  have hc4 : coordinateLp 4 (KFCausalClosedGraphForm.energyOutput GD (GL u))=
      coordinateLp 4 (RA u) :=
    (congrArg (coordinateLp 4) hg).trans
      ((KFCausalClockFloorOrbitFactorGraphs.coordinate_growing 4 (RA u)).trans
        (if_neg (by decide : ¬ (4:ℕ)<3)))
  have hr' : inner ℂ (referenceRoot ε hε h hh hb m g k u) (referenceRoot ε hε h hh hb m g k u)=
      inner ℂ (coordinateLp 3 (RA u)) (coordinateLp 3 (RA u))+
        inner ℂ (coordinateLp 4 (RA u)) (coordinateLp 4 (RA u)) :=
    hr.trans (congrArg₂ (·+·) (congrArg₂ (inner ℂ) hc3 hc3) (congrArg₂ (inner ℂ) hc4 hc4))
  have he := hs.trans (congrArg (fun q : ℂ => q+inner ℂ (selectedOutputLp (RA u)) (selectedOutputLp (RA u))) hr'.symm)
  exact norm_sq_of_inner_sum (RA u) (selectedOutputLp (RA u)) (referenceRoot ε hε h hh hb m g k u) he

theorem reference_form_norm_sq (u : RV) :
    ‖u‖^2=‖RJ u‖^2+(‖referenceRoot ε hε h hh hb m g k u‖^2+‖selectedOutputLp (RA u)‖^2) :=
  (KFCausalClockFloorAveragedFormTransport.form_norm_identity ε hε h hh hw m g k 0 u).trans
    (congrArg (fun s : ℝ => ‖RJ u‖^2+s) (reference_output_norm_sq ε hε h hh hb m g k u))

private theorem reference_zero_triple_closed :
    IsClosed {q : Hilbert × Hilbert × EnergyOutputSpace |
      ∃ u : RV, (RJ u,referenceRoot ε hε h hh hb m g k u,selectedOutputLp (RA u))=q} :=
  closed_isometric_range (RJ).toLinearMap (referenceRootLinear ε hε h hh hb m g k)
    (selectedOutputLp.toLinearMap.comp (RA).toLinearMap) (reference_form_norm_sq ε hε h hh hb m g k)

private theorem sourceMap_eq_time_selected (u : RV) :
    sourceMap ε hε h hh hw m g k t u=timeOutputLp 0 t (selectedOutputLp (RA u)) :=
  ((ContinuousLinearMap.comp_apply selectedOutputLp ((timeOutputLp 0 t).comp RA) u).trans
    (congrArg selectedOutputLp (ContinuousLinearMap.comp_apply (timeOutputLp 0 t) RA u))).trans
    (lp_selected_time 0 t (RA u))

private theorem reference_triple_closed :
    IsClosed {q : Hilbert × Hilbert × EnergyOutputSpace |
      ∃ u : RV, (RJ u,referenceRoot ε hε h hh hb m g k u,sourceMap ε hε h hh hw m g k t u)=q} := by
  let S0 := {q : Hilbert × Hilbert × EnergyOutputSpace |
    ∃ u : RV, (RJ u,referenceRoot ε hε h hh hb m g k u,selectedOutputLp (RA u))=q}
  let ψ : Hilbert × Hilbert × EnergyOutputSpace → Hilbert × Hilbert × EnergyOutputSpace :=
    fun q => (q.1,q.2.1,timeOutputLp t 0 q.2.2)
  have hψ : Continuous ψ :=
    continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
      ((timeOutputLp t 0).continuous.comp (continuous_snd.comp continuous_snd)))
  have hset : {q : Hilbert × Hilbert × EnergyOutputSpace |
      ∃ u : RV, (RJ u,referenceRoot ε hε h hh hb m g k u,sourceMap ε hε h hh hw m g k t u)=q}=
      ψ ⁻¹' S0 := by
    ext ⟨x,r,z⟩
    constructor
    · rintro ⟨u,hu⟩
      have hx : RJ u=x := congrArg (Prod.fst : Hilbert × Hilbert × EnergyOutputSpace → Hilbert) hu
      have hr : referenceRoot ε hε h hh hb m g k u=r :=
        congrArg (fun p : Hilbert × Hilbert × EnergyOutputSpace => p.2.1) hu
      have hz : sourceMap ε hε h hh hw m g k t u=z :=
        congrArg (fun p : Hilbert × Hilbert × EnergyOutputSpace => p.2.2) hu
      have hs : selectedOutputLp (RA u)=timeOutputLp t 0 z :=
        (lp_time_inv 0 t (selectedOutputLp (RA u))).symm.trans
          (congrArg (timeOutputLp t 0)
            ((sourceMap_eq_time_selected ε hε h hh hb m g k t u).symm.trans hz))
      exact ⟨u,Prod.ext hx (Prod.ext hr hs)⟩
    · rintro ⟨u,hu⟩
      have hx : RJ u=x := congrArg (Prod.fst : Hilbert × Hilbert × EnergyOutputSpace → Hilbert) hu
      have hr : referenceRoot ε hε h hh hb m g k u=r :=
        congrArg (fun p : Hilbert × Hilbert × EnergyOutputSpace => p.2.1) hu
      have hs : selectedOutputLp (RA u)=timeOutputLp t 0 z :=
        congrArg (fun p : Hilbert × Hilbert × EnergyOutputSpace => p.2.2) hu
      have hz : sourceMap ε hε h hh hw m g k t u=z :=
        (sourceMap_eq_time_selected ε hε h hh hb m g k t u).trans
          ((congrArg (timeOutputLp 0 t) hs).trans (lp_time_inv t 0 z))
      exact ⟨u,Prod.ext hx (Prod.ext hr hz)⟩
  rw [hset]
  exact (reference_zero_triple_closed ε hε h hh hb m g k).preimage hψ

private theorem reference_regularized_in_triple (N : ℝ) (hN : 0 < N) (v : RV) :
    let sv := SR v
    (action ε hε h N hN (SJ sv),rootAction ε hε h N hN (SJ sv),
      SB (KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m g k t sv)) ∈
      {q : Hilbert × Hilbert × EnergyOutputSpace |
        ∃ u : RV, (RJ u,referenceRoot ε hε h hh hb m g k u,sourceMap ε hε h hh hw m g k t u)=q} := by
  let sv := SR v
  have href := KFCausalClockFloorRadialYosidaGrowing.reference_stability
    ε hε h N hN hb hh m g k v
  let vM : RV := Classical.choose href
  have hvM : RJ vM=KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (RJ v) :=
    (Classical.choose_spec href).1
  let u : RV := v-(N⁻¹:ℂ) • vM
  refine ⟨u,?_⟩
  have h1 : RJ u=RJ v-(N⁻¹:ℂ) • RJ vM :=
    ((RJ).map_sub v ((N⁻¹:ℂ) • vM)).trans
      (congrArg (fun z : Hilbert => RJ v-z) ((RJ).map_smul (N⁻¹:ℂ) vM))
  have hJ0 : RJ u=action ε hε h N hN (RJ v) :=
    h1.trans (congrArg (fun z : Hilbert => RJ v-(N⁻¹:ℂ) • z) hvM)
  have hJ : RJ u=action ε hε h N hN (SJ sv) :=
    hJ0.trans (congrArg (action ε hε h N hN)
      (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding ε hε h hh hw m g k t v).symm)
  have hR : referenceRoot ε hε h hh hb m g k u=rootAction ε hε h N hN (SJ sv) :=
    (rootOperator ε hε h).mem_graph_snd_inj'
      (referenceRoot_graph ε hε h hh hb m g k u)
      (root_graph ε hε h N hN (SJ sv)) hJ
  have hL : SR u=
      KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m g k t sv := by
    apply KFCausalClosedGraphForm.embedding_injective SD
    exact (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding ε hε h hh hw m g k t u).trans
      (hJ.trans (KFCausalClockFloorRadialResolventResidual.formAction_embedding
        ε hε h N hN hb hh m g k t sv).symm)
  have hB : sourceMap ε hε h hh hw m g k t u=
      SB (KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m g k t sv) :=
    (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_output ε hε h hh hw m g k t u).symm.trans
      (congrArg SB hL)
  exact Prod.ext hJ (Prod.ext hR hB)

theorem regularized_residual_in_reference (N : ℝ) (hN : 0 < N) (w : SV) :
    ∃ u : RV, RJ u=action ε hε h N hN (SJ w) ∧
      referenceRoot ε hε h hh hb m g k u=rootAction ε hε h N hN (SJ w) ∧
      SR u=KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m g k t w := by
  let S := {q : Hilbert × Hilbert × EnergyOutputSpace |
    ∃ u : RV, (RJ u,referenceRoot ε hε h hh hb m g k u,sourceMap ε hε h hh hw m g k t u)=q}
  let Ψ : SV → Hilbert × Hilbert × EnergyOutputSpace := fun z =>
    (action ε hε h N hN (SJ z),rootAction ε hε h N hN (SJ z),
      SB (KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m g k t z))
  have hΨ : Continuous Ψ :=
    ((action ε hε h N hN).continuous.comp (SJ).continuous).prodMk
      (((rootAction ε hε h N hN).continuous.comp (SJ).continuous).prodMk
        ((SB).continuous.comp
          (KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m g k t).continuous))
  have hclosed : IsClosed (Ψ ⁻¹' S) := (reference_triple_closed ε hε h hh hb m g k t).preimage hΨ
  have hmem : w ∈ Ψ ⁻¹' S := by
    apply closure_minimal
      (s := Set.range (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift ε hε h hh hw m g k t))
      ?_ hclosed ((KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_dense ε hε h hh hw m g k t) w)
    rintro _ ⟨v,rfl⟩
    exact reference_regularized_in_triple ε hε h hh hb m g k t N hN v
  obtain ⟨u,hu⟩ := hmem
  have hJ : RJ u=action ε hε h N hN (SJ w) :=
    congrArg (Prod.fst : Hilbert × Hilbert × EnergyOutputSpace → Hilbert) hu
  have hR : referenceRoot ε hε h hh hb m g k u=rootAction ε hε h N hN (SJ w) :=
    congrArg (fun p : Hilbert × Hilbert × EnergyOutputSpace => p.2.1) hu
  have hJ' : SJ (SR u)=
      SJ (KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m g k t w) :=
    (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding ε hε h hh hw m g k t u).trans
      (hJ.trans (KFCausalClockFloorRadialResolventResidual.formAction_embedding
        ε hε h N hN hb hh m g k t w).symm)
  exact ⟨u,hJ,hR,KFCausalClosedGraphForm.embedding_injective SD hJ'⟩

private theorem reference_in_averaged_domain (u : RV) :
    RJ u ∈ (Eavg).domain := by
  let ut := KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hw m g k 0 t u
  have hdom : KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k t ut ∈ (Eavg).domain :=
    LinearPMap.mem_domain_of_mem_graph ut.property
  exact (congrArg (fun x : Hilbert => x ∈ (Eavg).domain)
    (KFCausalClockFloorAveragedFormTransport.transfer_embedding ε hε h hh hw m g k 0 t u)).mp hdom

theorem residual_domain_regularized_in_averaged (N : ℝ) (hN : 0 < N)
    (f : Hilbert) (hf : f ∈ (Tres).domain) :
    action ε hε h N hN f ∈ (Kr).domain ∧ action ε hε h N hN f ∈ (Eavg).domain := by
  let w := KFCausalClosedGraphForm.graphVector SD ⟨f,hf⟩
  obtain ⟨u,hJ,_,_⟩ := regularized_residual_in_reference ε hε h hh hb m g k t N hN w
  have hJf : RJ u=action ε hε h N hN f :=
    hJ.trans (congrArg (action ε hε h N hN)
      (KFCausalClosedGraphForm.graphVector_embedding SD ⟨f,hf⟩))
  refine ⟨radial_domain ε hε h N hN f,?_⟩
  exact (congrArg (fun x : Hilbert => x ∈ (Eavg).domain) hJf).mp
    (reference_in_averaged_domain ε hε h hh hb m g k t u)

theorem reconstruct_reference_form (w : SV) (r : Hilbert)
    (hr : (SJ w,r) ∈ (rootOperator ε hε h).graph) :
    ∃ u : RV, RJ u=SJ w ∧ referenceRoot ε hε h hh hb m g k u=r ∧ SR u=w := by
  let S := {q : Hilbert × Hilbert × EnergyOutputSpace |
    ∃ u : RV, (RJ u,referenceRoot ε hε h hh hb m g k u,sourceMap ε hε h hh hw m g k t u)=q}
  let seq : ℕ → Hilbert × Hilbert × EnergyOutputSpace := fun n =>
    (action ε hε h ((n:ℝ)+1) (by positivity) (SJ w),
      rootAction ε hε h ((n:ℝ)+1) (by positivity) (SJ w),
      SB (KFCausalClockFloorRadialResolventResidual.formAction
        ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k t w))
  have hmem : ∀ n : ℕ, seq n ∈ S := by
    intro n
    obtain ⟨u,hJ,hR,hL⟩ := regularized_residual_in_reference
      ε hε h hh hb m g k t ((n:ℝ)+1) (by positivity) w
    refine ⟨u,Prod.ext hJ (Prod.ext hR ?_)⟩
    exact (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_output
      ε hε h hh hw m g k t u).symm.trans (congrArg SB hL)
  have ht : Tendsto seq atTop (𝓝 (SJ w,r,SB w)) :=
    (sequence_tendsto ε hε h (SJ w)).prodMk_nhds
      ((rootAction_sequence_tendsto ε hε h (SJ w) r hr).prodMk_nhds
        (((SB).continuous.tendsto w).comp
          (KFCausalClockFloorRadialResolventResidual.form_sequence_tendsto ε hε h hb hh m g k t w)))
  obtain ⟨u,hu⟩ := (reference_triple_closed ε hε h hh hb m g k t).mem_of_tendsto ht
    (Eventually.of_forall hmem)
  have hJ : RJ u=SJ w :=
    congrArg (Prod.fst : Hilbert × Hilbert × EnergyOutputSpace → Hilbert) hu
  have hR : referenceRoot ε hε h hh hb m g k u=r :=
    congrArg (fun p : Hilbert × Hilbert × EnergyOutputSpace => p.2.1) hu
  have hJ' : SJ (SR u)=SJ w :=
    (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding ε hε h hh hw m g k t u).trans hJ
  exact ⟨u,hJ,hR,KFCausalClosedGraphForm.embedding_injective SD hJ'⟩

theorem referenceLift_range_eq :
    Set.range (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift ε hε h hh hw m g k t)=
      {w : SV | SJ w ∈ (rootOperator ε hε h).domain} := by
  ext w
  constructor
  · rintro ⟨u,hu⟩
    have hj : SJ w=RJ u :=
      (congrArg SJ hu.symm).trans
        (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding ε hε h hh hw m g k t u)
    exact (congrArg (fun x : Hilbert => x ∈ (rootOperator ε hε h).domain) hj.symm).mp
      (LinearPMap.mem_domain_of_mem_graph (referenceRoot_graph ε hε h hh hb m g k u))
  · intro hdom
    obtain ⟨u,_,_,hu⟩ := reconstruct_reference_form ε hε h hh hb m g k t w _
      ((rootOperator ε hε h).mem_graph ⟨SJ w,hdom⟩)
    exact ⟨u,hu⟩

theorem averaged_domain_eq_root_inter_residual (f : Hilbert) :
    f ∈ (Eavg).domain ↔ f ∈ (rootOperator ε hε h).domain ∧ f ∈ (Tres).domain := by
  constructor
  · intro hf
    let TD := KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hw m g k t
    let ut := KFCausalClosedGraphForm.graphVector TD ⟨f,hf⟩
    let u := KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hw m g k t 0 ut
    have hJu : RJ u=f :=
      (KFCausalClockFloorAveragedFormTransport.transfer_embedding ε hε h hh hw m g k t 0 ut).trans
        (KFCausalClosedGraphForm.graphVector_embedding TD ⟨f,hf⟩)
    have hr : f ∈ (rootOperator ε hε h).domain :=
      (congrArg (fun x : Hilbert => x ∈ (rootOperator ε hε h).domain) hJu).mp
        (LinearPMap.mem_domain_of_mem_graph (referenceRoot_graph ε hε h hh hb m g k u))
    have hs : f ∈ (Tres).domain :=
      (congrArg (fun x : Hilbert => x ∈ (Tres).domain) hJu).mp
        (LinearPMap.mem_domain_of_mem_graph
          (KFCausalClockFloorStaticPotentialOutputClosure.reference_graph ε hε h hh hw m g k t u))
    exact ⟨hr,hs⟩
  · rintro ⟨hr,hs⟩
    let w := KFCausalClosedGraphForm.graphVector SD ⟨f,hs⟩
    have hrg : (SJ w,rootOperator ε hε h ⟨f,hr⟩) ∈ (rootOperator ε hε h).graph :=
      (congrArg (fun x : Hilbert => (x,rootOperator ε hε h ⟨f,hr⟩) ∈ (rootOperator ε hε h).graph)
        (KFCausalClosedGraphForm.graphVector_embedding SD ⟨f,hs⟩).symm).mp
          ((rootOperator ε hε h).mem_graph ⟨f,hr⟩)
    obtain ⟨u,hJ,_,_⟩ := reconstruct_reference_form ε hε h hh hb m g k t w _ hrg
    have hJf : RJ u=f :=
      hJ.trans (KFCausalClosedGraphForm.graphVector_embedding SD ⟨f,hs⟩)
    exact (congrArg (fun x : Hilbert => x ∈ (Eavg).domain) hJf).mp
      (reference_in_averaged_domain ε hε h hh hb m g k t u)

theorem averaged_domain_eq_growing_inter_residual (f : Hilbert) :
    f ∈ (Eavg).domain ↔ f ∈ (Tgrow).domain ∧ f ∈ (Tres).domain := by
  rw [averaged_domain_eq_root_inter_residual ε hε h hh hb m g k t f,
    KFCausalClockFloorGrowingFormReconstruction.growing_domain_iff ε hε h hh hb m g k f]
  constructor
  · rintro ⟨hr,hs⟩
    have hp : f ∈ (Tpot).domain :=
      LinearPMap.mem_domain_of_mem_graph
        (KFCausalClockFloorResidualFormSplit.potential_graph ε hε h hh hw m g k t f _
          ((Tres).mem_graph ⟨f,hs⟩))
    exact ⟨⟨hr,hp⟩,hs⟩
  · rintro ⟨⟨hr,_⟩,hs⟩
    exact ⟨hr,hs⟩

#print axioms referenceRoot_graph
#print axioms reference_output_norm_sq
#print axioms reference_form_norm_sq
#print axioms regularized_residual_in_reference
#print axioms residual_domain_regularized_in_averaged
#print axioms reconstruct_reference_form
#print axioms referenceLift_range_eq
#print axioms averaged_domain_eq_root_inter_residual
#print axioms averaged_domain_eq_growing_inter_residual
end
end UnifiedTheory.Audit.KFCausalClockFloorResidualFormReconstruction
