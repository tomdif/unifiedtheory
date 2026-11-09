/- The completed residual form (static plus time-weighted potential rows)
projects continuously into both the completed static form and the completed
potential form, and its sesquilinear energy is the exact sum of the static
form energy and the time-weighted potential form energy. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticPotentialHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorStaticHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorPotentialHamiltonian

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorResidualFormSplit
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalFiniteOutputRescaling (selected_apply)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp growingOutputLp)
open KFCausalPhysicalEnergyTransport (staticOutput growingOutput timeOutput timeOutput_apply)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalClockFloorChartPhasePairing (orderedOutput orderedOutputLp)
open KFCausalClockFloorStaticPotentialOutputClosure (retained selectedOutput selectedOutputLp sourceMap)
open KFCausalUnitIntervalOrbit (angleMeasure)

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

private theorem projection_closure {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (S : Submodule ℂ (X × Y)) (T : Submodule ℂ (X × Z))
    (L : Y →L[ℂ] Z) (hT : IsClosed (T : Set (X × Z)))
    (hS : ∀ z ∈ S, (z.1,L z.2) ∈ T) (z : X × Y) (hz : z ∈ S.topologicalClosure) :
    (z.1,L z.2) ∈ T := by
  let F : X × Y →L[ℂ] X × Z := (ContinuousLinearMap.id ℂ X).prodMap L
  have hs : S ≤ T.comap F.toLinearMap := hS
  exact S.topologicalClosure_minimal hs (hT.preimage F.continuous) hz

private theorem exp_smul_inner_cancel {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (t : ℝ) (x y : K) :
    (Real.exp (2*t):ℂ)*inner ℂ ((Real.exp (-t):ℂ) • x) ((Real.exp (-t):ℂ) • y)=
      inner ℂ x y := by
  rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal,← mul_assoc,← mul_assoc,
    ← Complex.ofReal_mul,← Complex.ofReal_mul,← Real.exp_add,← Real.exp_add,
    show 2*t+(-t)+(-t)=(0:ℝ) by ring,Real.exp_zero,Complex.ofReal_one,one_mul]

private theorem norm_sq_of_inner_split {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (x y z : K) (c : ℝ)
    (h : inner ℂ x x=inner ℂ y y+(c:ℂ)*inner ℂ z z) :
    ‖x‖^2=‖y‖^2+c*‖z‖^2 := by
  have hi := congrArg Complex.re h
  rw [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hi
  exact ((inner_self_eq_norm_sq (𝕜 := ℂ) x).symm.trans hi).trans
    (congrArg₂ (·+·) (inner_self_eq_norm_sq (𝕜 := ℂ) y)
      (congrArg (c*·) (inner_self_eq_norm_sq (𝕜 := ℂ) z)))

private theorem point_static_selected (z : Output (Fin 8) Hilbert) :
    staticOutput (selectedOutput z)=staticOutput z := by
  apply PiLp.ext
  intro i
  by_cases h3 : i.val < 3
  · have hr : retained i := Or.inl h3
    simp only [staticOutput,selectedOutput,selected_apply,h3,hr,if_true]
  · simp only [staticOutput,selected_apply,h3,if_false]

private theorem point_static_time (t : ℝ) (z : Output (Fin 8) Hilbert) :
    staticOutput (timeOutput 0 t z)=staticOutput z := by
  apply PiLp.ext
  intro i
  by_cases h3 : i.val < 3
  · simp only [staticOutput,selected_apply,timeOutput_apply,h3,if_true]
  · simp only [staticOutput,selected_apply,h3,if_false]

private theorem point_potential_source (t : ℝ) (z : Output (Fin 8) Hilbert) :
    (Real.exp (-t):ℂ) • orderedOutput (selectedOutput (timeOutput 0 t z))=
      orderedOutput (growingOutput z) := by
  have he : (Real.exp (-t):ℂ)*(Real.exp (t-0):ℂ)=1 := by
    rw [sub_zero,← Complex.ofReal_mul,← Real.exp_add,neg_add_cancel,Real.exp_zero,Complex.ofReal_one]
  apply PiLp.ext
  intro i
  by_cases h5 : i.val < 5
  · simp only [PiLp.smul_apply,orderedOutput,selected_apply,h5,not_true_eq_false,if_false,smul_zero]
  · have hr : retained i := Or.inr (by omega)
    have h3 : ¬ i.val < 3 := by omega
    simp only [PiLp.smul_apply,orderedOutput,selectedOutput,growingOutput,
      selected_apply,timeOutput_apply,h5,h3,hr,not_false_eq_true,if_true,if_false,smul_smul,he,one_smul]

private theorem point_selected_idem (z : Output (Fin 8) Hilbert) :
    selectedOutput (selectedOutput z)=selectedOutput z := by
  apply PiLp.ext
  intro i
  by_cases hr : retained i <;>
    simp only [selectedOutput,selected_apply,hr,if_true,if_false]

private theorem lp_selected_idem (z : EnergyOutputSpace) :
    selectedOutputLp (selectedOutputLp z)=selectedOutputLp z := by
  let w := selectedOutputLp z
  apply Lp.ext
  filter_upwards [selectedOutput.coeFn_compLp w,selectedOutput.coeFn_compLp z] with θ h1 h2
  change (selectedOutput.compLp w) θ=(selectedOutput.compLp z) θ
  rw [h1]
  change selectedOutput ((selectedOutput.compLp z) θ)=(selectedOutput.compLp z) θ
  rw [h2,point_selected_idem]

private theorem lp_static_selected (z : EnergyOutputSpace) :
    staticOutputLp (selectedOutputLp z)=staticOutputLp z := by
  let w := selectedOutputLp z
  apply Lp.ext
  filter_upwards [staticOutput.coeFn_compLp w,selectedOutput.coeFn_compLp z,
    staticOutput.coeFn_compLp z] with θ h1 h2 h3
  change (staticOutput.compLp w) θ=(staticOutput.compLp z) θ
  rw [h1,h3]
  change staticOutput ((selectedOutput.compLp z) θ)=staticOutput (z θ)
  rw [h2,point_static_selected]

private theorem lp_static_time (t : ℝ) (z : EnergyOutputSpace) :
    staticOutputLp (timeOutputLp 0 t z)=staticOutputLp z := by
  let w := timeOutputLp 0 t z
  apply Lp.ext
  filter_upwards [staticOutput.coeFn_compLp w,(timeOutput 0 t).coeFn_compLp z,
    staticOutput.coeFn_compLp z] with θ h1 h2 h3
  change (staticOutput.compLp w) θ=(staticOutput.compLp z) θ
  rw [h1,h3]
  change staticOutput (((timeOutput 0 t).compLp z) θ)=staticOutput (z θ)
  rw [h2,point_static_time]

private theorem lp_static_source (t : ℝ) (z : EnergyOutputSpace) :
    staticOutputLp (selectedOutputLp (timeOutputLp 0 t z))=staticOutputLp z :=
  (lp_static_selected (timeOutputLp 0 t z)).trans (lp_static_time t z)

private theorem lp_potential_source (t : ℝ) (z : EnergyOutputSpace) :
    (Real.exp (-t):ℂ) • orderedOutputLp (selectedOutputLp (timeOutputLp 0 t z))=
      orderedOutputLp (growingOutputLp z) := by
  let w1 := timeOutputLp 0 t z
  let w2 := selectedOutputLp w1
  let w3 := orderedOutputLp w2
  let g := growingOutputLp z
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (Real.exp (-t):ℂ) w3,orderedOutput.coeFn_compLp w2,
    selectedOutput.coeFn_compLp w1,(timeOutput 0 t).coeFn_compLp z,
    orderedOutput.coeFn_compLp g,growingOutput.coeFn_compLp z]
    with θ hs ho1 hsel ht ho2 hg
  change ((Real.exp (-t):ℂ) • w3) θ=(orderedOutput.compLp g) θ
  rw [hs,ho2]
  simp only [Pi.smul_apply]
  change (Real.exp (-t):ℂ) • (orderedOutput.compLp w2) θ=orderedOutput ((growingOutput.compLp z) θ)
  rw [ho1,hg]
  change (Real.exp (-t):ℂ) • orderedOutput ((selectedOutput.compLp w1) θ)=orderedOutput (growingOutput (z θ))
  rw [hsel]
  change (Real.exp (-t):ℂ) • orderedOutput (selectedOutput (((timeOutput 0 t).compLp z) θ))=
    orderedOutput (growingOutput (z θ))
  rw [ht,point_potential_source]

private theorem point_selected_inner (z w : Output (Fin 8) Hilbert) :
    inner ℂ (selectedOutput z) (selectedOutput w)=
      inner ℂ (staticOutput z) (staticOutput w)+
      inner ℂ (orderedOutput z) (orderedOutput w) := by
  rw [PiLp.inner_apply,PiLp.inner_apply,PiLp.inner_apply,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h3 : i.val < 3
  · have hr : retained i := Or.inl h3
    have h5 : i.val < 5 := by omega
    simp only [selectedOutput,staticOutput,orderedOutput,selected_apply,h3,h5,hr,
      not_true_eq_false,if_true,if_false,inner_zero_left,add_zero]
  · by_cases h5 : i.val < 5
    · have hr : ¬ retained i := by simp only [retained]; omega
      simp only [selectedOutput,staticOutput,orderedOutput,selected_apply,h3,h5,hr,
        not_true_eq_false,if_false,inner_zero_left,add_zero]
    · have hr : retained i := Or.inr (by omega)
      simp only [selectedOutput,staticOutput,orderedOutput,selected_apply,h3,h5,hr,
        not_false_eq_true,if_true,if_false,inner_zero_left,zero_add]

private theorem lp_selected_inner (z w : EnergyOutputSpace) :
    inner ℂ (selectedOutputLp z) (selectedOutputLp w)=
      inner ℂ (staticOutputLp z) (staticOutputLp w)+
      inner ℂ (orderedOutputLp z) (orderedOutputLp w) := by
  have he : (fun θ => inner ℂ (selectedOutputLp z θ) (selectedOutputLp w θ)) =ᵐ[angleMeasure]
      fun θ => inner ℂ (staticOutputLp z θ) (staticOutputLp w θ)+
        inner ℂ (orderedOutputLp z θ) (orderedOutputLp w θ) := by
    filter_upwards [selectedOutput.coeFn_compLp z,selectedOutput.coeFn_compLp w,
      staticOutput.coeFn_compLp z,staticOutput.coeFn_compLp w,
      orderedOutput.coeFn_compLp z,orderedOutput.coeFn_compLp w]
      with θ hz hw hsz hsw hoz how
    change inner ℂ (selectedOutput.compLp z θ) (selectedOutput.compLp w θ)=
      inner ℂ (staticOutput.compLp z θ) (staticOutput.compLp w θ)+
      inner ℂ (orderedOutput.compLp z θ) (orderedOutput.compLp w θ)
    rw [hz,hw,hsz,hsw,hoz,how,point_selected_inner]
  rw [L2.inner_def,integral_congr_ae he,
    integral_add (L2.integrable_inner (𝕜 := ℂ) (staticOutputLp z) (staticOutputLp w))
      (L2.integrable_inner (𝕜 := ℂ) (orderedOutputLp z) (orderedOutputLp w))]
  rfl

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
local notation "V" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hb m g k 0
local notation "J" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb m g k 0
local notation "A" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hb m g k 0
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hb m g k t
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hb m g k t
local notation "SJ" => KFCausalClosedGraphForm.embedding SD
local notation "SB" => KFCausalClosedGraphForm.energyOutput SD
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hb m g k 0
local notation "TV" => KFCausalClockFloorStaticHamiltonian.StaticForm ε hε h hh hb m g k 0
local notation "TJ" => KFCausalClosedGraphForm.embedding TD
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hb m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hb m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD

private theorem sourceMap_apply (u : V) :
    sourceMap ε hε h hh hb m g k t u=selectedOutputLp (timeOutputLp 0 t (A u)) :=
  (ContinuousLinearMap.comp_apply selectedOutputLp ((timeOutputLp 0 t).comp A) u).trans
    (congrArg selectedOutputLp (ContinuousLinearMap.comp_apply (timeOutputLp 0 t) A u))

theorem source_static (u : V) :
    staticOutputLp (sourceMap ε hε h hh hb m g k t u)=
      KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hb m g k u :=
  (congrArg staticOutputLp (sourceMap_apply ε hε h hh hb m g k t u)).trans
    ((lp_static_source t (A u)).trans
      (ContinuousLinearMap.comp_apply staticOutputLp A u).symm)

private theorem source_potential (u : V) :
    ((Real.exp (-t):ℂ) • orderedOutputLp) (sourceMap ε hε h hh hb m g k t u)=
      KFCausalClockFloorPotentialOutputClosure.potentialMap ε hε h hh hb m g k u :=
  (ContinuousLinearMap.smul_apply (Real.exp (-t):ℂ) orderedOutputLp
    (sourceMap ε hε h hh hb m g k t u)).trans
    ((congrArg (fun y : EnergyOutputSpace => (Real.exp (-t):ℂ) • orderedOutputLp y)
      (sourceMap_apply ε hε h hh hb m g k t u)).trans
      ((lp_potential_source t (A u)).trans
        ((congrArg orderedOutputLp
          (ContinuousLinearMap.comp_apply growingOutputLp A u).symm).trans
          (ContinuousLinearMap.comp_apply orderedOutputLp
            (KFCausalClockFloorAveragedRegularity.growingMap ε hε h hh hb m g k) u).symm)))

private theorem source_selected (u : V) :
    selectedOutputLp (sourceMap ε hε h hh hb m g k t u)=
      sourceMap ε hε h hh hb m g k t u :=
  (congrArg selectedOutputLp (sourceMap_apply ε hε h hh hb m g k t u)).trans
    ((lp_selected_idem (timeOutputLp 0 t (A u))).trans
      (sourceMap_apply ε hε h hh hb m g k t u).symm)

private theorem reference_static_graph (u : V) :
    (J u,KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hb m g k u) ∈
      (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hb m g k 0).graph := by
  let lift := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hb m g k 0
  have hl : Function.Surjective lift :=
    KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hb m g k 0
  let a := Classical.choose (hl u)
  have ha : lift a=u := Classical.choose_spec (hl u)
  have hj : J (lift a)=J u := congrArg J ha
  have hb' : KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hb m g k (lift a)=
      KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hb m g k u :=
    congrArg (KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hb m g k) ha
  have hj0 : KFCausalClockFloorAveragedEnergy.embedding ε hε h
      (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hb) hh m g k 0 a=J u :=
    (KFCausalClockFloorAveragedHamiltonian.graphFormVector_embedding ε hε h hh hb m g k 0 a).symm.trans hj
  have hb0 : KFCausalClockFloorStaticRootSource.staticOutput ε hε h hh hb m g k 0 a=
      KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hb m g k u :=
    (ContinuousLinearMap.comp_apply staticOutputLp
      (KFCausalClockFloorAveragedEnergy.energyOutput ε hε h
        (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hb) hh m g k 0) a).trans
      ((congrArg staticOutputLp
        (KFCausalClockFloorAveragedHamiltonian.graphFormVector_output ε hε h hh hb m g k 0 a)).symm.trans
        ((ContinuousLinearMap.comp_apply staticOutputLp A (lift a)).symm.trans hb'))
  rw [KFCausalClockFloorStaticOutputClosure.operator_graph]
  exact (KFCausalClockFloorStaticOutputClosure.initialGraph ε hε h hh hb m g k 0).le_topologicalClosure
    ⟨a,Prod.ext hj0 hb0⟩

theorem static_graph (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hb m g k t).graph) :
    (f,staticOutputLp z) ∈ (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hb m g k 0).graph := by
  have hs : ∀ p ∈ KFCausalClockFloorStaticPotentialOutputClosure.initialGraph ε hε h hh hb m g k t,
      (p.1,staticOutputLp p.2) ∈ (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hb m g k 0).graph := by
    rintro p ⟨u,rfl⟩
    exact (congrArg (fun y : EnergyOutputSpace =>
      (J u,y) ∈ (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hb m g k 0).graph)
      (source_static ε hε h hh hb m g k t u).symm).mp
        (reference_static_graph ε hε h hh hb m g k u)
  rw [KFCausalClockFloorStaticPotentialOutputClosure.operator_graph] at hz
  exact projection_closure
    (KFCausalClockFloorStaticPotentialOutputClosure.initialGraph ε hε h hh hb m g k t)
    (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hb m g k 0).graph
    staticOutputLp (KFCausalClockFloorStaticOutputClosure.operator_closed ε hε h hh hb m g k 0)
    hs (f,z) hz

theorem potential_graph (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hb m g k t).graph) :
    (f,((Real.exp (-t):ℂ) • orderedOutputLp) z) ∈
      (KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hb m g k).graph := by
  have hs : ∀ p ∈ KFCausalClockFloorStaticPotentialOutputClosure.initialGraph ε hε h hh hb m g k t,
      (p.1,((Real.exp (-t):ℂ) • orderedOutputLp) p.2) ∈
        (KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hb m g k).graph := by
    rintro p ⟨u,rfl⟩
    exact (congrArg (fun y : EnergyOutputSpace =>
      (J u,y) ∈ (KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hb m g k).graph)
      (source_potential ε hε h hh hb m g k t u).symm).mp
        (KFCausalClockFloorPotentialOutputClosure.reference_graph ε hε h hh hb m g k u)
  rw [KFCausalClockFloorStaticPotentialOutputClosure.operator_graph] at hz
  exact projection_closure
    (KFCausalClockFloorStaticPotentialOutputClosure.initialGraph ε hε h hh hb m g k t)
    (KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hb m g k).graph
    ((Real.exp (-t):ℂ) • orderedOutputLp)
    (KFCausalClockFloorPotentialOutputClosure.operator_closed ε hε h hh hb m g k)
    hs (f,z) hz

def staticLift (w : SV) : TV :=
  projectForm SD TD staticOutputLp (static_graph ε hε h hh hb m g k t) w

def potentialLift (w : SV) : PV :=
  projectForm SD PD ((Real.exp (-t):ℂ) • orderedOutputLp)
    (potential_graph ε hε h hh hb m g k t) w

theorem staticLift_embedding (w : SV) :
    TJ (staticLift ε hε h hh hb m g k t w)=SJ w :=
  projectForm_embedding SD TD staticOutputLp (static_graph ε hε h hh hb m g k t) w

theorem potentialLift_embedding (w : SV) :
    PJ (potentialLift ε hε h hh hb m g k t w)=SJ w :=
  projectForm_embedding SD PD ((Real.exp (-t):ℂ) • orderedOutputLp)
    (potential_graph ε hε h hh hb m g k t) w

private theorem staticLift_output (w : SV) :
    TB (staticLift ε hε h hh hb m g k t w)=staticOutputLp (SB w) :=
  projectForm_output SD TD staticOutputLp (static_graph ε hε h hh hb m g k t) w

private theorem potentialLift_output (w : SV) :
    PB (potentialLift ε hε h hh hb m g k t w)=(Real.exp (-t):ℂ) • orderedOutputLp (SB w) :=
  (projectForm_output SD PD ((Real.exp (-t):ℂ) • orderedOutputLp)
    (potential_graph ε hε h hh hb m g k t) w).trans
    (ContinuousLinearMap.smul_apply (Real.exp (-t):ℂ) orderedOutputLp (SB w))

private theorem selected_residual_output (w : SV) :
    selectedOutputLp (SB w)=SB w :=
  congrFun ((KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_dense ε hε h hh hb m g k t).equalizer
    (selectedOutputLp.continuous.comp (SB).continuous) (SB).continuous
    (funext (fun u => (congrArg selectedOutputLp
      (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_output ε hε h hh hb m g k t u)).trans
      ((source_selected ε hε h hh hb m g k t u).trans
        (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_output ε hε h hh hb m g k t u).symm)))) w

theorem residual_inner_split (w1 w2 : SV) :
    inner ℂ (SB w1) (SB w2)=
      inner ℂ (TB (staticLift ε hε h hh hb m g k t w1))
        (TB (staticLift ε hε h hh hb m g k t w2))+
      (Real.exp (2*t):ℂ)*inner ℂ (PB (potentialLift ε hε h hh hb m g k t w1))
        (PB (potentialLift ε hε h hh hb m g k t w2)) := by
  have h1 : inner ℂ (SB w1) (SB w2)=
      inner ℂ (selectedOutputLp (SB w1)) (selectedOutputLp (SB w2)) :=
    congrArg₂ (inner ℂ) (selected_residual_output ε hε h hh hb m g k t w1).symm
      (selected_residual_output ε hε h hh hb m g k t w2).symm
  have hs := h1.trans (lp_selected_inner (SB w1) (SB w2))
  have ht : inner ℂ (TB (staticLift ε hε h hh hb m g k t w1))
      (TB (staticLift ε hε h hh hb m g k t w2))=
      inner ℂ (staticOutputLp (SB w1)) (staticOutputLp (SB w2)) :=
    congrArg₂ (inner ℂ) (staticLift_output ε hε h hh hb m g k t w1)
      (staticLift_output ε hε h hh hb m g k t w2)
  have hp0 : inner ℂ (PB (potentialLift ε hε h hh hb m g k t w1))
      (PB (potentialLift ε hε h hh hb m g k t w2))=
      inner ℂ ((Real.exp (-t):ℂ) • orderedOutputLp (SB w1))
        ((Real.exp (-t):ℂ) • orderedOutputLp (SB w2)) :=
    congrArg₂ (inner ℂ) (potentialLift_output ε hε h hh hb m g k t w1)
      (potentialLift_output ε hε h hh hb m g k t w2)
  have h2 : (Real.exp (2*t):ℂ)*inner ℂ (PB (potentialLift ε hε h hh hb m g k t w1))
      (PB (potentialLift ε hε h hh hb m g k t w2))=
      inner ℂ (orderedOutputLp (SB w1)) (orderedOutputLp (SB w2)) :=
    (congrArg ((Real.exp (2*t):ℂ)*·) hp0).trans
      (exp_smul_inner_cancel t (orderedOutputLp (SB w1)) (orderedOutputLp (SB w2)))
  exact hs.trans (congrArg₂ (·+·) ht.symm h2.symm)

theorem residual_norm_split (w : SV) :
    ‖SB w‖^2=‖TB (staticLift ε hε h hh hb m g k t w)‖^2+
      Real.exp (2*t)*‖PB (potentialLift ε hε h hh hb m g k t w)‖^2 :=
  norm_sq_of_inner_split (SB w) (TB (staticLift ε hε h hh hb m g k t w))
    (PB (potentialLift ε hε h hh hb m g k t w)) (Real.exp (2*t))
    (residual_inner_split ε hε h hh hb m g k t w w)

#print axioms source_static
#print axioms static_graph
#print axioms potential_graph
#print axioms staticLift_embedding
#print axioms potentialLift_embedding
#print axioms residual_inner_split
#print axioms residual_norm_split
end
end UnifiedTheory.Audit.KFCausalClockFloorResidualFormSplit
