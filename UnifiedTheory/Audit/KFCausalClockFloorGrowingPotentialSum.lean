/- The actual growing Hamiltonian is the natural operator sum of its
maximal radial multiplier and the completed ORIGINAL potential Hamiltonian.
The difficult inclusion is derived by potential-form projection and dense
reference testing. Self-adjoint maximality supplies the reverse inclusion;
no separate-domain or joint-core equality is postulated. -/
import UnifiedTheory.Audit.KFCausalClockFloorPotentialHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingRadialPairing
import UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialCrossEstimate

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialSum
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorChartPhasePairing (orderedOutput orderedOutputLp)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOutput rootOutput_inner)
open KFCausalClockFloorGaussianGrowingRadialPairing (radialOutput root_form_pairing)
open KFCausalClockFloorPotentialHamiltonian
  (referenceLift referenceLift_dense growingLift)

private theorem coordinate_ordered (i : Fin 8) (y : EnergyOutputSpace) :
    coordinateLp i (orderedOutputLp y)=if i.val<5 then 0 else coordinateLp i y := by
  apply Lp.ext
  filter_upwards [(coordinate i).coeFn_compLp (orderedOutputLp y),
    orderedOutput.coeFn_compLp y,(coordinate i).coeFn_compLp y,
    Lp.coeFn_zero (E := Hilbert) (p := 2) (μ := angleMeasure)] with θ h1 h2 h3 h0
  change (coordinate i).compLp (orderedOutputLp y) θ=_
  rw [h1]
  change orderedOutput.compLp y θ i=_
  rw [h2]
  by_cases hi : i.val<5
  · simp only [orderedOutput,KFCausalFiniteOutputRescaling.selected_apply,hi,
      not_true_eq_false,if_false,if_true,h0,Pi.zero_apply]
  · simpa only [orderedOutput,KFCausalFiniteOutputRescaling.selected_apply,hi,
      not_false_eq_true,if_true,if_false] using h3.symm

private theorem inner_components (f g : EnergyOutputSpace) :
    inner ℂ f g=∑ i : Fin 8, inner ℂ (coordinateLp i f) (coordinateLp i g) := by
  have he : (fun θ => inner ℂ (f θ) (g θ)) =ᵐ[angleMeasure]
      fun θ => ∑ i : Fin 8, inner ℂ (coordinateLp i f θ) (coordinateLp i g θ) := by
    filter_upwards [ae_all_iff.mpr (fun i : Fin 8 => (coordinate i).coeFn_compLp f),
      ae_all_iff.mpr (fun i : Fin 8 => (coordinate i).coeFn_compLp g)] with θ hf hg
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg₂ (inner ℂ) (hf i).symm (hg i).symm
  rw [L2.inner_def,integral_congr_ae he,integral_finset_sum Finset.univ]
  · rfl
  · intro i _
    exact L2.integrable_inner (𝕜 := ℂ) (coordinateLp i f) (coordinateLp i g)

private theorem form_graph (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (u : KFCausalClosedGraphForm.FormSpace D) (y : Hilbert)
    (hp : ∀ v, inner ℂ (KFCausalClosedGraphForm.energyOutput D u)
      (KFCausalClosedGraphForm.energyOutput D v)=inner ℂ y (KFCausalClosedGraphForm.embedding D v)) :
    (KFCausalClosedGraphForm.embedding D u,y) ∈ (KFCausalClosedGraphForm.hamiltonian D).graph := by
  obtain ⟨hu,he⟩ := (KFCausalClosedGraphForm.hamiltonian_domain_characterization D u y).mpr hp
  have hg := (KFCausalClosedGraphForm.hamiltonian D).mem_graph
    ⟨KFCausalClosedGraphForm.embedding D u,hu⟩
  rwa [he] at hg

private theorem residual_pairing (A B C D E F : ℂ)
    (hs : A=B+C) (ha : A=D) (hb : B=E) (hf : F=D-E) : C=F := by
  rw [ha,hb] at hs
  rw [hf]
  exact eq_sub_of_add_eq (by simpa only [add_comm] using hs.symm)

private theorem sum_graph (K P : Hilbert →ₗ.[ℂ] Hilbert) (f r p : Hilbert)
    (hr : (f,r) ∈ K.graph) (hp : (f,p) ∈ P.graph) : (f,r+p) ∈ (K+P).graph := by
  have hk := LinearPMap.mem_domain_of_mem_graph hr
  have hp' := LinearPMap.mem_domain_of_mem_graph hp
  have heK : K ⟨f,hk⟩=r := K.mem_graph_snd_inj' (K.mem_graph ⟨f,hk⟩) hr rfl
  have heP : P ⟨f,hp'⟩=p := P.mem_graph_snd_inj' (P.mem_graph ⟨f,hp'⟩) hp rfl
  exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨f,⟨hk,hp'⟩⟩,rfl,by
    change K ⟨f,hk⟩+P ⟨f,hp'⟩=r+p
    rw [heK,heP]⟩

private theorem formal_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) : A.IsFormalAdjoint A := by
  have hf := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp hA] at hf

private theorem maximal_sum (A K P : Hilbert →ₗ.[ℂ] Hilbert)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K) (hP : IsSelfAdjoint P)
    (hle : A ≤ K+P) : A=K+P := by
  have hsum : (K+P).IsFormalAdjoint (K+P) := by
    intro x y
    change inner ℂ (K ⟨x,x.property.1⟩+P ⟨x,x.property.2⟩) (y:Hilbert)=
      inner ℂ (x:Hilbert) (K ⟨y,y.property.1⟩+P ⟨y,y.property.2⟩)
    rw [inner_add_left,inner_add_right]
    exact congrArg₂ (·+·)
      (formal_self K hK ⟨(x:Hilbert),x.property.1⟩ ⟨(y:Hilbert),y.property.1⟩)
      (formal_self P hP ⟨(x:Hilbert),x.property.2⟩ ⟨(y:Hilbert),y.property.2⟩)
  have hf : A.IsFormalAdjoint (K+P) := by
    intro x y
    have he : A x=(K+P) ⟨x,hle.1 x.property⟩ := hle.2 rfl
    rw [he]
    exact hsum ⟨x,hle.1 x.property⟩ y
  have hrev := hf.le_adjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hrev
  exact le_antisymm hle hrev

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "GV" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hw m g k
local notation "GJ" => KFCausalClosedGraphForm.embedding GD
local notation "GB" => KFCausalClosedGraphForm.energyOutput GD
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hw m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "R" => rootOutput ε hε h hh hw m g k

private theorem static_coordinate_zero (u : GV) (i : Fin 8) (hi : i.val<3) :
    coordinateLp i (GB u)=0 := by
  have hg := u.property
  change (GJ u,GB u) ∈ (KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k).graph at hg
  rw [KFCausalClockFloorGrowingOutputClosure.operator_graph] at hg
  have hc := KFCausalClockFloorGrowingOutputClosure.closure_component ε hε h hh hw m g k
    (GJ u,GB u) hg i
  exact (KFCausalClockFloorOrbitFactorGraphs.factorOperator ε hε h i).graph_fst_eq_zero_snd hc
    (by simp only [KFCausalClockFloorOrbitFactorGraphs.growingWeight,hi,if_true,zero_smul,map_zero])

private theorem form_split (u v : GV) :
    inner ℂ (GB u) (GB v)=inner ℂ (R u) (R v)+
      inner ℂ (orderedOutputLp (GB u)) (orderedOutputLp (GB v)) := by
  have h0 := static_coordinate_zero ε hε h hh hb m g k u 0 (by decide)
  have h1 := static_coordinate_zero ε hε h hh hb m g k u 1 (by decide)
  have h2 := static_coordinate_zero ε hε h hh hb m g k u 2 (by decide)
  have hr := rootOutput_inner ε hε h hh hw m g k u v
  have e1 := inner_components (GB u) (GB v)
  have e2 := inner_components (orderedOutputLp (GB u)) (orderedOutputLp (GB v))
  have hs : (∑ i : Fin 8, inner ℂ (coordinateLp i (GB u)) (coordinateLp i (GB v)))=
      (inner ℂ (coordinateLp 3 (GB u)) (coordinateLp 3 (GB v))+
        inner ℂ (coordinateLp 4 (GB u)) (coordinateLp 4 (GB v)))+
      (∑ i : Fin 8, inner ℂ (coordinateLp i (orderedOutputLp (GB u)))
        (coordinateLp i (orderedOutputLp (GB v)))) := by
    simp [Fin.sum_univ_succ,coordinate_ordered,h0,h1,h2]
    abel
  have he := e1.trans (hs.trans (congrArg (fun z : ℂ =>
    (inner ℂ (coordinateLp 3 (GB u)) (coordinateLp 3 (GB v))+
      inner ℂ (coordinateLp 4 (GB u)) (coordinateLp 4 (GB v)))+z) e2.symm))

  exact he.trans (congrArg (fun z : ℂ => z+
    inner ℂ (orderedOutputLp (GB u)) (orderedOutputLp (GB v))) hr.symm)

theorem potential_graph (x : (G).domain) :
    ((x:Hilbert),G x-radialOutput ε hε h hh hb m g k x) ∈ (P).graph := by
  let u := KFCausalClosedGraphForm.formLift GD x
  let v := growingLift ε hε h hh hw m g k u
  have hp : ∀ w : PV, inner ℂ (PB v) (PB w)=
      inner ℂ (G x-radialOutput ε hε h hh hb m g k x) (PJ w) := by
    intro w
    refine congrFun ((referenceLift_dense ε hε h hh hw m g k).equalizer
      (continuous_const.inner (𝕜 := ℂ) (PB).continuous)
      (continuous_const.inner (𝕜 := ℂ) (PJ).continuous) ?_) w
    funext z
    let gz := KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k z
    have hs := form_split ε hε h hh hb m g k u gz
    have hg := KFCausalClosedGraphForm.hamiltonian_represents_form GD x gz
    have hk := root_form_pairing ε hε h hh hb m g k x gz
    have hi : inner ℂ (G x-radialOutput ε hε h hh hb m g k x) (GJ gz)=
      inner ℂ (G x) (GJ gz)-inner ℂ (radialOutput ε hε h hh hb m g k x) (GJ gz) :=
      inner_sub_left _ _ _
    have hp0 := residual_pairing _ _ _ _ _ _ hs hg hk hi
    have hleft := KFCausalClockFloorPotentialHamiltonian.growingLift_output
      ε hε h hh hw m g k u
    have hright : PB (referenceLift ε hε h hh hw m g k z)=orderedOutputLp (GB gz) :=
      (KFCausalClockFloorPotentialHamiltonian.referenceLift_output ε hε h hh hw m g k z).trans
        (congrArg orderedOutputLp
          (KFCausalClockFloorGrowingHamiltonian.referenceLift_output ε hε h hh hw m g k z)).symm
    have hemb : PJ (referenceLift ε hε h hh hw m g k z)=GJ gz :=
      (KFCausalClockFloorPotentialHamiltonian.referenceLift_embedding ε hε h hh hw m g k z).trans
        (KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding ε hε h hh hw m g k z).symm
    exact ((congrArg₂ (inner ℂ) hleft hright).trans hp0).trans
      (congrArg (inner ℂ (G x-radialOutput ε hε h hh hb m g k x)) hemb).symm
  have hg := form_graph PD v (G x-radialOutput ε hε h hh hb m g k x) hp
  have he : PJ v=(x:Hilbert) :=
    (KFCausalClockFloorPotentialHamiltonian.growingLift_embedding ε hε h hh hw m g k u).trans
      (KFCausalClosedGraphForm.embedding_formLift GD x)
  exact (congrArg (fun f : Hilbert =>
    (f,G x-radialOutput ε hε h hh hb m g k x) ∈ (P).graph) he).mp hg

theorem potential_domain (x : (G).domain) : (x:Hilbert) ∈ (P).domain :=
  LinearPMap.mem_domain_of_mem_graph (potential_graph ε hε h hh hb m g k x)

theorem operator_sum : (G)=(K)+(P) := by
  apply maximal_sum _ _ _
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_selfAdjoint ε hε h hh hw m g k)
    (KFCausalClockFloorRadialYosidaDomain.operator_selfAdjoint ε hε h)
    (KFCausalClockFloorPotentialHamiltonian.hamiltonian_selfAdjoint ε hε h hh hw m g k)
  apply LinearPMap.le_graph_iff.mp
  rintro ⟨f,z⟩ hfz
  let x : (G).domain := ⟨f,LinearPMap.mem_domain_of_mem_graph hfz⟩
  have he : G x=z := (G).mem_graph_snd_inj' ((G).mem_graph x) hfz rfl
  have hk := (K).mem_graph ⟨(x:Hilbert),
    KFCausalClockFloorGrowingRadialDomination.radial_domain ε hε h hh hb m g k x⟩
  have hp := potential_graph ε hε h hh hb m g k x
  have hs := sum_graph (K) (P) (x:Hilbert) (radialOutput ε hε h hh hb m g k x)
    (G x-radialOutput ε hε h hh hb m g k x) hk hp
  have ha : radialOutput ε hε h hh hb m g k x+
      (G x-radialOutput ε hε h hh hb m g k x)=z := by rw [← he]; abel
  exact (congrArg (fun y : Hilbert => ((x:Hilbert),y) ∈ ((K)+(P)).graph) ha).mp hs

theorem domain_iff (x : Hilbert) :
    x ∈ (G).domain ↔ x ∈ (K).domain ∧ x ∈ (P).domain := by
  rw [operator_sum ε hε h hh hb m g k,LinearPMap.add_domain]
  rfl

theorem split_norm_square (x : (G).domain) :
    ‖radialOutput ε hε h hh hb m g k x‖^2+
      ‖P ⟨(x:Hilbert),potential_domain ε hε h hh hb m g k x⟩‖^2 ≤ ‖G x‖^2 := by
  have he : P ⟨(x:Hilbert),potential_domain ε hε h hh hb m g k x⟩=
      G x-radialOutput ε hε h hh hb m g k x :=
    (P).mem_graph_snd_inj' ((P).mem_graph _)
      (potential_graph ε hε h hh hb m g k x) rfl
  rw [he]
  exact KFCausalClockFloorGrowingRadialCrossEstimate.split_norm_square ε hε h hh hb m g k x

#print axioms potential_graph
#print axioms potential_domain
#print axioms operator_sum
#print axioms domain_iff
#print axioms split_norm_square
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialSum
