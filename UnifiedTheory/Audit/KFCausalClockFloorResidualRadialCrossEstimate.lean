/- Cross-estimates between the residual Hamiltonian S(t), the maximal static
operator T, the closed potential operator P, and the maximal radial kinetic
operator Kr. Any vector in Dom S(t) ∩ Dom Kr lies in Dom H(t) with
H(t) f = exp(2t) Kr f + S(t) f, yielding an unconditional lower bound on
Re ⟨S(t) f, Kr f⟩ and, at zero couplings where S(0) = T, on Re ⟨T f, Kr f⟩. -/
import UnifiedTheory.Audit.KFCausalClockFloorResidualFormReconstruction
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianRadialCrossEstimate
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaOutputAccretivity
import UnifiedTheory.Audit.KFCausalClockFloorResidualStaticPotentialDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorResidualRadialCrossEstimate
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorChartPhasePairing (orderedOutput orderedOutputLp)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOperator)

private theorem sum_graph {X : Type*} [AddCommGroup X] [Module ℂ X]
    (A B : X →ₗ.[ℂ] X) (f a b : X)
    (ha : (f,a) ∈ A.graph) (hb : (f,b) ∈ B.graph) : (f,a+b) ∈ (A+B).graph := by
  have hda := LinearPMap.mem_domain_of_mem_graph ha
  have hdb := LinearPMap.mem_domain_of_mem_graph hb
  have hea : A ⟨f,hda⟩=a := A.mem_graph_snd_inj' (A.mem_graph ⟨f,hda⟩) ha rfl
  have heb : B ⟨f,hdb⟩=b := B.mem_graph_snd_inj' (B.mem_graph ⟨f,hdb⟩) hb rfl
  exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨f,⟨hda,hdb⟩⟩,rfl,by
    change A ⟨f,hda⟩+B ⟨f,hdb⟩=a+b
    rw [hea,heb]⟩

private theorem smul_graph {X : Type*} [AddCommGroup X] [Module ℂ X]
    (c : ℂ) (A : X →ₗ.[ℂ] X) (f a : X)
    (ha : (f,a) ∈ A.graph) : (f,c • a) ∈ (c • A).graph := by
  have hd := LinearPMap.mem_domain_of_mem_graph ha
  have he : A ⟨f,hd⟩=a := A.mem_graph_snd_inj' (A.mem_graph ⟨f,hd⟩) ha rfl
  exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨f,hd⟩,rfl,by
    change c • A ⟨f,hd⟩=c • a
    rw [he]⟩

private theorem selfadjoint_eq_of_le {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] (A B : X →ₗ.[ℂ] X)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hle : A ≤ B) : A=B := by
  have hBB : B.IsFormalAdjoint B := by
    have hF := LinearPMap.adjoint_isFormalAdjoint hB.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hB] at hF
  have hAB : A.IsFormalAdjoint B := by
    intro f g
    have he : A f=B ⟨f,hle.1 f.property⟩ := hle.2 rfl
    rw [he]
    exact hBB ⟨f,hle.1 f.property⟩ g
  have hrev := hAB.le_adjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hrev
  exact le_antisymm hle hrev

private theorem form_graph (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (u : KFCausalClosedGraphForm.FormSpace D) (y : Hilbert)
    (hp : ∀ v, inner ℂ (KFCausalClosedGraphForm.energyOutput D u)
      (KFCausalClosedGraphForm.energyOutput D v)=inner ℂ y (KFCausalClosedGraphForm.embedding D v)) :
    (KFCausalClosedGraphForm.embedding D u,y) ∈ (KFCausalClosedGraphForm.hamiltonian D).graph := by
  obtain ⟨hu,he⟩ := (KFCausalClosedGraphForm.hamiltonian_domain_characterization D u y).mpr hp
  have hg := (KFCausalClosedGraphForm.hamiltonian D).mem_graph
    ⟨KFCausalClosedGraphForm.embedding D u,hu⟩
  rwa [he] at hg

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

private theorem zero_growingWeight_ge_five (i : Fin 8) (hi : ¬ i.val<5) :
    KFCausalClockFloorOrbitFactorGraphs.growingWeight 0 0 0 i=0 := by
  fin_cases i <;>
    simp [KFCausalClockFloorOrbitFactorGraphs.growingWeight,
      KFCausalPhysicalEnergyFactors.energyWeight] at hi ⊢

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k t
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k t
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hw) hh m g k t

theorem residual_radial_in_averaged_domain (f : Hilbert)
    (hs : f ∈ (S).domain) (hr : f ∈ (K).domain) :
    f ∈ (Eavg).domain := by
  have hH : f ∈ (H).domain :=
    (KFCausalClockFloorHamiltonianRadialSum.domain_iff ε hε h hh hb m g k t f).mpr ⟨hr,hs⟩
  let u := KFCausalClockFloorAveragedHamiltonianBridge.referenceLift ε hε h hh hw m g k t ⟨f,hH⟩
  have hJu : KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k 0 u=f :=
    KFCausalClockFloorAveragedHamiltonianBridge.embedding_referenceLift ε hε h hh hw m g k t ⟨f,hH⟩
  have hroot : f ∈ (rootOperator ε hε h).domain :=
    (congrArg (fun x : Hilbert => x ∈ (rootOperator ε hε h).domain) hJu).mp
      (LinearPMap.mem_domain_of_mem_graph
        (KFCausalClockFloorResidualFormReconstruction.referenceRoot_graph ε hε h hh hb m g k u))
  let w := KFCausalClosedGraphForm.formLift SD ⟨f,hs⟩
  have hres : f ∈ (Tres).domain :=
    (congrArg (fun x : Hilbert => x ∈ (Tres).domain)
      (KFCausalClosedGraphForm.embedding_formLift SD ⟨f,hs⟩)).mp
      (LinearPMap.mem_domain_of_mem_graph w.property)
  exact (KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_root_inter_residual
    ε hε h hh hb m g k t f).mpr ⟨hroot,hres⟩

theorem hamiltonian_graph_of_residual_radial (f s r : Hilbert)
    (hs : (f,s) ∈ (S).graph) (hr : (f,r) ∈ (K).graph) :
    (f,(Real.exp (2*t):ℂ) • r+s) ∈ (H).graph := by
  rw [KFCausalClockFloorHamiltonianRadialSum.operator_sum ε hε h hh hb m g k t]
  exact sum_graph ((Real.exp (2*t):ℂ) • (K)) (S) f ((Real.exp (2*t):ℂ) • r) s
    (smul_graph (Real.exp (2*t):ℂ) (K) f r hr) hs

theorem residual_radial_pairing (f s r : Hilbert)
    (hs : (f,s) ∈ (S).graph) (hr : (f,r) ∈ (K).graph) :
    -(h^2/ε^2)*‖f‖^2 ≤ (inner ℂ s r).re :=
  (KFCausalClockFloorHamiltonianRadialCrossEstimate.graph_residual_radial_pairing
    ε hε h hh hb m g k t f ((Real.exp (2*t):ℂ) • r+s) r s
    (hamiltonian_graph_of_residual_radial ε hε h hh hb m g k t f s r hs hr) hr hs).1

theorem residual_radial_sum_norm_sq (f s r : Hilbert)
    (hs : (f,s) ∈ (S).graph) (hr : (f,r) ∈ (K).graph) :
    Real.exp (4*t)*‖r‖^2+‖s‖^2 ≤
      ‖(Real.exp (2*t):ℂ) • r+s‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖f‖^2 :=
  (KFCausalClockFloorHamiltonianRadialCrossEstimate.graph_residual_radial_pairing
    ε hε h hh hb m g k t f ((Real.exp (2*t):ℂ) • r+s) r s
    (hamiltonian_graph_of_residual_radial ε hε h hh hb m g k t f s r hs hr) hr hs).2

theorem static_potential_radial_pairing (f y z r : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hp : (f,z) ∈ (P).graph)
    (hr : (f,r) ∈ (K).graph) (hf : f ∈ (Tres).domain) :
    -(h^2/ε^2)*‖f‖^2 ≤ (inner ℂ (y+(Real.exp (2*t):ℂ) • z) r).re := by
  let w := KFCausalClosedGraphForm.graphVector SD ⟨f,hf⟩
  have hw_emb : KFCausalClosedGraphForm.embedding SD w=f :=
    KFCausalClosedGraphForm.graphVector_embedding SD ⟨f,hf⟩
  have ht' : (KFCausalClosedGraphForm.embedding SD w,y) ∈ (T).graph :=
    (congrArg (fun x : Hilbert => (x,y) ∈ (T).graph) hw_emb.symm).mp ht
  have hp' : (KFCausalClosedGraphForm.embedding SD w,z) ∈ (P).graph :=
    (congrArg (fun x : Hilbert => (x,z) ∈ (P).graph) hw_emb.symm).mp hp
  have hs' := KFCausalClockFloorResidualStaticPotentialDecomposition.sum_graph
    ε hε h hh hw m g k t w y z ht' hp'
  have hs : (f,y+(Real.exp (2*t):ℂ) • z) ∈ (S).graph :=
    (congrArg (fun x : Hilbert => (x,y+(Real.exp (2*t):ℂ) • z) ∈ (S).graph) hw_emb).mp hs'
  exact residual_radial_pairing ε hε h hh hb m g k t f (y+(Real.exp (2*t):ℂ) • z) r hs hr

private theorem zero_coupling_potentialMap_zero
    (u : KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw 0 0 0 0) :
    KFCausalClockFloorPotentialOutputClosure.potentialMap ε hε h hh hw 0 0 0 u=0 := by
  apply KFCausalClockFloorOrbitFactorGraphs.coordinates_detect_zero
  intro i
  change coordinateLp i (orderedOutputLp
    (KFCausalClockFloorAveragedRegularity.growingMap ε hε h hh hw 0 0 0 u))=0
  rw [coordinate_ordered]
  by_cases hi : i.val<5
  · simp only [hi,if_true]
  · simp only [hi,if_false]
    have hg := KFCausalClockFloorOrbitFactorGraphs.growing_factor_graph
      ε hε h hh hw 0 0 0 u i
    exact (KFCausalClockFloorOrbitFactorGraphs.factorOperator ε hε h i).graph_fst_eq_zero_snd hg
      (by simp only [zero_growingWeight_ge_five i hi,zero_smul,map_zero])

private theorem zero_coupling_potential_output_zero
    (w : KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hw 0 0 0) :
    KFCausalClosedGraphForm.energyOutput
      (KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw 0 0 0) w=0 := by
  let PD0 := KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw 0 0 0
  refine congrFun ((KFCausalClockFloorPotentialHamiltonian.referenceLift_dense
    ε hε h hh hw 0 0 0).equalizer
    (KFCausalClosedGraphForm.energyOutput PD0).continuous continuous_const ?_) w
  funext u
  exact (KFCausalClockFloorPotentialHamiltonian.referenceLift_output ε hε h hh hw 0 0 0 u).trans
    (zero_coupling_potentialMap_zero ε hε h hh hb u)

theorem zero_coupling_residual_eq_static :
    KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw 0 0 0 0 = (T) := by
  let S0 := KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw 0 0 0 0
  let SD0 := KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw 0 0 0 0
  let PD0 := KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw 0 0 0
  let P0 := KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw 0 0 0
  apply selfadjoint_eq_of_le S0 (T)
    (KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian_selfAdjoint ε hε h hh hw 0 0 0 0)
    (KFCausalClockFloorStaticOperator.selfAdjoint ε hε h)
  apply LinearPMap.le_graph_iff.mp
  rintro ⟨x,s⟩ hxs
  let w := KFCausalClosedGraphForm.formLift SD0 ⟨x,LinearPMap.mem_domain_of_mem_graph hxs⟩
  let pw := KFCausalClockFloorResidualFormSplit.potentialLift ε hε h hh hw 0 0 0 0 w
  have hpw_emb : KFCausalClosedGraphForm.embedding PD0 pw=x :=
    (KFCausalClockFloorResidualFormSplit.potentialLift_embedding ε hε h hh hw 0 0 0 0 w).trans
      (KFCausalClosedGraphForm.embedding_formLift SD0 _)
  have hp0' : (KFCausalClosedGraphForm.embedding PD0 pw,0) ∈ P0.graph := by
    apply form_graph PD0 pw 0
    intro v
    rw [zero_coupling_potential_output_zero ε hε h hh hb pw,inner_zero_left,inner_zero_left]
  have hp0 : (x,0) ∈ P0.graph :=
    (congrArg (fun a : Hilbert => (a,(0:Hilbert)) ∈ P0.graph) hpw_emb).mp hp0'
  have ht := KFCausalClockFloorResidualStaticPotentialDecomposition.static_graph_of_residual
    ε hε h hh hw 0 0 0 0 x s 0 hxs hp0
  simpa only [smul_zero,sub_zero] using ht

include hh hb in
theorem static_radial_pairing (f y r : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hr : (f,r) ∈ (K).graph) :
    -(h^2/ε^2)*‖f‖^2 ≤ (inner ℂ y r).re := by
  have hs : (f,y) ∈
      (KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw 0 0 0 0).graph := by
    rwa [zero_coupling_residual_eq_static ε hε h hh hb]
  exact residual_radial_pairing ε hε h hh hb 0 0 0 0 f y r hs hr

include hh hb in
theorem static_radial_sum_norm_sq (f y r : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hr : (f,r) ∈ (K).graph) :
    ‖r‖^2+‖y‖^2 ≤ ‖r+y‖^2+2*(h^2/ε^2)*‖f‖^2 := by
  have hs : (f,y) ∈
      (KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw 0 0 0 0).graph := by
    rwa [zero_coupling_residual_eq_static ε hε h hh hb]
  have hsq := residual_radial_sum_norm_sq ε hε h hh hb 0 0 0 0 f y r hs hr
  simpa only [mul_zero,Real.exp_zero,Complex.ofReal_one,one_smul,one_mul,mul_one] using hsq

#print axioms residual_radial_in_averaged_domain
#print axioms hamiltonian_graph_of_residual_radial
#print axioms residual_radial_pairing
#print axioms residual_radial_sum_norm_sq
#print axioms static_potential_radial_pairing
#print axioms zero_coupling_residual_eq_static
#print axioms static_radial_pairing
#print axioms static_radial_sum_norm_sq
end
end UnifiedTheory.Audit.KFCausalClockFloorResidualRadialCrossEstimate
