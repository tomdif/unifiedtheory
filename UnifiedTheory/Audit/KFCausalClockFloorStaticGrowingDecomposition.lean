/- Exact static/growing decomposition on the ORIGINAL interacting form.
The static reference-domain converse uses the proved original static core.
The full form-domain restriction is retained; no maximal intersection or
simultaneous graph-density conclusion is inferred from separate cores. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorGrowingCommonDomain

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticGrowingDecomposition
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorAveragedRegularity
open KFCausalBoundedFormCurve (formOperator gram)
open KFCausalMassFormOperator (graph_domain_iff)

private theorem graph_pairing {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (D : KFCausalClosedGraphForm.Data X Y)
    (u : KFCausalClosedGraphForm.FormSpace D) (x y : X)
    (hx : KFCausalClosedGraphForm.embedding D u=x) :
    (x,y) ∈ (KFCausalClosedGraphForm.hamiltonian D).graph ↔
      ∀ v, inner ℂ (KFCausalClosedGraphForm.energyOutput D u)
        (KFCausalClosedGraphForm.energyOutput D v) =
          inner ℂ y (KFCausalClosedGraphForm.embedding D v) := by
  rw [← hx]
  exact (graph_domain_iff _ _ _).trans (KFCausalClosedGraphForm.hamiltonian_domain_characterization D u y)

private theorem transport_pairing {X V Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (f : V → X) (hf : Function.Surjective f)
    (J : X → Y) (A : X → Z) (j : V → Y) (a : V → Z)
    (hj : ∀ v, J (f v)=j v) (ha : ∀ v, A (f v)=a v) (u : V) (y : Y) :
    (∀ v, inner ℂ (a u) (a v)=inner ℂ y (j v)) ↔
      ∀ v, inner ℂ (A (f u)) (A v)=inner ℂ y (J v) := by
  constructor
  · intro hp v
    obtain ⟨w,rfl⟩ := hf v
    simpa only [ha,hj] using hp w
  · intro hp v
    simpa only [ha,hj] using hp (f v)

private theorem dense_pairing {X V Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (S : V → X) (hS : DenseRange S) (J : X →L[ℂ] Y) (E : X →L[ℂ] Z)
    (j : V → Y) (a : V → Z) (hj : ∀ v, J (S v)=j v) (ha : ∀ v, E (S v)=a v)
    (u : V) (y : Y) :
    (∀ w, inner ℂ (E (S u)) (E w)=inner ℂ y (J w)) ↔
      ∀ v, inner ℂ (a u) (a v)=inner ℂ y (j v) := by
  constructor
  · intro hp v
    simpa only [ha,hj] using hp (S v)
  · intro hp w
    have hleft : Continuous (fun v : X => inner ℂ (E (S u)) (E v)) :=
      continuous_const.inner E.continuous
    have hright : Continuous (fun v : X => inner ℂ y (J v)) :=
      continuous_const.inner J.continuous
    have he := hS.equalizer hleft hright
      (funext (fun v => by simpa only [Function.comp_apply,ha,hj] using hp v))
    exact congrFun he w

private theorem sum_pairing {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (J : X →L[ℂ] Y) (A B : X →L[ℂ] Z) (t : ℝ) (u : X) (y z : Y)
    (ha : ∀ v, inner ℂ (A u) (A v)=inner ℂ y (J v))
    (hb : ∀ v, inner ℂ (B u) (B v)=inner ℂ z (J v)) (v : X) :
    inner ℂ u (formOperator A B t v)=inner ℂ (y+Real.exp (2*t) • z) (J v) := by
  simp only [formOperator,gram,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,inner_add_right,inner_smul_right_eq_smul,
    ContinuousLinearMap.adjoint_inner_right,ha v,hb v,inner_add_left,inner_smul_left_eq_smul]

private theorem subtract_static_pairing {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (J : X →L[ℂ] Y) (A B : X →L[ℂ] Z) (t : ℝ) (u : X) (y z : Y)
    (hh : ∀ v, inner ℂ u (formOperator A B t v)=inner ℂ y (J v))
    (hg : ∀ v, inner ℂ (B u) (B v)=inner ℂ z (J v)) (v : X) :
    inner ℂ (A u) (A v)=inner ℂ (y-Real.exp (2*t) • z) (J v) := by
  have he := hh v
  simp only [formOperator,gram,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,inner_add_right,inner_smul_right_eq_smul,
    ContinuousLinearMap.adjoint_inner_right,hg v] at he
  rw [inner_sub_left,inner_smul_left_eq_smul]
  exact eq_sub_of_add_eq he

private theorem subtract_growing_pairing {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (J : X →L[ℂ] Y) (A B : X →L[ℂ] Z) (t : ℝ) (u : X) (y z : Y)
    (hh : ∀ v, inner ℂ u (formOperator A B t v)=inner ℂ y (J v))
    (hs : ∀ v, inner ℂ (A u) (A v)=inner ℂ z (J v)) (v : X) :
    Real.exp (2*t) • inner ℂ (B u) (B v)=inner ℂ (y-z) (J v) := by
  rw [inner_sub_left,← hh v]
  simp only [formOperator,gram,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,inner_add_right,inner_smul_right_eq_smul,
    ContinuousLinearMap.adjoint_inner_right,hs v]
  abel

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ : ℝ)
local notation "V" => FormSpace ε hε h hh hb m g κ 0
local notation "J" => embedding ε hε h hh hb m g κ 0
local notation "A" => staticMap ε hε h hh hb m g κ
local notation "B" => growingMap ε hε h hh hb m g κ
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb m g κ
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb m g κ
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "AV" => KFCausalClockFloorAveragedEnergy.AveragedSpace ε hε h (hamiltonian_bound ε h hb) hh m g κ 0
local notation "AJ" => KFCausalClockFloorAveragedEnergy.embedding ε hε h (hamiltonian_bound ε h hb) hh m g κ 0
local notation "AA" => KFCausalClockFloorStaticRootSource.staticOutput ε hε h hh hb m g κ 0
local notation "S" => KFCausalClockFloorStaticRootSource.source ε hε h hh hb m g κ 0
local notation "D" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hb m g κ 0
local notation "L" => KFCausalClockFloorStaticHamiltonian.rootLift ε hε h hh hb m g κ 0
local notation "E" => KFCausalClockFloorStaticOutputClosure.extension ε hε h hh hb m g κ 0
local notation "RJ" => KFCausalClosedGraphForm.embedding (KFCausalClockFloorStaticRootSource.rootData ε hε h)

private theorem averaged_static_graph_iff (u : AV) (y : Hilbert) :
    (AJ u,y) ∈ (T).graph ↔ ∀ v : AV, inner ℂ (AA u) (AA v)=inner ℂ y (AJ v) := by
  have he := congrArg (fun M : Hilbert →ₗ.[ℂ] Hilbert => (AJ u,y) ∈ M.graph)
    (KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hb m g κ 0)
  have hj : KFCausalClosedGraphForm.embedding D (L (S u))=AJ u :=
    (KFCausalClockFloorStaticHamiltonian.rootLift_embedding ε hε h hh hb m g κ 0 (S u)).trans
      (KFCausalClockFloorStaticRootSource.source_embedding ε hε h hh hb m g κ 0 u)
  have hc := graph_pairing D (L (S u)) (AJ u) y hj
  have ht := transport_pairing L
    (KFCausalClockFloorStaticHamiltonian.rootLift_surjective ε hε h hh hb m g κ 0)
    (KFCausalClosedGraphForm.embedding D) (KFCausalClosedGraphForm.energyOutput D) RJ E
    (KFCausalClockFloorStaticHamiltonian.rootLift_embedding ε hε h hh hb m g κ 0)
    (KFCausalClockFloorStaticHamiltonian.rootLift_output ε hε h hh hb m g κ 0) (S u) y
  have hd := dense_pairing S (KFCausalClockFloorStaticRootSource.source_dense ε hε h hh hb m g κ 0)
    RJ E AJ AA (KFCausalClockFloorStaticRootSource.source_embedding ε hε h hh hb m g κ 0)
    (KFCausalClockFloorStaticOutputClosure.extension_source ε hε h hh hb m g κ 0) u y
  exact (Iff.of_eq he.symm).trans (hc.trans (ht.symm.trans hd))

theorem static_reference_graph_iff (u : V) (y : Hilbert) :
    (J u,y) ∈ (T).graph ↔ ∀ v : V, inner ℂ (A u) (A v)=inner ℂ y (J v) := by
  let f : AV → V := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hb m g κ 0
  have hf : Function.Surjective f :=
    KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hb m g κ 0
  have hj (v : AV) : J (f v)=AJ v :=
    KFCausalClockFloorAveragedHamiltonian.graphFormVector_embedding ε hε h hh hb m g κ 0 v
  have ha (v : AV) : A (f v)=AA v :=
    congrArg KFCausalAveragedOutputRescaling.staticOutputLp
      (KFCausalClockFloorAveragedHamiltonian.graphFormVector_output ε hε h hh hb m g κ 0 v)
  obtain ⟨w,hw⟩ := hf u
  have he := (averaged_static_graph_iff ε hε h hh hb m g κ w y).trans
    (transport_pairing f hf J A AJ AA hj ha w y)
  have he' : (J (f w),y) ∈ (T).graph ↔
      ∀ v : V, inner ℂ (A (f w)) (A v)=inner ℂ y (J v) := by
    simpa only [hj w] using he
  exact (congrArg (fun z : V => (J z,y) ∈ (T).graph ↔
    ∀ v : V, inner ℂ (A z) (A v)=inner ℂ y (J v)) hw).mp he'

theorem sum_graph (t : ℝ) (u : V) (y z : Hilbert)
    (hs : (J u,y) ∈ (T).graph) (hg : (J u,z) ∈ (G).graph) :
    (J u,y+Real.exp (2*t) • z) ∈ (H t).graph := by
  apply (graph_domain_iff (H t) _ _).mpr
  apply (KFCausalClockFloorAveragedHamiltonianBridge.hamiltonian_reference_domain ε hε h hh hb m g κ t u _).mpr
  exact sum_pairing J A B t u y z
    ((static_reference_graph_iff ε hε h hh hb m g κ u y).mp hs)
    ((KFCausalClockFloorGrowingHamiltonian.reference_domain_characterization ε hε h hh hb m g κ u z).mp
      ((graph_domain_iff G _ _).mp hg))

theorem static_graph (t : ℝ) (x y z : Hilbert)
    (hf : (x,y) ∈ (H t).graph) (hg : (x,z) ∈ (G).graph) :
    (x,y-Real.exp (2*t) • z) ∈ (T).graph := by
  let u : V := KFCausalClockFloorAveragedHamiltonianBridge.referenceLift ε hε h hh hb m g κ t
    ⟨x,LinearPMap.mem_domain_of_mem_graph hf⟩
  have hj : J u=x := KFCausalClockFloorAveragedHamiltonianBridge.embedding_referenceLift ε hε h hh hb m g κ t _
  have hf' : (J u,y) ∈ (H t).graph := by simpa only [hj] using hf
  have hg' : (J u,z) ∈ (G).graph := by simpa only [hj] using hg
  have hp := (KFCausalClockFloorAveragedHamiltonianBridge.hamiltonian_reference_domain ε hε h hh hb m g κ t u y).mp
    ((graph_domain_iff (H t) _ _).mp hf')
  have hq := (KFCausalClockFloorGrowingHamiltonian.reference_domain_characterization ε hε h hh hb m g κ u z).mp
    ((graph_domain_iff G _ _).mp hg')
  have ht := (static_reference_graph_iff ε hε h hh hb m g κ u _).mpr
    (subtract_static_pairing J A B t u y z hp hq)
  simpa only [hj] using ht

theorem growing_graph (t : ℝ) (x y z : Hilbert)
    (hf : (x,y) ∈ (H t).graph) (hs : (x,z) ∈ (T).graph) :
    (x,(Real.exp (2*t))⁻¹ • (y-z)) ∈ (G).graph := by
  let u : V := KFCausalClockFloorAveragedHamiltonianBridge.referenceLift ε hε h hh hb m g κ t
    ⟨x,LinearPMap.mem_domain_of_mem_graph hf⟩
  have hj : J u=x := KFCausalClockFloorAveragedHamiltonianBridge.embedding_referenceLift ε hε h hh hb m g κ t _
  have hf' : (J u,y) ∈ (H t).graph := by simpa only [hj] using hf
  have hs' : (J u,z) ∈ (T).graph := by simpa only [hj] using hs
  have hp := (KFCausalClockFloorAveragedHamiltonianBridge.hamiltonian_reference_domain ε hε h hh hb m g κ t u y).mp
    ((graph_domain_iff (H t) _ _).mp hf')
  have hq := (static_reference_graph_iff ε hε h hh hb m g κ u z).mp hs'
  have hg := (graph_domain_iff G (J u) ((Real.exp (2*t))⁻¹ • (y-z))).mpr
    ((KFCausalClockFloorGrowingHamiltonian.reference_domain_characterization ε hε h hh hb m g κ u ((Real.exp (2*t))⁻¹ • (y-z))).mpr
      (fun v => by
        have he := congrArg (fun q : ℂ => (Real.exp (2*t))⁻¹ • q)
          (subtract_growing_pairing J A B t u y z hp hq v)
        simpa only [smul_smul,inv_mul_cancel₀ (Real.exp_ne_zero _),one_smul,
          inner_smul_left_eq_smul] using he))
  simpa only [hj] using hg

theorem common_domain_eq (t : ℝ) :
    (H t).domain ⊓ (G).domain=(H t).domain ⊓ (T).domain := by
  ext x
  constructor
  · rintro ⟨hf,hg⟩
    exact ⟨hf,LinearPMap.mem_domain_of_mem_graph
      (static_graph ε hε h hh hb m g κ t x _ _ ((H t).mem_graph ⟨x,hf⟩) ((G).mem_graph ⟨x,hg⟩))⟩
  · rintro ⟨hf,hs⟩
    exact ⟨hf,LinearPMap.mem_domain_of_mem_graph
      (growing_graph ε hε h hh hb m g κ t x _ _ ((H t).mem_graph ⟨x,hf⟩) ((T).mem_graph ⟨x,hs⟩))⟩

theorem original_common_domain_eq (t : ℝ) :
    (H t).domain ⊓ (G).domain=((T).domain ⊓ (G).domain) ⊓ (J).toLinearMap.range := by
  ext x
  constructor
  · rintro ⟨hf,hg⟩
    have hs := LinearPMap.mem_domain_of_mem_graph
      (static_graph ε hε h hh hb m g κ t x _ _ ((H t).mem_graph ⟨x,hf⟩) ((G).mem_graph ⟨x,hg⟩))
    refine ⟨⟨hs,hg⟩,?_⟩
    exact ⟨KFCausalClockFloorAveragedHamiltonianBridge.referenceLift ε hε h hh hb m g κ t ⟨x,hf⟩,
      KFCausalClockFloorAveragedHamiltonianBridge.embedding_referenceLift ε hε h hh hb m g κ t _⟩
  · rintro ⟨⟨hs,hg⟩,⟨u,hu⟩⟩
    change J u=x at hu
    have hsg : (J u,T ⟨x,hs⟩) ∈ (T).graph := by simpa only [hu] using (T).mem_graph ⟨x,hs⟩
    have hgg : (J u,G ⟨x,hg⟩) ∈ (G).graph := by simpa only [hu] using (G).mem_graph ⟨x,hg⟩
    have hsum := sum_graph ε hε h hh hb m g κ t u _ _ hsg hgg
    rw [hu] at hsum
    exact ⟨LinearPMap.mem_domain_of_mem_graph hsum,hg⟩

#print axioms static_reference_graph_iff
#print axioms sum_graph
#print axioms static_graph
#print axioms growing_graph
#print axioms common_domain_eq
#print axioms original_common_domain_eq
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticGrowingDecomposition
