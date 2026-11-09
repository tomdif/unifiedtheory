/- Exact operator decomposition relating the residual Hamiltonian S(t),
the maximal static operator T, and the closed potential Hamiltonian P on
the completed residual form, valid for all real couplings (including zero
vacuum coupling). On Dom S(t) and on Dom H(t), membership in Dom P and
Dom T are equivalent. -/
import UnifiedTheory.Audit.KFCausalClockFloorResidualFormSplit
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianRadialSum
import UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialSum

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorResidualStaticPotentialDecomposition
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp)
open KFCausalClockFloorResidualFormSplit (static_graph potential_graph staticLift
  potentialLift staticLift_embedding potentialLift_embedding residual_inner_split)

private theorem graph_domain_iff {H : Type*} [AddCommGroup H] [Module ℂ H]
    (A : H →ₗ.[ℂ] H) (x y : H) :
    ((x,y) ∈ A.graph) ↔ ∃ hx : x ∈ A.domain, A ⟨x,hx⟩=y := by
  constructor
  · intro hg
    have hx := LinearPMap.mem_domain_of_mem_graph hg
    exact ⟨hx,A.mem_graph_snd_inj' (A.mem_graph ⟨x,hx⟩) hg rfl⟩
  · rintro ⟨hx,rfl⟩
    exact A.mem_graph ⟨x,hx⟩

private theorem sub_of_add_left {a b c : ℂ} (h : a=b+c) : b=a-c := by
  linear_combination -h

private theorem sub_of_add_right {a b c : ℂ} (h : a=b+c) : c=a-b := by
  linear_combination -h

private theorem exp_solve_right (t : ℝ) {a b c : ℂ}
    (h : a=b+(Real.exp (2*t):ℂ)*c) :
    c=(Real.exp (-2*t):ℂ)*(a-b) := by
  have he : (Real.exp (-2*t):ℂ)*(Real.exp (2*t):ℂ)=1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add,show -2*t+2*t=(0:ℝ) by ring,
      Real.exp_zero,Complex.ofReal_one]
  have hc : (Real.exp (2*t):ℂ)*c=a-b := sub_of_add_right h
  calc
    c = ((Real.exp (-2*t):ℂ)*(Real.exp (2*t):ℂ))*c := by rw [he,one_mul]
    _ = (Real.exp (-2*t):ℂ)*((Real.exp (2*t):ℂ)*c) := mul_assoc _ _ _
    _ = (Real.exp (-2*t):ℂ)*(a-b) := congrArg ((Real.exp (-2*t):ℂ)*·) hc

private theorem inner_add_smul_exp_left (t : ℝ) (y z x : Hilbert) :
    inner ℂ y x+(Real.exp (2*t):ℂ)*inner ℂ z x=
      inner ℂ (y+(Real.exp (2*t):ℂ) • z) x := by
  rw [inner_add_left,inner_smul_left,Complex.conj_ofReal]

private theorem inner_sub_smul_exp_left (t : ℝ) (s z x : Hilbert) :
    inner ℂ s x-(Real.exp (2*t):ℂ)*inner ℂ z x=
      inner ℂ (s-(Real.exp (2*t):ℂ) • z) x := by
  rw [inner_sub_left,inner_smul_left,Complex.conj_ofReal]

private theorem inner_smul_exp_sub_left (t : ℝ) (s y x : Hilbert) :
    (Real.exp (-2*t):ℂ)*(inner ℂ s x-inner ℂ y x)=
      inner ℂ ((Real.exp (-2*t):ℂ) • (s-y)) x := by
  rw [inner_smul_left,inner_sub_left,Complex.conj_ofReal]

private theorem source_dense {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (J : X →L[ℂ] Hilbert) (A : X →L[ℂ] EnergyOutputSpace)
    (F : X → KFCausalClosedGraphForm.FormSpace D)
    (hF : ∀ u, WithLp.ofLp (F u).val=(J u,A u))
    (hgraph : D.operator.graph=(J.prod A).toLinearMap.range.topologicalClosure) :
    DenseRange F := by
  intro w
  have hw : WithLp.ofLp w.val ∈ (J.prod A).toLinearMap.range.topologicalClosure := by
    rw [← hgraph]
    exact w.property
  obtain ⟨z,hz,ht⟩ := mem_closure_iff_seq_limit.mp
    (show WithLp.ofLp w.val ∈ closure ((J.prod A).toLinearMap.range : Set (Hilbert × EnergyOutputSpace)) from hw)
  have hex (n : ℕ) : ∃ u : X, (J u,A u)=z n := hz n
  choose u hu using hex
  have hu' : Tendsto (fun n => WithLp.ofLp (F (u n)).val) atTop (𝓝 (WithLp.ofLp w.val)) := by
    simpa only [hF,hu] using ht
  have hl : Tendsto (fun n => F (u n)) atTop (𝓝 w) := by
    apply tendsto_subtype_rng.mpr
    exact ((WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert EnergyOutputSpace).symm.continuous.tendsto
      (WithLp.ofLp w.val)).comp hu'
  exact mem_closure_of_tendsto hl (Eventually.of_forall (fun n => Set.mem_range_self (u n)))

private theorem dense_pairing {X : Type*}
    (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (S : X → KFCausalClosedGraphForm.FormSpace D) (hS : DenseRange S)
    (u : KFCausalClosedGraphForm.FormSpace D) (y : Hilbert) :
    ((KFCausalClosedGraphForm.embedding D u,y) ∈ (KFCausalClosedGraphForm.hamiltonian D).graph) ↔
      ∀ v : X, inner ℂ (KFCausalClosedGraphForm.energyOutput D u)
        (KFCausalClosedGraphForm.energyOutput D (S v))=
          inner ℂ y (KFCausalClosedGraphForm.embedding D (S v)) := by
  refine (graph_domain_iff _ _ _).trans
    ((KFCausalClosedGraphForm.hamiltonian_domain_characterization D u y).trans ?_)
  constructor
  · intro hp v
    exact hp (S v)
  · intro hp w
    have hleft : Continuous (fun z => inner ℂ (KFCausalClosedGraphForm.energyOutput D u)
        (KFCausalClosedGraphForm.energyOutput D z)) :=
      continuous_const.inner (KFCausalClosedGraphForm.energyOutput D).continuous
    have hright : Continuous (fun z => inner ℂ y (KFCausalClosedGraphForm.embedding D z)) :=
      continuous_const.inner (KFCausalClosedGraphForm.embedding D).continuous
    exact congrFun (hS.equalizer hleft hright (funext hp)) w

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
local notation "V" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hb m g k 0
local notation "J" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb m g k 0
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hb m g k t
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hb m g k t
local notation "SJ" => KFCausalClosedGraphForm.embedding SD
local notation "SB" => KFCausalClosedGraphForm.energyOutput SD
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hb m g k t
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hb m g k 0
local notation "TV" => KFCausalClockFloorStaticHamiltonian.StaticForm ε hε h hh hb m g k 0
local notation "TJ" => KFCausalClosedGraphForm.embedding TD
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hb m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hb m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hb m g k
local notation "SR" => KFCausalClockFloorStaticPotentialHamiltonian.referenceLift ε hε h hh hb m g k t

private theorem static_reference_range_eq :
    (TD).operator.graph=
      ((J).prod (KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hb m g k)).toLinearMap.range.topologicalClosure := by
  rw [show (TD).operator=KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hb m g k 0 from rfl,
    KFCausalClockFloorStaticOutputClosure.operator_graph]
  congr 1
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    refine ⟨KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hb m g k 0 a,?_⟩
    exact Prod.ext
      (KFCausalClockFloorAveragedHamiltonian.graphFormVector_embedding ε hε h hh hb m g k 0 a)
      (congrArg staticOutputLp
        (KFCausalClockFloorAveragedHamiltonian.graphFormVector_output ε hε h hh hb m g k 0 a))
  · rintro ⟨u,rfl⟩
    let lift := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hb m g k 0
    have hl : Function.Surjective lift :=
      KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hb m g k 0
    let a := Classical.choose (hl u)
    have ha : lift a=u := Classical.choose_spec (hl u)
    refine ⟨a,?_⟩
    exact Prod.ext
      ((KFCausalClockFloorAveragedHamiltonian.graphFormVector_embedding ε hε h hh hb m g k 0 a).symm.trans
        (congrArg J ha))
      ((congrArg staticOutputLp
        (KFCausalClockFloorAveragedHamiltonian.graphFormVector_output ε hε h hh hb m g k 0 a)).symm.trans
          (congrArg (KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hb m g k) ha))

private theorem staticLift_reference_dense :
    DenseRange (fun u : V => staticLift ε hε h hh hb m g k t (SR u)) := by
  apply source_dense TD J (KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hb m g k)
    (fun u : V => staticLift ε hε h hh hb m g k t (SR u)) ?_
    (static_reference_range_eq ε hε h hh hb m g k)
  intro u
  exact Prod.ext
    (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding ε hε h hh hb m g k t u)
    ((congrArg staticOutputLp
      (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_output ε hε h hh hb m g k t u)).trans
        (KFCausalClockFloorResidualFormSplit.source_static ε hε h hh hb m g k t u))

private theorem potentialLift_reference_eq (u : V) :
    potentialLift ε hε h hh hb m g k t (SR u)=
      KFCausalClockFloorPotentialHamiltonian.referenceLift ε hε h hh hb m g k u := by
  apply KFCausalClosedGraphForm.embedding_injective PD
  exact (potentialLift_embedding ε hε h hh hb m g k t (SR u)).trans
    ((KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding ε hε h hh hb m g k t u).trans
      (KFCausalClockFloorPotentialHamiltonian.referenceLift_embedding ε hε h hh hb m g k u).symm)

private theorem potentialLift_reference_dense :
    DenseRange (fun u : V => potentialLift ε hε h hh hb m g k t (SR u)) := by
  have he : (fun u : V => potentialLift ε hε h hh hb m g k t (SR u))=
      KFCausalClockFloorPotentialHamiltonian.referenceLift ε hε h hh hb m g k :=
    funext (potentialLift_reference_eq ε hε h hh hb m g k t)
  rw [he]
  exact KFCausalClockFloorPotentialHamiltonian.referenceLift_dense ε hε h hh hb m g k

private theorem static_graph_iff (w : SV) (y : Hilbert) :
    (SJ w,y) ∈ (T).graph ↔
      ∀ u : V, inner ℂ (TB (staticLift ε hε h hh hb m g k t w))
        (TB (staticLift ε hε h hh hb m g k t (SR u)))=inner ℂ y (J u) := by
  have heq : ((SJ w,y) ∈ (T).graph) ↔
      ((TJ (staticLift ε hε h hh hb m g k t w),y) ∈
        (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hb m g k 0).graph) := by
    rw [KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hb m g k 0]
    exact iff_of_eq (congrArg (fun x : Hilbert => (x,y) ∈ (T).graph)
      (staticLift_embedding ε hε h hh hb m g k t w).symm)
  exact heq.trans (dense_pairing TD (fun u : V => staticLift ε hε h hh hb m g k t (SR u))
    (staticLift_reference_dense ε hε h hh hb m g k t) (staticLift ε hε h hh hb m g k t w) y)

private theorem potential_graph_iff (w : SV) (z : Hilbert) :
    (SJ w,z) ∈ (P).graph ↔
      ∀ u : V, inner ℂ (PB (potentialLift ε hε h hh hb m g k t w))
        (PB (potentialLift ε hε h hh hb m g k t (SR u)))=inner ℂ z (J u) := by
  have heq : ((SJ w,z) ∈ (P).graph) ↔
      ((PJ (potentialLift ε hε h hh hb m g k t w),z) ∈ (P).graph) :=
    iff_of_eq (congrArg (fun x : Hilbert => (x,z) ∈ (P).graph)
      (potentialLift_embedding ε hε h hh hb m g k t w).symm)
  exact heq.trans (dense_pairing PD (fun u : V => potentialLift ε hε h hh hb m g k t (SR u))
    (potentialLift_reference_dense ε hε h hh hb m g k t) (potentialLift ε hε h hh hb m g k t w) z)

private theorem residual_graph_iff (w : SV) (s : Hilbert) :
    (SJ w,s) ∈ (S).graph ↔
      ∀ u : V, inner ℂ (SB w) (SB (SR u))=inner ℂ s (J u) :=
  dense_pairing SD SR (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_dense ε hε h hh hb m g k t) w s

theorem residual_form_domains (x : (S).domain) :
    (x:Hilbert) ∈ (KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h).domain ∧
      (x:Hilbert) ∈ (KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hb m g k).domain := by
  let w := KFCausalClosedGraphForm.formLift SD x
  have hw : SJ w=(x:Hilbert) := KFCausalClosedGraphForm.embedding_formLift SD x
  have hs0 : SJ w ∈ (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hb m g k 0).domain :=
    LinearPMap.mem_domain_of_mem_graph (staticLift ε hε h hh hb m g k t w).property
  have hp0 : SJ w ∈ (KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hb m g k).domain :=
    LinearPMap.mem_domain_of_mem_graph (potentialLift ε hε h hh hb m g k t w).property
  rw [KFCausalClockFloorStaticOutputClosure.operator_domain] at hs0
  exact ⟨(congrArg (fun a : Hilbert => a ∈ (KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h).domain) hw).mp hs0,
    (congrArg (fun a : Hilbert => a ∈ (KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hb m g k).domain) hw).mp hp0⟩

theorem sum_graph (w : SV) (y z : Hilbert)
    (ht : (SJ w,y) ∈ (T).graph) (hp : (SJ w,z) ∈ (P).graph) :
    (SJ w,y+(Real.exp (2*t):ℂ) • z) ∈ (S).graph := by
  apply (residual_graph_iff ε hε h hh hb m g k t w _).mpr
  intro u
  have h1 := (static_graph_iff ε hε h hh hb m g k t w y).mp ht u
  have h2 := (potential_graph_iff ε hε h hh hb m g k t w z).mp hp u
  have h3 := (residual_inner_split ε hε h hh hb m g k t w (SR u)).trans
    (congrArg₂ (·+·) h1 (congrArg ((Real.exp (2*t):ℂ)*·) h2))
  exact h3.trans (inner_add_smul_exp_left t y z (J u))

theorem static_graph_of_residual (x s z : Hilbert)
    (hs : (x,s) ∈ (S).graph) (hp : (x,z) ∈ (P).graph) :
    (x,s-(Real.exp (2*t):ℂ) • z) ∈ (T).graph := by
  let w := KFCausalClosedGraphForm.formLift SD ⟨x,LinearPMap.mem_domain_of_mem_graph hs⟩
  have hw : SJ w=x := KFCausalClosedGraphForm.embedding_formLift SD _
  have hs' : (SJ w,s) ∈ (S).graph :=
    (congrArg (fun a : Hilbert => (a,s) ∈ (S).graph) hw.symm).mp hs
  have hp' : (SJ w,z) ∈ (P).graph :=
    (congrArg (fun a : Hilbert => (a,z) ∈ (P).graph) hw.symm).mp hp
  have ht : (SJ w,s-(Real.exp (2*t):ℂ) • z) ∈ (T).graph := by
    apply (static_graph_iff ε hε h hh hb m g k t w _).mpr
    intro u
    have h1 := (residual_graph_iff ε hε h hh hb m g k t w s).mp hs' u
    have h2 := (potential_graph_iff ε hε h hh hb m g k t w z).mp hp' u
    have h3 : inner ℂ s (J u)=
        inner ℂ (TB (staticLift ε hε h hh hb m g k t w))
          (TB (staticLift ε hε h hh hb m g k t (SR u)))+
        (Real.exp (2*t):ℂ)*inner ℂ z (J u) :=
      h1.symm.trans ((residual_inner_split ε hε h hh hb m g k t w (SR u)).trans
        (congrArg₂ (·+·) rfl (congrArg ((Real.exp (2*t):ℂ)*·) h2)))
    exact (sub_of_add_left h3).trans (inner_sub_smul_exp_left t s z (J u))
  exact (congrArg (fun a : Hilbert => (a,s-(Real.exp (2*t):ℂ) • z) ∈ (T).graph) hw).mp ht

theorem potential_graph_of_residual (x s y : Hilbert)
    (hs : (x,s) ∈ (S).graph) (ht : (x,y) ∈ (T).graph) :
    (x,(Real.exp (-2*t):ℂ) • (s-y)) ∈ (P).graph := by
  let w := KFCausalClosedGraphForm.formLift SD ⟨x,LinearPMap.mem_domain_of_mem_graph hs⟩
  have hw : SJ w=x := KFCausalClosedGraphForm.embedding_formLift SD _
  have hs' : (SJ w,s) ∈ (S).graph :=
    (congrArg (fun a : Hilbert => (a,s) ∈ (S).graph) hw.symm).mp hs
  have ht' : (SJ w,y) ∈ (T).graph :=
    (congrArg (fun a : Hilbert => (a,y) ∈ (T).graph) hw.symm).mp ht
  have hp : (SJ w,(Real.exp (-2*t):ℂ) • (s-y)) ∈ (P).graph := by
    apply (potential_graph_iff ε hε h hh hb m g k t w _).mpr
    intro u
    have h1 := (residual_graph_iff ε hε h hh hb m g k t w s).mp hs' u
    have h2 := (static_graph_iff ε hε h hh hb m g k t w y).mp ht' u
    have h3 : inner ℂ s (J u)=
        inner ℂ y (J u)+
        (Real.exp (2*t):ℂ)*inner ℂ (PB (potentialLift ε hε h hh hb m g k t w))
          (PB (potentialLift ε hε h hh hb m g k t (SR u))) :=
      h1.symm.trans ((residual_inner_split ε hε h hh hb m g k t w (SR u)).trans
        (congrArg₂ (·+·) h2 rfl))
    exact (exp_solve_right t h3).trans (inner_smul_exp_sub_left t s y (J u))
  exact (congrArg (fun a : Hilbert => (a,(Real.exp (-2*t):ℂ) • (s-y)) ∈ (P).graph) hw).mp hp

theorem common_domain_eq :
    (S).domain ⊓ (P).domain=(S).domain ⊓ (T).domain := by
  ext x
  constructor
  · rintro ⟨hs,hp⟩
    exact ⟨hs,LinearPMap.mem_domain_of_mem_graph
      (static_graph_of_residual ε hε h hh hb m g k t x _ _
        ((S).mem_graph ⟨x,hs⟩) ((P).mem_graph ⟨x,hp⟩))⟩
  · rintro ⟨hs,ht⟩
    exact ⟨hs,LinearPMap.mem_domain_of_mem_graph
      (potential_graph_of_residual ε hε h hh hb m g k t x _ _
        ((S).mem_graph ⟨x,hs⟩) ((T).mem_graph ⟨x,ht⟩))⟩

theorem hamiltonian_common_domain_eq (hb' : |h| ≤ Real.pi*ε/3) :
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
      (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb') m g k t).domain ⊓
      (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
        (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb') m g k).domain =
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
      (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb') m g k t).domain ⊓
      (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh
        (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb') m g k).domain ∧
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
      (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb') m g k t).domain ⊓
      (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
        (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb') m g k).domain =
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
      (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb') m g k t).domain ⊓
      (T).domain := by
  let hw := KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb'
  constructor
  · ext x
    change (x ∈ (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t).domain ∧
        x ∈ (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k).domain) ↔
      (x ∈ (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t).domain ∧
        x ∈ (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k).domain)
    rw [KFCausalClockFloorHamiltonianRadialSum.domain_iff ε hε h hh hb' m g k t x,
      KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb' m g k x]
    tauto
  · ext x
    change (x ∈ (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t).domain ∧
        x ∈ (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k).domain) ↔
      (x ∈ (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t).domain ∧
        x ∈ (T).domain)
    rw [KFCausalClockFloorHamiltonianRadialSum.domain_iff ε hε h hh hb' m g k t x]
    have hc := Set.ext_iff.mp (congrArg SetLike.coe
      (common_domain_eq ε hε h hh hw m g k t)) x
    change (x ∈ (KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k t).domain ∧
        x ∈ (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k).domain) ↔
      (x ∈ (KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k t).domain ∧
        x ∈ (T).domain) at hc
    tauto

#print axioms residual_form_domains
#print axioms sum_graph
#print axioms static_graph_of_residual
#print axioms potential_graph_of_residual
#print axioms common_domain_eq
#print axioms hamiltonian_common_domain_eq
end
end UnifiedTheory.Audit.KFCausalClockFloorResidualStaticPotentialDecomposition
