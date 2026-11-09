/- Unconditional Growing Form Reconstruction for all real couplings:
every regularized potential-form vector lifts to the completed growing form,
the range of the growing-to-potential form projection is the intersection with
the maximal radial square-root domain, and the completed growing-output domain
equals the intersection of the radial square-root domain and the completed
potential-output domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventRoot
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventGrowing

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingFormReconstruction
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorChartPhasePairing (orderedOutputLp)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer (action radial_domain sequence_tendsto)
open KFCausalClockFloorRadialResolventRoot (rootAction root_graph
  action_root_domain rootAction_sequence_tendsto)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOperator rootOutput
  root_domain rootOutput_graph)
open KFCausalClockFloorPotentialHamiltonian (growingLift growingLift_embedding growingLift_output)
open KFCausalClockFloorRadialResolventGrowing (growing_form_norm_sq formAction
  formAction_embedding growingLift_formAction)

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

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k 0
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "GV" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hw m g k
local notation "GJ" => KFCausalClosedGraphForm.embedding GD
local notation "GB" => KFCausalClosedGraphForm.energyOutput GD
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hw m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "R" => rootOutput ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Kr" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h

private theorem growing_triple_closed :
    IsClosed {q : Hilbert × Hilbert × EnergyOutputSpace |
      ∃ u : GV, (GJ u,R u,orderedOutputLp (GB u))=q} := by
  refine closed_isometric_range (GJ).toLinearMap (R) ((orderedOutputLp.comp GB).toLinearMap) ?_
  intro u
  exact (growing_form_norm_sq ε hε h hb hh m g k u).trans
    (congrArg (fun y : EnergyOutputSpace => ‖GJ u‖^2+(‖R u‖^2+‖y‖^2))
      (growingLift_output ε hε h hh hw m g k u))

private theorem reference_growingLift_eq (v : RV) :
    growingLift ε hε h hh hw m g k
      (KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k v)=
      KFCausalClockFloorPotentialHamiltonian.referenceLift ε hε h hh hw m g k v := by
  apply KFCausalClosedGraphForm.embedding_injective PD
  exact (growingLift_embedding ε hε h hh hw m g k
    (KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k v)).trans
    ((KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding ε hε h hh hw m g k v).trans
      (KFCausalClockFloorPotentialHamiltonian.referenceLift_embedding ε hε h hh hw m g k v).symm)

private theorem reference_regularized_in_triple (N : ℝ) (hN : 0 < N) (v : RV) :
    let pv := KFCausalClockFloorPotentialHamiltonian.referenceLift ε hε h hh hw m g k v
    (action ε hε h N hN (PJ pv),rootAction ε hε h N hN (PJ pv),
      PB (KFCausalClockFloorRadialResolventPotential.formAction ε hε h N hN hb hh m g k pv)) ∈
      {q : Hilbert × Hilbert × EnergyOutputSpace |
        ∃ u : GV, (GJ u,R u,orderedOutputLp (GB u))=q} := by
  let gv := KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k v
  let pv := KFCausalClockFloorPotentialHamiltonian.referenceLift ε hε h hh hw m g k v
  let u := formAction ε hε h N hN hb hh m g k gv
  refine ⟨u,?_⟩
  have hgp : GJ gv=PJ pv :=
    (KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding ε hε h hh hw m g k v).trans
      (KFCausalClockFloorPotentialHamiltonian.referenceLift_embedding ε hε h hh hw m g k v).symm
  have hJ : GJ u=action ε hε h N hN (PJ pv) :=
    (formAction_embedding ε hε h N hN hb hh m g k gv).trans
      (congrArg (action ε hε h N hN) hgp)
  have hR : R u=rootAction ε hε h N hN (PJ pv) :=
    (rootOperator ε hε h).mem_graph_snd_inj'
      (rootOutput_graph ε hε h hh hw m g k u)
      (root_graph ε hε h N hN (PJ pv)) hJ
  have hL : growingLift ε hε h hh hw m g k u=
      KFCausalClockFloorRadialResolventPotential.formAction ε hε h N hN hb hh m g k pv :=
    (growingLift_formAction ε hε h N hN hb hh m g k gv).trans
      (congrArg (KFCausalClockFloorRadialResolventPotential.formAction ε hε h N hN hb hh m g k)
        (reference_growingLift_eq ε hε h hh hb m g k v))
  have hP : orderedOutputLp (GB u)=
      PB (KFCausalClockFloorRadialResolventPotential.formAction ε hε h N hN hb hh m g k pv) :=
    (growingLift_output ε hε h hh hw m g k u).symm.trans (congrArg PB hL)
  exact Prod.ext hJ (Prod.ext hR hP)

theorem regularized_potential_in_growing (N : ℝ) (hN : 0 < N) (w : PV) :
    ∃ u : GV, GJ u=action ε hε h N hN (PJ w) ∧
      R u=rootAction ε hε h N hN (PJ w) ∧
      growingLift ε hε h hh hw m g k u=
        KFCausalClockFloorRadialResolventPotential.formAction ε hε h N hN hb hh m g k w := by
  let S := {q : Hilbert × Hilbert × EnergyOutputSpace |
    ∃ u : GV, (GJ u,R u,orderedOutputLp (GB u))=q}
  let Ψ : PV → Hilbert × Hilbert × EnergyOutputSpace := fun z =>
    (action ε hε h N hN (PJ z),rootAction ε hε h N hN (PJ z),
      PB (KFCausalClockFloorRadialResolventPotential.formAction ε hε h N hN hb hh m g k z))
  have hΨ : Continuous Ψ :=
    ((action ε hε h N hN).continuous.comp (PJ).continuous).prodMk
      (((rootAction ε hε h N hN).continuous.comp (PJ).continuous).prodMk
        ((PB).continuous.comp (KFCausalClockFloorRadialResolventPotential.formAction ε hε h N hN hb hh m g k).continuous))
  have hclosed : IsClosed (Ψ ⁻¹' S) := (growing_triple_closed ε hε h hh hb m g k).preimage hΨ
  have hmem : w ∈ Ψ ⁻¹' S := by
    apply closure_minimal (s := Set.range (KFCausalClockFloorPotentialHamiltonian.referenceLift ε hε h hh hw m g k))
      ?_ hclosed ((KFCausalClockFloorPotentialHamiltonian.referenceLift_dense ε hε h hh hw m g k) w)
    rintro _ ⟨v,rfl⟩
    exact reference_regularized_in_triple ε hε h hh hb m g k N hN v
  obtain ⟨u,hu⟩ := hmem
  have hJ : GJ u=action ε hε h N hN (PJ w) :=
    congrArg (Prod.fst : Hilbert × Hilbert × EnergyOutputSpace → Hilbert) hu
  have hR : R u=rootAction ε hε h N hN (PJ w) :=
    congrArg (fun p : Hilbert × Hilbert × EnergyOutputSpace => p.2.1) hu
  have hJ' : PJ (growingLift ε hε h hh hw m g k u)=
      PJ (KFCausalClockFloorRadialResolventPotential.formAction ε hε h N hN hb hh m g k w) :=
    (growingLift_embedding ε hε h hh hw m g k u).trans
      (hJ.trans (KFCausalClockFloorRadialResolventPotential.formAction_embedding
        ε hε h N hN hb hh m g k w).symm)
  exact ⟨u,hJ,hR,KFCausalClosedGraphForm.embedding_injective PD hJ'⟩

theorem potential_domain_regularized_in_growing (N : ℝ) (hN : 0 < N)
    (f : Hilbert) (hf : f ∈ (Tpot).domain) :
    action ε hε h N hN f ∈ (Kr).domain ∧ action ε hε h N hN f ∈ (Tgrow).domain := by
  let w := KFCausalClosedGraphForm.graphVector PD ⟨f,hf⟩
  obtain ⟨u,hJ,_,_⟩ := regularized_potential_in_growing ε hε h hh hb m g k N hN w
  have hJf : GJ u=action ε hε h N hN f :=
    hJ.trans (congrArg (action ε hε h N hN)
      (KFCausalClosedGraphForm.graphVector_embedding PD ⟨f,hf⟩))
  refine ⟨radial_domain ε hε h N hN f,?_⟩
  exact (congrArg (fun x : Hilbert => x ∈ (Tgrow).domain) hJf).mp
    (LinearPMap.mem_domain_of_mem_graph u.property)

theorem reconstruct_growing_form (w : PV) (r : Hilbert)
    (hr : (PJ w,r) ∈ (rootOperator ε hε h).graph) :
    ∃ u : GV, GJ u=PJ w ∧ R u=r ∧ growingLift ε hε h hh hw m g k u=w := by
  let S := {q : Hilbert × Hilbert × EnergyOutputSpace |
    ∃ u : GV, (GJ u,R u,orderedOutputLp (GB u))=q}
  let seq : ℕ → Hilbert × Hilbert × EnergyOutputSpace := fun n =>
    (action ε hε h ((n:ℝ)+1) (by positivity) (PJ w),
      rootAction ε hε h ((n:ℝ)+1) (by positivity) (PJ w),
      PB (KFCausalClockFloorRadialResolventPotential.formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k w))
  have hmem : ∀ n : ℕ, seq n ∈ S := by
    intro n
    obtain ⟨u,hJ,hR,hL⟩ := regularized_potential_in_growing ε hε h hh hb m g k ((n:ℝ)+1) (by positivity) w
    refine ⟨u,Prod.ext hJ (Prod.ext hR ?_)⟩
    exact (growingLift_output ε hε h hh hw m g k u).symm.trans (congrArg PB hL)
  have ht : Tendsto seq atTop (𝓝 (PJ w,r,PB w)) :=
    (sequence_tendsto ε hε h (PJ w)).prodMk_nhds
      ((rootAction_sequence_tendsto ε hε h (PJ w) r hr).prodMk_nhds
        (((PB).continuous.tendsto w).comp
          (KFCausalClockFloorRadialResolventPotentialForm.form_sequence_tendsto ε hε h hb hh m g k w)))
  obtain ⟨u,hu⟩ := (growing_triple_closed ε hε h hh hb m g k).mem_of_tendsto ht
    (Eventually.of_forall hmem)
  have hJ : GJ u=PJ w :=
    congrArg (Prod.fst : Hilbert × Hilbert × EnergyOutputSpace → Hilbert) hu
  have hR : R u=r := congrArg (fun p : Hilbert × Hilbert × EnergyOutputSpace => p.2.1) hu
  have hJ' : PJ (growingLift ε hε h hh hw m g k u)=PJ w :=
    (growingLift_embedding ε hε h hh hw m g k u).trans hJ
  exact ⟨u,hJ,hR,KFCausalClosedGraphForm.embedding_injective PD hJ'⟩

theorem growingLift_range_eq :
    Set.range (growingLift ε hε h hh hw m g k)=
      {w : PV | PJ w ∈ (rootOperator ε hε h).domain} := by
  ext w
  constructor
  · rintro ⟨u,hu⟩
    have hj : PJ w=GJ u :=
      (congrArg PJ hu.symm).trans (growingLift_embedding ε hε h hh hw m g k u)
    exact (congrArg (fun x : Hilbert => x ∈ (rootOperator ε hε h).domain) hj.symm).mp
      (root_domain ε hε h hh hw m g k (GJ u) (GB u) u.property)
  · intro hdom
    obtain ⟨u,_,_,hu⟩ := reconstruct_growing_form ε hε h hh hb m g k w _
      ((rootOperator ε hε h).mem_graph ⟨PJ w,hdom⟩)
    exact ⟨u,hu⟩

theorem growing_domain_iff (f : Hilbert) :
    f ∈ (Tgrow).domain ↔ f ∈ (rootOperator ε hε h).domain ∧ f ∈ (Tpot).domain := by
  constructor
  · intro hf
    have hg := (Tgrow).mem_graph ⟨f,hf⟩
    exact ⟨root_domain ε hε h hh hw m g k f _ hg,
      LinearPMap.mem_domain_of_mem_graph
        (KFCausalClockFloorPotentialOutputClosure.growing_graph ε hε h hh hw m g k f _ hg)⟩
  · rintro ⟨hr,hp⟩
    let w := KFCausalClosedGraphForm.graphVector PD ⟨f,hp⟩
    have hrg : (PJ w,rootOperator ε hε h ⟨f,hr⟩) ∈ (rootOperator ε hε h).graph :=
      (congrArg (fun x : Hilbert => (x,rootOperator ε hε h ⟨f,hr⟩) ∈ (rootOperator ε hε h).graph)
        (KFCausalClosedGraphForm.graphVector_embedding PD ⟨f,hp⟩).symm).mp
          ((rootOperator ε hε h).mem_graph ⟨f,hr⟩)
    obtain ⟨u,hJ,_,_⟩ := reconstruct_growing_form ε hε h hh hb m g k w _ hrg
    have hJf : GJ u=f :=
      hJ.trans (KFCausalClosedGraphForm.graphVector_embedding PD ⟨f,hp⟩)
    exact (congrArg (fun x : Hilbert => x ∈ (Tgrow).domain) hJf).mp
      (LinearPMap.mem_domain_of_mem_graph u.property)

#print axioms regularized_potential_in_growing
#print axioms potential_domain_regularized_in_growing
#print axioms reconstruct_growing_form
#print axioms growingLift_range_eq
#print axioms growing_domain_iff
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingFormReconstruction
