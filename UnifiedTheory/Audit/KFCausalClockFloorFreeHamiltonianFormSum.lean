/- The actual free Hamiltonian is the operator represented by the sum of
the explicit maximal static and radial forms. This is a full graph statement,
with the intersection domain proved rather than postulated. -/
import UnifiedTheory.Audit.KFCausalClockFloorFreeFormSum

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFreeHamiltonianFormSum
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorFreeFormSum
open KFCausalAveragedOutputRescaling (staticOutputLp growingOutputLp)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)

private theorem equal_norm_inner {V H K : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (A : V →ₗ[ℂ] H) (B : V →ₗ[ℂ] K) (hn : ∀ u, ‖A u‖ = ‖B u‖) (u v : V) :
    inner ℂ (A u) (A v) = inner ℂ (B u) (B v) := by
  rw [inner_eq_sum_norm_sq_div_four,inner_eq_sum_norm_sq_div_four]
  simp only [← map_add,← map_sub,← map_smul,hn]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi*ε/3)
local notation "hw" => wide_bound ε hε h hb
local notation "V" => FormSpace ε hε h hh hw 0 0 0 0
local notation "J" => embedding ε hε h hh hw 0 0 0 0
local notation "A" => energyOutput ε hε h hh hw 0 0 0 0
local notation "S" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "R" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "D" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hw 0 0 0
local notation "T" => formTransfer ε hε h hh hw 0 0 0

theorem static_domain (u : V) : J u ∈ (S).domain :=
  (residual_domain_iff ε hε h hh hw 0 (J u)).mp
    (LinearPMap.mem_domain_of_mem_graph
      (KFCausalClockFloorStaticPotentialOutputClosure.reference_graph ε hε h hh hw 0 0 0 0 u))

def staticRoot : V →ₗ[ℂ] Hilbert :=
  (S).toFun.comp ((J).toLinearMap.codRestrict (S).domain (static_domain ε hε h hh hb))

theorem staticRoot_graph (u : V) : (J u,staticRoot ε hε h hh hb u) ∈ (S).graph :=
  (S).mem_graph ⟨J u,static_domain ε hε h hh hb u⟩

theorem staticRoot_norm (u : V) : ‖staticRoot ε hε h hh hb u‖ = ‖staticOutputLp (A u)‖ := by
  let SD := KFCausalClockFloorStaticRootSource.rootData ε hε h
  let w := KFCausalClosedGraphForm.graphVector SD ⟨J u,static_domain ε hε h hh hb u⟩
  have hr : (J u,staticOutputLp (A u)) ∈
      (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hw 0 0 0 0).graph := by
    rw [← residual_operator_eq_static ε hε h hh hw 0]
    exact (congrArg (fun y => (J u,y) ∈
      (KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw 0 0 0 0).graph)
      (residual_source_eq_static ε hε h hh hw 0 u)).mp
        (KFCausalClockFloorStaticPotentialOutputClosure.reference_graph ε hε h hh hw 0 0 0 0 u)
  have he := (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hw 0 0 0 0).mem_graph_snd_inj'
    (KFCausalClockFloorStaticOutputClosure.root_form_graph ε hε h hh hw 0 0 0 0 w) hr rfl
  exact (KFCausalClockFloorStaticOutputClosure.extension_norm ε hε h hh hw 0 0 0 0 w).symm.trans
    (congrArg norm he)

def radialRoot : V →ₗ[ℂ] Hilbert :=
  KFCausalClockFloorResidualFormReconstruction.referenceRootLinear ε hε h hh hb 0 0 0

theorem radialRoot_graph (u : V) : (J u,radialRoot ε hε h hh hb u) ∈ (R).graph :=
  KFCausalClockFloorResidualFormReconstruction.referenceRoot_graph ε hε h hh hb 0 0 0 u

theorem radialRoot_norm (u : V) : ‖radialRoot ε hε h hh hb u‖ = ‖growingOutputLp (A u)‖ := by
  have hres := residual_source_eq_static ε hε h hh hw 0 u
  change KFCausalClockFloorStaticPotentialOutputClosure.selectedOutputLp
    (KFCausalClockFloorAveragedOutputTransport.timeOutputLp 0 0 (A u)) = staticOutputLp (A u) at hres
  rw [KFCausalAveragedOutputRescaling.timeOutputLp_self] at hres
  have hs := KFCausalClockFloorResidualFormReconstruction.reference_output_norm_sq ε hε h hh hb 0 0 0 u
  rw [hres] at hs
  have hp := KFCausalAveragedOutputRescaling.split_norm (A u)
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖KFCausalClockFloorResidualFormReconstruction.referenceRoot ε hε h hh hb 0 0 0 u‖^2 = _
  linarith

theorem staticRoot_inner (u v : V) :
    inner ℂ (staticRoot ε hε h hh hb u) (staticRoot ε hε h hh hb v) =
      inner ℂ (staticOutputLp (A u)) (staticOutputLp (A v)) :=
  equal_norm_inner (staticRoot ε hε h hh hb) (staticOutputLp.comp A).toLinearMap
    (staticRoot_norm ε hε h hh hb) u v

theorem radialRoot_inner (u v : V) :
    inner ℂ (radialRoot ε hε h hh hb u) (radialRoot ε hε h hh hb v) =
      inner ℂ (growingOutputLp (A u)) (growingOutputLp (A v)) :=
  equal_norm_inner (radialRoot ε hε h hh hb) (growingOutputLp.comp A).toLinearMap
    (radialRoot_norm ε hε h hh hb) u v

theorem transferred_pairing (t : ℝ) (u v : V) :
    inner ℂ (energyOutput ε hε h hh hw 0 0 0 t (T 0 t u))
      (energyOutput ε hε h hh hw 0 0 0 t (T 0 t v)) =
      inner ℂ (staticRoot ε hε h hh hb u) (staticRoot ε hε h hh hb v)+
        (Real.exp (2*t):ℂ)*inner ℂ (radialRoot ε hε h hh hb u) (radialRoot ε hε h hh hb v) := by
  have hp : inner ℂ
      (KFCausalClockFloorAveragedOutputTransport.timeOutputLp 0 t (A u))
      (KFCausalClockFloorAveragedOutputTransport.timeOutputLp 0 t (A v)) =
      inner ℂ (staticOutputLp (A u)) (staticOutputLp (A v))+
        (Real.exp (2*t):ℂ)*inner ℂ (growingOutputLp (A u)) (growingOutputLp (A v)) := by
    simpa only [sub_zero] using
      KFCausalAveragedOutputRescaling.timeOutputLp_inner 0 t (A u) (A v)
  exact (congrArg₂ (inner ℂ)
    (transfer_energyOutput ε hε h hh hw 0 0 0 0 t u)
    (transfer_energyOutput ε hε h hh hw 0 0 0 0 t v)).trans
      (hp.trans (congrArg₂ (fun x y : ℂ => x+(Real.exp (2*t):ℂ)*y)
        (staticRoot_inner ε hε h hh hb u v).symm (radialRoot_inner ε hε h hh hb u v).symm))

/-- The explicit domain of the sum of the two closed forms. -/
def FormDomain : Submodule ℂ Hilbert := (R).domain ⊓ (S).domain

def toReference (f : FormDomain ε hε h) : V :=
  KFCausalClosedGraphForm.graphVector (D 0)
    ⟨f.val,(free_form_domain ε hε h hh 0 hb f.val).mpr f.property⟩

theorem toReference_embedding (f : FormDomain ε hε h) :
    J (toReference ε hε h hh hb f) = f.val := rfl

theorem toReference_surjective : Function.Surjective (toReference ε hε h hh hb) := by
  intro u
  refine ⟨⟨J u,?_⟩,?_⟩
  · exact ⟨LinearPMap.mem_domain_of_mem_graph (radialRoot_graph ε hε h hh hb u),
      static_domain ε hε h hh hb u⟩
  · exact embedding_injective ε hε h hh hw 0 0 0 0 rfl

/-- This expression uses only the two explicit maximal root operators. -/
def pairing (t : ℝ) (f g : FormDomain ε hε h) : ℂ :=
  inner ℂ (S ⟨f.val,f.property.2⟩) (S ⟨g.val,g.property.2⟩)+
    (Real.exp (2*t):ℂ)*inner ℂ (R ⟨f.val,f.property.1⟩) (R ⟨g.val,g.property.1⟩)

theorem pairing_toReference (t : ℝ) (f g : FormDomain ε hε h) :
    inner ℂ (energyOutput ε hε h hh hw 0 0 0 t (T 0 t (toReference ε hε h hh hb f)))
      (energyOutput ε hε h hh hw 0 0 0 t (T 0 t (toReference ε hε h hh hb g))) =
      pairing ε hε h t f g := by
  rw [transferred_pairing ε hε h hh hb t
    (toReference ε hε h hh hb f) (toReference ε hε h hh hb g)]
  have hs (x : FormDomain ε hε h) : staticRoot ε hε h hh hb (toReference ε hε h hh hb x) =
      S ⟨x.val,x.property.2⟩ :=
    (S).mem_graph_snd_inj' (staticRoot_graph ε hε h hh hb (toReference ε hε h hh hb x))
      ((S).mem_graph ⟨x.val,x.property.2⟩) rfl
  have hr (x : FormDomain ε hε h) : radialRoot ε hε h hh hb (toReference ε hε h hh hb x) =
      R ⟨x.val,x.property.1⟩ :=
    (R).mem_graph_snd_inj' (radialRoot_graph ε hε h hh hb (toReference ε hε h hh hb x))
      ((R).mem_graph ⟨x.val,x.property.1⟩) rfl
  simp only [hs,hr,pairing]

/-- Both directions on the full actual Hamiltonian graph, tested against every
vector in the explicit static/radial intersection domain. -/
theorem hamiltonian_graph_iff (t : ℝ) (f g : Hilbert) :
    (f,g) ∈ (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw 0 0 0 t).graph ↔
      ∃ u : FormDomain ε hε h, u.val = f ∧ ∀ v : FormDomain ε hε h,
        pairing ε hε h t u v = inner ℂ g v.val := by
  let F : FormDomain ε hε h → FormSpace ε hε h hh hw 0 0 0 t :=
    fun u => T 0 t (toReference ε hε h hh hb u)
  have hsur : Function.Surjective F := by
    intro w
    obtain ⟨u,hu⟩ := toReference_surjective ε hε h hh hb (T t 0 w)
    refine ⟨u,?_⟩
    change T 0 t (toReference ε hε h hh hb u) = w
    rw [hu,transfer_inverse]
  exact KFCausalClosedFormUnitaryGraph.graph_iff (D t) (LinearIsometryEquiv.refl ℂ Hilbert)
    (fun u : FormDomain ε hε h => u.val) F hsur
    (fun u => transfer_embedding ε hε h hh hw 0 0 0 0 t (toReference ε hε h hh hb u))
    (pairing ε hε h t) (pairing_toReference ε hε h hh hb t) f g

theorem static_energy_integral (f : FormDomain ε hε h) :
    ‖S ⟨f.val,f.property.2⟩‖^2 = ∫ x,
      KFCausalClockFloorStaticMultiplierForm.symbol ε h x*
        ‖(KFCausalChargeTransverseSplit.dualPhysical f.val) x‖^2 := by
  change ‖KFCausalUnitaryRealMultiplier.realPullback _ _ _ _‖^2 = _
  rw [KFCausalRealMultiplierSelfAdjoint.realPullback_norm_square]
  simp_rw [KFCausalClockFloorStaticMultiplierForm.rootSymbol_square ε hε h]

theorem radial_energy_integral (f : FormDomain ε hε h) :
    ‖R ⟨f.val,f.property.1⟩‖^2 = ∫ x,
      KFCausalClockFloorRadialYosidaSymbol.radial ε h x*
        ‖(KFCausalPhysicalCircleAction.chargeCoordinates f.val) x‖^2 := by
  change ‖KFCausalUnitaryRealMultiplier.realPullback _ _ _ _‖^2 = _
  rw [KFCausalRealMultiplierSelfAdjoint.realPullback_norm_square]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => congrArg (fun r : ℝ =>
    r*‖(KFCausalPhysicalCircleAction.chargeCoordinates f.val) x‖^2)
      (Real.sq_sqrt (KFCausalClockFloorRadialYosidaSymbol.radial_nonnegative ε hε h x)))

/-- The explicit Fourier kinetic and position radial integrals are the actual
completed free energy form, with their exact time coefficient. -/
theorem energy_integrals (t : ℝ) (f : FormDomain ε hε h) :
    (pairing ε hε h t f f).re =
      (∫ x, KFCausalClockFloorStaticMultiplierForm.symbol ε h x*
        ‖(KFCausalChargeTransverseSplit.dualPhysical f.val) x‖^2)+
      Real.exp (2*t)*(∫ x, KFCausalClockFloorRadialYosidaSymbol.radial ε h x*
        ‖(KFCausalPhysicalCircleAction.chargeCoordinates f.val) x‖^2) := by
  simp only [pairing,inner_self_eq_norm_sq_to_K]
  change (((‖S ⟨f.val,f.property.2⟩‖:ℂ)^2+
    (Real.exp (2*t):ℂ)*(‖R ⟨f.val,f.property.1⟩‖:ℂ)^2)).re = _
  rw [← Complex.ofReal_pow,← Complex.ofReal_pow,← Complex.ofReal_mul,
    ← Complex.ofReal_add,Complex.ofReal_re,
    static_energy_integral ε hε h f,radial_energy_integral ε hε h f]

#print axioms staticRoot_graph
#print axioms staticRoot_norm
#print axioms radialRoot_graph
#print axioms radialRoot_norm
#print axioms transferred_pairing
#print axioms toReference_surjective
#print axioms pairing_toReference
#print axioms hamiltonian_graph_iff
#print axioms energy_integrals
end
end UnifiedTheory.Audit.KFCausalClockFloorFreeHamiltonianFormSum
