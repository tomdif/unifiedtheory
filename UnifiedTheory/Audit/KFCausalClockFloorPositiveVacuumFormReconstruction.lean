/- Under the explicit positive-vacuum hypothesis, completed static and
growing outputs reconstruct the ORIGINAL averaged form. This is a form
domain intersection theorem, not a simultaneous operator graph core or
a forward-evolution domain theorem. -/
import UnifiedTheory.Audit.KFCausalLpClosedGraphFormLift
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumJointClosed
import UnifiedTheory.Audit.KFCausalClockFloorStaticOutputClosure
import UnifiedTheory.Audit.KFCausalClockFloorGrowingOutputClosure

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumFormReconstruction
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output jointGraph)
open KFCausalFiniteOutputRescaling (selected selected_apply)
open KFCausalPhysicalEnergyFactors (energyWeight modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorOrbitVacuumGraph (physicalOrbit)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp growingOutputLp)
open KFCausalPhysicalEnergyTransport (staticOutput growingOutput)

private theorem selected_joint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (F : Fin 8 → H →ₗ.[ℂ] H) (w : Fin 8 → ℂ)
    (p : Fin 8 → Prop) [DecidablePred p] (f : H) (z : Output (Fin 8) H)
    (hz : (f,z) ∈ jointGraph F w) :
    (f,selected p z) ∈ jointGraph F (fun i => if p i then w i else 0) := by
  intro i
  by_cases hi : p i
  · simpa only [if_pos hi,selected_apply] using hz i
  · simpa only [if_neg hi,selected_apply,zero_smul] using (F i).graph.zero_mem

private theorem selected_joint_closed {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (F : Fin 8 → H →ₗ.[ℂ] H) (w : Fin 8 → ℂ)
    (p : Fin 8 → Prop) [DecidablePred p] (hF : ∀ i, p i → (F i).IsClosed) :
    IsClosed (jointGraph F (fun i => if p i then w i else 0) :
      Set (H × Output (Fin 8) H)) := by
  have he : (jointGraph F (fun i => if p i then w i else 0) :
      Set (H × Output (Fin 8) H)) =
      {z | ∀ i, if p i then (w i • z.1,z.2 i) ∈ (F i).graph else z.2 i = 0} := by
    ext z
    constructor
    · intro hz i
      by_cases hi : p i
      · simpa only [if_pos hi] using hz i
      · simp only [if_neg hi]
        exact (F i).graph_fst_eq_zero_snd (hz i) (by simp only [if_neg hi,zero_smul])
    · intro hz i
      by_cases hi : p i
      · simpa only [if_pos hi] using hz i
      · have h0 : z.2 i = 0 := by simpa only [if_neg hi] using hz i
        simpa only [if_neg hi,zero_smul,h0] using (F i).graph.zero_mem
  rw [he,Set.setOf_forall]
  apply isClosed_iInter
  intro i
  have hc := (PiLp.continuous_apply 2 (fun _ : Fin 8 => H) i).comp
    (continuous_snd : Continuous (fun z : H × Output (Fin 8) H => z.2))
  by_cases hi : p i
  · simp only [if_pos hi]
    exact (hF i hi).preimage ((continuous_const.smul continuous_fst).prodMk hc)
  · simp only [if_neg hi]
    exact isClosed_eq hc continuous_const

private theorem orbit_relation_closed {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (R : H →L[ℂ] Lp H 2 angleMeasure) (S : Set (H × K)) (hS : IsClosed S) :
    IsClosed {z : H × Lp K 2 angleMeasure | ∀ᵐ θ ∂angleMeasure, (R z.1 θ,z.2 θ) ∈ S} :=
  (KFCausalLpClosedGraphFormLift.ae_relation_closed angleMeasure S hS).preimage
    ((R.continuous.comp continuous_fst).prodMk continuous_snd)

private theorem closure_relation {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (R : H →L[ℂ] Lp H 2 angleMeasure) (S : Set (H × K)) (hS : IsClosed S)
    (I : Submodule ℂ (H × Lp K 2 angleMeasure))
    (hI : ∀ z ∈ I, ∀ᵐ θ ∂angleMeasure, (R z.1 θ,z.2 θ) ∈ S)
    (z : H × Lp K 2 angleMeasure) (hz : z ∈ I.topologicalClosure) :
    ∀ᵐ θ ∂angleMeasure, (R z.1 θ,z.2 θ) ∈ S :=
  closure_minimal hI (orbit_relation_closed R S hS)
    (by simpa only [Submodule.topologicalClosure_coe] using hz)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ : ℝ)
local notation "F" => energyFactor ε hε h modelDirections pointField
local notation "w" => energyWeight m g κ 0
local notation "R" => physicalOrbit h hh
local notation "E" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hb) hh m g κ 0
local notation "S" => KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hb m g κ 0
local notation "B" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hb m g κ

def staticWeight (m g κ : ℝ) (i : Fin 8) : ℂ :=
  if i.val < 3 then energyWeight m g κ 0 i else 0

def growingWeight (m g κ : ℝ) (i : Fin 8) : ℂ :=
  if ¬i.val < 3 then energyWeight m g κ 0 i else 0

theorem averaged_graph_iff (hκ : 0 < κ) (f : Hilbert) (z : EnergyOutputSpace) :
    (f,z) ∈ (E).graph ↔
      ∀ᵐ θ ∂angleMeasure, (R f θ,z θ) ∈ jointGraph F w := by
  rw [KFCausalLpClosedGraphFormLift.averaged_graph_iff]
  apply Filter.eventually_congr
  filter_upwards [] with θ
  exact KFCausalClockFloorPositiveVacuumJointClosed.closedEnergy_graph_iff
    ε hε h modelDirections pointField m g κ 0 hκ _ _

private theorem static_closed :
    IsClosed (jointGraph F (staticWeight m g κ) : Set (Hilbert × Output (Fin 8) Hilbert)) := by
  apply selected_joint_closed
  intro i hi
  fin_cases i
  · exact (KFCausalClockFloorClockHalf.clockHalf_selfAdjoint ε).isClosed
  · exact KFCausalClockFloorAntisymmetricGraph.clockMomentum_closed ε hε h (modelDirections 0)
  · exact KFCausalClockFloorAntisymmetricGraph.clockMomentum_closed ε hε h (modelDirections 1)
  all_goals norm_num at hi

private theorem growing_closed (hκ : 0 < κ) :
    IsClosed (jointGraph F (growingWeight m g κ) : Set (Hilbert × Output (Fin 8) Hilbert)) := by
  apply KFCausalClockFloorPositiveVacuumJointClosed.weighted_jointGraph_closed
  change ((Real.exp 0*Real.sqrt κ : ℝ):ℂ) ≠ 0
  exact Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (Real.exp_ne_zero 0) (Real.sqrt_pos.mpr hκ).ne')

private theorem selected_source (hκ : 0 < κ)
    (p : Fin 8 → Prop) [DecidablePred p] (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (E).graph) :
    ∀ᵐ θ ∂angleMeasure,
      (R f θ,(selected p).compLp z θ) ∈ jointGraph F (fun i => if p i then w i else 0) := by
  filter_upwards [(averaged_graph_iff ε hε h hh hb m g κ hκ f z).mp hz,
    (selected p).coeFn_compLp z] with θ hx he
  rw [he]
  exact selected_joint F w p _ _ hx

theorem static_graph_natural (hκ : 0 < κ) (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (S).graph) :
    ∀ᵐ θ ∂angleMeasure, (R f θ,z θ) ∈ jointGraph F (staticWeight m g κ) := by
  rw [KFCausalClockFloorStaticOutputClosure.operator_graph] at hz
  apply closure_relation (R).toContinuousLinearMap _ (static_closed ε hε h m g κ)
    (KFCausalClockFloorStaticOutputClosure.initialGraph ε hε h hh hb m g κ 0) ?_ (f,z) hz
  rintro z ⟨u,rfl⟩
  exact selected_source ε hε h hh hb m g κ hκ (fun i => i.val < 3) _ _
    (KFCausalAveragedEnergyGraph.averagedOperator_form_graph _ _ _ _
      (KFCausalClosedGraphForm.embedding_injective _) u)

theorem growing_graph_natural (hκ : 0 < κ) (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (B).graph) :
    ∀ᵐ θ ∂angleMeasure, (R f θ,z θ) ∈ jointGraph F (growingWeight m g κ) := by
  rw [KFCausalClockFloorGrowingOutputClosure.operator_graph] at hz
  apply closure_relation (R).toContinuousLinearMap _ (growing_closed ε hε h m g κ hκ)
    (KFCausalClockFloorGrowingOutputClosure.initialGraph ε hε h hh hb m g κ) ?_ (f,z) hz
  rintro z ⟨u,rfl⟩
  exact selected_source ε hε h hh hb m g κ hκ (fun i => ¬i.val < 3) _ _ u.property

theorem reconstruct_graph (hκ : 0 < κ) (f : Hilbert) (s z : EnergyOutputSpace)
    (hs : (f,s) ∈ (S).graph) (hz : (f,z) ∈ (B).graph) :
    (f,s+z) ∈ (E).graph := by
  apply (averaged_graph_iff ε hε h hh hb m g κ hκ f (s+z)).mpr
  filter_upwards [static_graph_natural ε hε h hh hb m g κ hκ f s hs,
    growing_graph_natural ε hε h hh hb m g κ hκ f z hz,Lp.coeFn_add s z] with θ hs hz ha
  rw [ha]
  intro i
  have he : staticWeight m g κ i + growingWeight m g κ i = w i := by
    by_cases hi : i.val < 3 <;> simp only [staticWeight,growingWeight,hi,not_true_eq_false,
      not_false_eq_true,if_true,if_false,zero_add,add_zero]
  simpa only [Prod.mk_add_mk,← add_smul,he] using (F i).graph.add_mem (hs i) (hz i)

theorem form_domain_iff (hκ : 0 < κ) (f : Hilbert) :
    f ∈ (E).domain ↔ f ∈ (S).domain ∧ f ∈ (B).domain := by
  constructor
  · intro hf
    obtain ⟨u,hu⟩ := (KFCausalClockFloorAveragedEnergy.energy_domain
      ε hε h (hamiltonian_bound ε h hb) hh m g κ 0 f).mp hf
    constructor
    · apply (KFCausalClockFloorStaticOutputClosure.operator_domain ε hε h hh hb m g κ 0 f).mpr
      have hr := KFCausalClockFloorStaticMultiplierForm.averaged_root_domain
        ε hε h (hamiltonian_bound ε h hb) hh m g κ 0 u
      rwa [hu] at hr
    · exact LinearPMap.mem_domain_of_mem_graph
        (KFCausalClockFloorGrowingOutputClosure.reference_graph ε hε h hh hb m g κ
          (KFCausalClosedGraphForm.graphVector
            (KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hb m g κ 0) ⟨f,hf⟩))
  · rintro ⟨hs,hz⟩
    exact LinearPMap.mem_domain_of_mem_graph
      (reconstruct_graph ε hε h hh hb m g κ hκ f _ _
        ((S).mem_graph ⟨f,hs⟩) ((B).mem_graph ⟨f,hz⟩))

theorem root_growing_domain_iff (hκ : 0 < κ) (f : Hilbert) :
    f ∈ (E).domain ↔
      f ∈ (KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h).domain ∧
      f ∈ (B).domain := by
  rw [form_domain_iff ε hε h hh hb m g κ hκ f,
    KFCausalClockFloorStaticOutputClosure.operator_domain]

#print axioms averaged_graph_iff
#print axioms static_graph_natural
#print axioms growing_graph_natural
#print axioms reconstruct_graph
#print axioms form_domain_iff
#print axioms root_growing_domain_iff
end
end UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumFormReconstruction
