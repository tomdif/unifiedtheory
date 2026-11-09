/- The Hamiltonian represented by the completed ORIGINAL static energy
output equals the maximal sigma multiplier. Its form domain and operator
are identified through actual graph/variational identities, not stipulated.
No full interacting H/G domain decomposition is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticOutputClosure
import UnifiedTheory.Audit.KFCausalClockFloorStaticOperator

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticHamiltonian
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorStaticRootSource (rootData RootForm)
open KFCausalClockFloorStaticOutputClosure
open KFCausalClockFloorStaticMultiplierForm (rootOperator symbol)

private theorem selfadjoint_eq_of_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A B : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hle : A ≤ B) : A = B := by
  have hBB : B.IsFormalAdjoint B := by
    have hF := LinearPMap.adjoint_isFormalAdjoint hB.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hB] at hF
  have hAB : A.IsFormalAdjoint B := by
    intro f g
    have he : A f = B ⟨f,hle.1 f.property⟩ := hle.2 rfl
    rw [he]
    exact hBB ⟨f,hle.1 f.property⟩ g
  have hrev := hAB.le_adjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hrev
  exact le_antisymm hle hrev

private theorem root_form_pairing (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (f : (KFCausalClockFloorStaticOperator.operator ε hε h).domain) (v : RootForm ε hε h) :
    inner ℂ (rootOperator ε hε h ⟨(f:Hilbert),KFCausalClockFloorStaticOperator.root_domain ε hε h f⟩)
      (KFCausalClosedGraphForm.energyOutput (rootData ε hε h) v) =
      inner ℂ (KFCausalClockFloorStaticOperator.operator ε hε h f)
        (KFCausalClosedGraphForm.embedding (rootData ε hε h) v) := by
  let x : (rootOperator ε hε h).domain :=
    ⟨KFCausalClosedGraphForm.embedding (rootData ε hε h) v,
      LinearPMap.mem_domain_of_mem_graph v.property⟩
  have hx : rootOperator ε hε h x = KFCausalClosedGraphForm.energyOutput (rootData ε hε h) v :=
    (rootOperator ε hε h).mem_graph_snd_inj' ((rootOperator ε hε h).mem_graph x) v.property rfl
  have hp := KFCausalClockFloorStaticOperator.root_pairing ε hε h f x
  have hc := (inner_conj_symm _ _).symm.trans ((congrArg star hp).trans (inner_conj_symm _ _))
  simpa only [hx] using hc

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ t : ℝ)

def formData : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace where
  operator := KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hb m g κ t
  closed := operator_closed ε hε h hh hb m g κ t
  dense := operator_dense ε hε h hh hb m g κ t

local notation "D" => formData ε hε h hh hb m g κ t
abbrev StaticForm := KFCausalClosedGraphForm.FormSpace D

def rootLift (u : RootForm ε hε h) : StaticForm ε hε h hh hb m g κ t :=
  ⟨WithLp.toLp 2 (KFCausalClosedGraphForm.embedding (rootData ε hε h) u,
      extension ε hε h hh hb m g κ t u),root_form_graph ε hε h hh hb m g κ t u⟩

theorem rootLift_embedding (u : RootForm ε hε h) :
    KFCausalClosedGraphForm.embedding D (rootLift ε hε h hh hb m g κ t u) =
      KFCausalClosedGraphForm.embedding (rootData ε hε h) u := rfl

theorem rootLift_output (u : RootForm ε hε h) :
    KFCausalClosedGraphForm.energyOutput D (rootLift ε hε h hh hb m g κ t u) =
      extension ε hε h hh hb m g κ t u := rfl

theorem rootLift_surjective : Function.Surjective (rootLift ε hε h hh hb m g κ t) := by
  intro w
  have hw := w.property
  change WithLp.ofLp w.val ∈ (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hb m g κ t).graph at hw
  rw [operator_graph,initialGraph_closure] at hw
  obtain ⟨u,hu⟩ := hw
  refine ⟨u,?_⟩
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  exact hu

def hamiltonian : Hilbert →ₗ.[ℂ] Hilbert := KFCausalClosedGraphForm.hamiltonian D

theorem hamiltonian_eq_operator : hamiltonian ε hε h hh hb m g κ t =
    KFCausalClockFloorStaticOperator.operator ε hε h := by
  apply Eq.symm
  apply selfadjoint_eq_of_le _ _ (KFCausalClockFloorStaticOperator.selfAdjoint ε hε h)
    (KFCausalClosedGraphForm.hamiltonian_selfAdjoint D)
  apply LinearPMap.le_graph_iff.mp
  rintro ⟨f,z⟩ hfz
  have hf := LinearPMap.mem_domain_of_mem_graph hfz
  let x : (KFCausalClockFloorStaticOperator.operator ε hε h).domain := ⟨f,hf⟩
  have hz : KFCausalClockFloorStaticOperator.operator ε hε h x = z :=
    (KFCausalClockFloorStaticOperator.operator ε hε h).mem_graph_snd_inj'
      ((KFCausalClockFloorStaticOperator.operator ε hε h).mem_graph x) hfz rfl
  let u := KFCausalClosedGraphForm.graphVector (rootData ε hε h)
    ⟨f,KFCausalClockFloorStaticOperator.root_domain ε hε h x⟩
  have hp : ∀ v : StaticForm ε hε h hh hb m g κ t,
      inner ℂ (KFCausalClosedGraphForm.energyOutput D (rootLift ε hε h hh hb m g κ t u))
        (KFCausalClosedGraphForm.energyOutput D v) =
        inner ℂ z (KFCausalClosedGraphForm.embedding D v) := by
    intro v
    obtain ⟨w,rfl⟩ := rootLift_surjective ε hε h hh hb m g κ t v
    change inner ℂ (extension ε hε h hh hb m g κ t u)
      (extension ε hε h hh hb m g κ t w) =
      inner ℂ z (KFCausalClosedGraphForm.embedding (rootData ε hε h) w)
    exact (extension_inner ε hε h hh hb m g κ t u w).trans
      ((root_form_pairing ε hε h x w).trans
        (congrArg (fun y => inner ℂ y (KFCausalClosedGraphForm.embedding (rootData ε hε h) w)) hz))
  obtain ⟨hd,he⟩ := (KFCausalClosedGraphForm.hamiltonian_domain_characterization D
    (rootLift ε hε h hh hb m g κ t u) z).mpr hp
  exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨f,hd⟩,rfl,he⟩

theorem hamiltonian_domain_iff (f : Hilbert) :
    f ∈ (hamiltonian ε hε h hh hb m g κ t).domain ↔
      MemLp (fun x => (symbol ε h x : ℂ)*(KFCausalChargeTransverseSplit.dualPhysical f) x) 2 := by
  rw [hamiltonian_eq_operator]
  exact KFCausalClockFloorStaticOperator.domain_iff ε hε h f

theorem hamiltonian_graph_iff (f z : Hilbert) :
    (f,z) ∈ (hamiltonian ε hε h hh hb m g κ t).graph ↔
      KFCausalChargeTransverseSplit.dualPhysical z =ᵐ[volume]
        fun x => (symbol ε h x : ℂ)*(KFCausalChargeTransverseSplit.dualPhysical f) x := by
  rw [hamiltonian_eq_operator]
  exact KFCausalClockFloorStaticOperator.graph_iff ε hε h f z

#print axioms rootLift_embedding
#print axioms rootLift_output
#print axioms rootLift_surjective
#print axioms hamiltonian_eq_operator
#print axioms hamiltonian_domain_iff
#print axioms hamiltonian_graph_iff
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticHamiltonian
