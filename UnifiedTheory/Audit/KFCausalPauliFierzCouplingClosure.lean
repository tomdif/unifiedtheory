/- The S3-by-boson coupling has a closed, densely defined extension on a
complete Hilbert space. This is the interaction operator by itself; adding
the actual second-quantized energy still requires a form-domain argument. -/
import UnifiedTheory.Audit.KFCausalPauliFierzMatterCore
import UnifiedTheory.Audit.KFCausalBosonicFieldClosure
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalPauliFierzCouplingClosure
noncomputable section
open KFCausalBosonicOccupationSpace KFCausalPauliFierzMatterCore
open KFCausalSeparatedGraphClosure
variable {ι : Type*}

abbrev CoupledHilbert (ι : Type*) := PiLp 2 (fun _ : Group => Fock ι)

def coupledEmbed : CoupledCore ι →ₗ[ℂ] CoupledHilbert ι where
  toFun u := WithLp.toLp 2 (fun r => embed (u r))
  map_add' _ _ := by ext r : 1; exact map_add embed _ _
  map_smul' _ _ := by ext r : 1; exact map_smul embed _ _

theorem coupledEmbed_inner (u v : CoupledCore ι) :
    inner ℂ (coupledEmbed u) (coupledEmbed v) = coupledPairing u v := rfl

theorem coupledEmbed_injective : Function.Injective (coupledEmbed (ι := ι)) := by
  intro u v he
  funext r
  apply embed_injective
  exact congrArg (fun x : CoupledHilbert ι => x r) he

theorem coupled_vacuum_output_nonzero (i : ι) :
    coupledEmbed (coupling i uncoupledVacuum) ≠ 0 := by
  intro he
  apply coupling_vacuum_nonzero i
  exact coupledEmbed_injective (by simpa only [map_zero] using he)

theorem coupledEmbed_dense : DenseRange (coupledEmbed (ι := ι)) := by
  let e := (PiLp.homeomorph 2 (fun _ : Group => Fock ι)).symm
  exact e.surjective.denseRange.comp (DenseRange.piMap (fun _ : Group => core_dense))
    e.continuous

theorem coupledCore_separates (y : CoupledHilbert ι)
    (hy : ∀ u : CoupledCore ι, inner ℂ (coupledEmbed u) y = 0) : y = 0 := by
  have hc : IsClosed {x : CoupledHilbert ι | inner ℂ x y = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have ha : ∀ x : CoupledHilbert ι, inner ℂ x y = 0 := by
    intro x
    exact closure_minimal (by rintro _ ⟨u, rfl⟩; exact hy u) hc (coupledEmbed_dense x)
  exact (inner_self_eq_zero).mp (ha y)

def initialCoupling (i : ι) : CoupledHilbert ι →ₗ.[ℂ] CoupledHilbert ι :=
  initialOperator coupledEmbed (coupledEmbed.comp (coupling i))

def closedCoupling (i : ι) : CoupledHilbert ι →ₗ.[ℂ] CoupledHilbert ι :=
  closedOperator coupledEmbed (coupledEmbed.comp (coupling i))

theorem closedCoupling_graph (i : ι) :
    (closedCoupling i).graph =
      (graphRange coupledEmbed (coupledEmbed.comp (coupling i))).topologicalClosure := by
  apply closedOperator_graph _ _
    (fun u : CoupledCore ι => coupledEmbed (coupling i u)) coupledEmbed coupledCore_separates
  intro v u
  exact (coupling_symmetric i u v).symm

theorem initialCoupling_closable (i : ι) : (initialCoupling i).IsClosable := by
  apply operator_closable _ _
    (fun u : CoupledCore ι => coupledEmbed (coupling i u)) coupledEmbed coupledCore_separates
  intro v u
  exact (coupling_symmetric i u v).symm

theorem closedCoupling_closed (i : ι) : (closedCoupling i).IsClosed := by
  apply operator_closed _ _
    (fun u : CoupledCore ι => coupledEmbed (coupling i u)) coupledEmbed coupledCore_separates
  intro v u
  exact (coupling_symmetric i u v).symm

theorem closedCoupling_extends_core (i : ι) (u : CoupledCore ι) :
    (coupledEmbed u, coupledEmbed (coupling i u)) ∈ (closedCoupling i).graph := by
  rw [closedCoupling_graph]
  apply (graphRange coupledEmbed (coupledEmbed.comp (coupling i))).le_topologicalClosure
  exact ⟨u, rfl⟩

theorem closedCoupling_domain_dense (i : ι) :
    Dense ((closedCoupling i).domain : Set (CoupledHilbert ι)) := by
  apply coupledEmbed_dense.mono
  rintro _ ⟨u, rfl⟩
  obtain ⟨v, hv, _⟩ := (closedCoupling i).mem_graph_iff.mp (closedCoupling_extends_core i u)
  change (v : CoupledHilbert ι) = coupledEmbed u at hv
  simpa only [← hv] using v.property

end
end UnifiedTheory.Audit.KFCausalPauliFierzCouplingClosure
