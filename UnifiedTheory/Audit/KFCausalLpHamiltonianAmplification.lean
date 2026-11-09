/- Self-adjoint amplification of an actual resolvent Hamiltonian to
L2(Omega; X), with the full almost-everywhere operator graph. This supplies
one tensor-factor action without an energy eigenbasis or a particle cutoff.
Summing different factors and restricting to bosonic sectors are later steps. -/
import UnifiedTheory.Audit.KFCausalResolventHamiltonian
import UnifiedTheory.Audit.KFCausalProbabilityL2Mean

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalLpHamiltonianAmplification
noncomputable section
open MeasureTheory KFCausalResolventHamiltonian
variable {Ω X : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
variable (μ : Measure Ω) (R : X →L[ℂ] X) (hi : Function.Injective R)
  (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y))

def resolvent : Lp X 2 μ →L[ℂ] Lp X 2 μ := R.compLpL 2 μ

theorem resolvent_coe (f : Lp X 2 μ) :
    resolvent μ R f =ᵐ[μ] fun x => R (f x) := R.coeFn_compLp f

include hi in
theorem resolvent_injective : Function.Injective (resolvent μ R) :=
  KFCausalProbabilityL2Mean.compLp_injective μ R hi

include hs in
theorem resolvent_symmetric (f g : Lp X 2 μ) :
    inner ℂ (resolvent μ R f) g = inner ℂ f (resolvent μ R g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [resolvent_coe μ R f, resolvent_coe μ R g] with x hf hg
  rw [hf,hg]
  exact hs _ _

include hi hs in
theorem resolvent_dense : DenseRange (resolvent μ R) := by
  have hsym : (resolvent μ R).toLinearMap.IsSymmetric := resolvent_symmetric μ R hs
  change Dense ((resolvent μ R).range : Set (Lp X 2 μ))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  rw [hsym.orthogonal_range, LinearMap.ker_eq_bot.mpr (resolvent_injective μ R hi)]

def hamiltonian : Lp X 2 μ →ₗ.[ℂ] Lp X 2 μ :=
  inverseShift (resolvent μ R) (resolvent_injective μ R hi)

include hs in
theorem hamiltonian_selfAdjoint : IsSelfAdjoint (hamiltonian μ R hi) :=
  inverseShift_selfAdjoint _ _ (resolvent_dense μ R hi hs) (resolvent_symmetric μ R hs)

theorem inverseShift_graph_iff (f g : X) :
    (f,g) ∈ (inverseShift R hi).graph ↔ R (g+f) = f := by
  constructor
  · intro hfg
    obtain ⟨u,hu,hv⟩ := (inverseShift R hi).mem_graph_iff.mp hfg
    simpa only [hu,hv] using inverseShift_resolvent R hi u
  · intro he
    refine (inverseShift R hi).mem_graph_iff.mpr ⟨rangeVector R hi (g+f), he, ?_⟩
    rw [inverseShift_apply_range,he,add_sub_cancel_right]

theorem hamiltonian_graph (f g : Lp X 2 μ) :
    (f,g) ∈ (hamiltonian μ R hi).graph ↔
      ∀ᵐ x ∂μ, (f x,g x) ∈ (inverseShift R hi).graph := by
  rw [hamiltonian, inverseShift_graph_iff]
  simp_rw [inverseShift_graph_iff]
  constructor
  · intro he
    have hae : resolvent μ R (g+f) =ᵐ[μ] f := by rw [he]
    filter_upwards [hae,resolvent_coe μ R (g+f),Lp.coeFn_add g f] with x hx hr ha
    simpa only [ha,Pi.add_apply] using hr.symm.trans hx
  · intro he
    apply Lp.ext
    filter_upwards [he,resolvent_coe μ R (g+f),Lp.coeFn_add g f] with x hx hr ha
    simpa only [ha,Pi.add_apply,hx] using hr

theorem hamiltonian_domain (f : Lp X 2 μ) :
    f ∈ (hamiltonian μ R hi).domain ↔
      ∃ g : Lp X 2 μ, ∀ᵐ x ∂μ, (f x,g x) ∈ (inverseShift R hi).graph := by
  constructor
  · intro hf
    exact ⟨hamiltonian μ R hi ⟨f,hf⟩,
      (hamiltonian_graph μ R hi f _).mp ((hamiltonian μ R hi).mem_graph ⟨f,hf⟩)⟩
  · rintro ⟨g,hg⟩
    exact LinearPMap.mem_domain_of_mem_graph ((hamiltonian_graph μ R hi f g).mpr hg)

end
end UnifiedTheory.Audit.KFCausalLpHamiltonianAmplification
