/- A completed-form construction for a linear bosonic field perturbation.
The annihilation estimate is an explicit input, not an assumed Hamiltonian.
It yields self-adjointness and the full variational graph for every real
coupling. Applying this to dΓ(H(t)) still requires that energy-form estimate. -/
import UnifiedTheory.Audit.KFCausalRelativeFormPerturbation

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalLinearFieldFormPerturbation
noncomputable section
variable {V X : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable (J A : V →L[ℂ] X) (g : ℝ)

def perturbation : V →L[ℂ] V :=
  (g : ℂ) • (A.adjoint.comp J + J.adjoint.comp A)

theorem perturbation_pairing (u v : V) :
    inner ℂ (perturbation J A g u) v =
      (g : ℂ)*(inner ℂ (J u) (A v) + inner ℂ (A u) (J v)) := by
  change inner ℂ ((g : ℂ) • (A.adjoint (J u) + J.adjoint (A u))) v = _
  rw [inner_smul_left, Complex.conj_ofReal, inner_add_left,
    A.adjoint_inner_left, J.adjoint_inner_left]

theorem perturbation_symmetric : (perturbation J A g).toLinearMap.IsSymmetric := by
  intro u v
  change inner ℂ (perturbation J A g u) v = inner ℂ u (perturbation J A g v)
  rw [perturbation_pairing]
  change _ = inner ℂ u ((g : ℂ) • (A.adjoint (J v) + J.adjoint (A v)))
  rw [inner_smul_right, inner_add_right, A.adjoint_inner_right, J.adjoint_inner_right]
  ring

theorem perturbation_diagonal (u : V) :
    (inner ℂ (perturbation J A g u) u).re = 2*g*(inner ℂ (A u) (J u)).re := by
  rw [perturbation_pairing]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_re]
  have hr : (inner ℂ (J u) (A u)).re = (inner ℂ (A u) (J u)).re :=
    inner_re_symm (𝕜 := ℂ) (J u) (A u)
  rw [hr]
  ring

variable (hA : ∀ u : V, ‖A u‖^2 ≤ ‖u‖^2 - ‖J u‖^2)

include hA in
theorem perturbation_bound (u : V) :
    |(inner ℂ (perturbation J A g u) u).re| ≤
      (1/2 : ℝ)*(‖u‖^2 - ‖J u‖^2) + (2*g^2)*‖J u‖^2 := by
  rw [perturbation_diagonal, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hi : |(inner ℂ (A u) (J u)).re| ≤ ‖A u‖*‖J u‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have hb := mul_le_mul_of_nonneg_left hi (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg g))
  have ha := hA u
  have hy := sq_nonneg (‖A u‖ - 2 * |g| * ‖J u‖)
  rw [← sq_abs g]
  nlinarith

variable (hi : Function.Injective J) (hd : DenseRange J)

def hamiltonian : X →ₗ.[ℂ] X :=
  KFCausalRelativeFormPerturbation.hamiltonian J (perturbation J A g) (2*g^2)
    (1/2) (by norm_num) (by norm_num) (perturbation_bound J A g hA) hi hd
    (perturbation_symmetric J A g)

theorem hamiltonian_selfAdjoint : IsSelfAdjoint (hamiltonian J A g hA hi hd) :=
  KFCausalRelativeFormPerturbation.hamiltonian_selfAdjoint _ _ _ _ _ _ _ _ _ _

theorem variational_graph (u : V) (y : X) :
    (J u,y) ∈ (hamiltonian J A g hA hi hd).graph ↔
      ∀ v : V, inner ℂ u v - inner ℂ (J u) (J v) +
        (g : ℂ)*(inner ℂ (J u) (A v) + inner ℂ (A u) (J v)) = inner ℂ y (J v) := by
  rw [hamiltonian, KFCausalRelativeFormPerturbation.variational_graph]
  simp only [perturbation_pairing]

theorem domain_in_form_range (x : (hamiltonian J A g hA hi hd).domain) :
    ∃ u : V, J u = (x : X) := by
  obtain ⟨y,hy⟩ := x.property
  exact ⟨Ring.inverse (KFCausalRelativeFormPerturbation.shiftedForm J
    (perturbation J A g) (2*g^2)) (J.adjoint y), hy⟩

theorem lower_bound (hc : ∀ u : V, ‖J u‖ ≤ ‖u‖) (u : V) (y : X)
    (hg : (J u,y) ∈ (hamiltonian J A g hA hi hd).graph) :
    -(2*g^2)*‖J u‖^2 ≤ (inner ℂ y (J u)).re :=
  KFCausalRelativeFormPerturbation.form_lower_bound _ _ _ _ _ _ _ _ _ _ hc u y hg

theorem lower_bound_with_floor (δ : ℝ)
    (hδ : ∀ u : V, δ*‖J u‖^2 ≤ ‖u‖^2-‖J u‖^2) (u : V) (y : X)
    (hg : (J u,y) ∈ (hamiltonian J A g hA hi hd).graph) :
    (δ/2-2*g^2)*‖J u‖^2 ≤ (inner ℂ y (J u)).re := by
  have hv := (KFCausalRelativeFormPerturbation.variational_graph J
    (perturbation J A g) (2*g^2) (1/2) (by norm_num) (by norm_num)
    (perturbation_bound J A g hA) hi hd (perturbation_symmetric J A g) u y).mp hg u
  have he := congrArg Complex.re hv
  have h1 : (inner ℂ u u).re = ‖u‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  have h2 : (inner ℂ (J u) (J u)).re = ‖J u‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) (J u)
  simp only [Complex.add_re, Complex.sub_re, h1, h2] at he
  have hb := (abs_le.mp (perturbation_bound J A g hA u)).1
  have hf := hδ u
  nlinarith

end
end UnifiedTheory.Audit.KFCausalLinearFieldFormPerturbation
