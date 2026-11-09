/- Constructive relative form perturbation theorem in a fixed Hilbert form
space. A symmetric form represented there by T, with relative bound a < 1,
produces an actual self-adjoint operator and a full variational graph test.
The field application must still supply its completed energy form and T. -/
import UnifiedTheory.Audit.KFCausalCoerciveFormHamiltonian

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalRelativeFormPerturbation
noncomputable section
open KFCausalCoerciveInverse
variable {V X : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable (J : V →L[ℂ] X) (T : V →L[ℂ] V) (b : ℝ)

def shiftedForm : V →L[ℂ] V := 1 + T + (b : ℂ) • (J.adjoint.comp J)

theorem shiftedForm_pairing (u v : V) :
    inner ℂ (shiftedForm J T b u) v = inner ℂ u v + inner ℂ (T u) v +
      (b : ℂ)*inner ℂ (J u) (J v) := by
  change inner ℂ (u + T u + (b : ℂ) • J.adjoint (J u)) v = _
  rw [inner_add_left, inner_add_left, inner_smul_left, Complex.conj_ofReal,
    J.adjoint_inner_left]

theorem shiftedForm_symmetric (hs : T.toLinearMap.IsSymmetric) :
    (shiftedForm J T b).toLinearMap.IsSymmetric := by
  intro u v
  change inner ℂ (shiftedForm J T b u) v = inner ℂ u (shiftedForm J T b v)
  rw [shiftedForm_pairing]
  change _ = inner ℂ u (v + T v + (b : ℂ) • J.adjoint (J v))
  rw [inner_add_right, inner_add_right, inner_smul_right, J.adjoint_inner_right]
  exact congrArg (fun z : ℂ => inner ℂ u v + z + (b : ℂ)*inner ℂ (J u) (J v)) (hs u v)

theorem shiftedForm_diagonal (u : V) :
    (inner ℂ (shiftedForm J T b u) u).re =
      ‖u‖^2 + (inner ℂ (T u) u).re + b*‖J u‖^2 := by
  have h1 : (inner ℂ u u).re = ‖u‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  have h2 : (inner ℂ (J u) (J u)).re = ‖J u‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) (J u)
  rw [shiftedForm_pairing]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, h1, h2]

variable (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
  (hbound : ∀ u : V, |(inner ℂ (T u) u).re| ≤
    a*(‖u‖^2-‖J u‖^2) + b*‖J u‖^2)

include ha0 hbound in
theorem shiftedForm_coercive (u : V) :
    (1-a)*‖u‖^2 ≤ (inner ℂ (shiftedForm J T b u) u).re := by
  rw [shiftedForm_diagonal]
  have hv := (abs_le.mp (hbound u)).1
  nlinarith [mul_nonneg ha0 (sq_nonneg ‖J u‖)]

def shiftedForm_unit (hs : T.toLinearMap.IsSymmetric) : IsUnit (shiftedForm J T b) :=
  coercive_isUnit _ (1-a) (sub_pos.mpr ha1)
    (shiftedForm_coercive J T b a ha0 hbound) (shiftedForm_symmetric J T b hs)

variable (hi : Function.Injective J) (hd : DenseRange J) (hs : T.toLinearMap.IsSymmetric)

def hamiltonian : X →ₗ.[ℂ] X := KFCausalCoerciveFormHamiltonian.hamiltonian J hi hd
  (shiftedForm J T b) (shiftedForm_unit J T b a ha0 ha1 hbound hs) (b+1)

theorem hamiltonian_selfAdjoint : IsSelfAdjoint (hamiltonian J T b a ha0 ha1 hbound hi hd hs) :=
  KFCausalCoerciveFormHamiltonian.hamiltonian_selfAdjoint J hi hd (shiftedForm J T b)
    (shiftedForm_unit J T b a ha0 ha1 hbound hs) (shiftedForm_symmetric J T b hs) (b+1)

theorem variational_graph (u : V) (y : X) :
    (J u,y) ∈ (hamiltonian J T b a ha0 ha1 hbound hi hd hs).graph ↔
      ∀ v : V, inner ℂ u v - inner ℂ (J u) (J v) + inner ℂ (T u) v = inner ℂ y (J v) := by
  rw [hamiltonian, KFCausalCoerciveFormHamiltonian.variational_graph]
  have he (v : V) : inner ℂ (shiftedForm J T b u) v - ((b+1 : ℝ) : ℂ)*inner ℂ (J u) (J v) =
      inner ℂ u v - inner ℂ (J u) (J v) + inner ℂ (T u) v := by
    rw [shiftedForm_pairing]
    push_cast
    ring
  simp only [he]

theorem form_lower_bound (hc : ∀ u : V, ‖J u‖ ≤ ‖u‖) (u : V) (y : X)
    (hg : (J u,y) ∈ (hamiltonian J T b a ha0 ha1 hbound hi hd hs).graph) :
    -b*‖J u‖^2 ≤ (inner ℂ y (J u)).re := by
  have he := congrArg Complex.re ((variational_graph J T b a ha0 ha1 hbound hi hd hs u y).mp hg u)
  have h1 : (inner ℂ u u).re = ‖u‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  have h2 : (inner ℂ (J u) (J u)).re = ‖J u‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) (J u)
  simp only [Complex.add_re, Complex.sub_re, h1, h2] at he
  have hv := (abs_le.mp (hbound u)).1
  have hq : 0 ≤ ‖u‖^2-‖J u‖^2 := by nlinarith [hc u, norm_nonneg u, norm_nonneg (J u)]
  have hp := mul_nonneg (sub_pos.mpr ha1).le hq
  nlinarith

end
end UnifiedTheory.Audit.KFCausalRelativeFormPerturbation
