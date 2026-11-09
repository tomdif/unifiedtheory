/- Quadratic-form order under a unitary implies the reverse order for
a positive symmetric bounded inverse. The inverse is supplied with its
actual equation; no spectral calculus or commutativity is assumed. -/
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalUnitaryInverseOrder
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem variational_bound (A R : H →L[ℂ] H)
    (hs : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y))
    (hp : ∀ x, 0 ≤ (inner ℂ x (A x)).re) (he : ∀ x, A (R x) = x)
    (f u : H) : 2*(inner ℂ f u).re-(inner ℂ u (A u)).re ≤ (inner ℂ f (R f)).re := by
  have hh := hp (u-R f)
  have hc : inner ℂ (R f) (A u) = inner ℂ f u := by rw [← hs,he]
  simp only [map_sub,inner_sub_left,inner_sub_right,he,hc,Complex.sub_re] at hh
  have h1 := inner_re_symm (𝕜 := ℂ) u f
  have h2 := inner_re_symm (𝕜 := ℂ) (R f) f
  change (inner ℂ u f).re = (inner ℂ f u).re at h1
  change (inner ℂ (R f) f).re = (inner ℂ f (R f)).re at h2
  linarith

theorem inverse_unitary_order (A R : H →L[ℂ] H)
    (hs : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y))
    (hp : ∀ x, 0 ≤ (inner ℂ x (A x)).re) (he : ∀ x, A (R x) = x)
    (U : H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, (inner ℂ x (A x)).re ≤ (inner ℂ (U x) (A (U x))).re)
    (f : H) : (inner ℂ (U f) (R (U f))).re ≤ (inner ℂ f (R f)).re := by
  let u := U.symm (R (U f))
  have hu : U u = R (U f) := U.apply_symm_apply _
  have hi : inner ℂ (U f) (R (U f)) = inner ℂ f u := by
    rw [← hu,U.inner_map_map]
  have hq : (inner ℂ u (A u)).re ≤ (inner ℂ f u).re := by
    have hb := hU u
    have hr : (inner ℂ (R (U f)) (U f)).re = (inner ℂ (U f) (R (U f))).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    rw [hu,he,hr,hi] at hb
    exact hb
  have hv := variational_bound A R hs hp he f u
  rw [hi]
  linarith

#print axioms variational_bound
#print axioms inverse_unitary_order
end
end UnifiedTheory.Audit.KFCausalUnitaryInverseOrder
