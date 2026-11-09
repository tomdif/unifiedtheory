/- A signed pairing for an unbounded operator passes to its bounded
Yosida approximants through the resolvent equation. No invariance of
the operator domain under the bounded observable is required. -/
import UnifiedTheory.Audit.KFCausalYosidaApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalYosidaSignedPairing
noncomputable section
open UnifiedTheory.Audit.KFCausalPositiveResolventBounds
open UnifiedTheory.Audit.KFCausalYosidaApproximation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem signed_pairing (T : H →ₗ.[ℂ] H) (R M : H →L[ℂ] H) (a c : ℝ)
    (hr : Resolves T R a) (hm : ∀ f, (inner ℂ f (M f)).im = 0)
    (hs : ∀ x : T.domain, 0 ≤ c*(inner ℂ (T x) (M x)).im) (f : H) :
    0 ≤ c*(inner ℂ (yosida R a f) (M f)).im := by
  let u := point T R a hr f
  have hv : T u = f-a • (u:H) := point_value T R a hr f
  have hy : yosida R a f = a • T u := by
    rw [hv,smul_sub,yosida_apply]
    rfl
  have hx : f = T u+a • (u:H) := by rw [hv]; abel
  have hM : M f = M (T u)+a • M (u:H) := by
    conv_lhs => rw [hx]
    rw [map_add,ContinuousLinearMap.map_smul_of_tower]
  have he : (inner ℂ (yosida R a f) (M f)).im =
      a^2*(inner ℂ (T u) (M u)).im := by
    rw [hy,hM,inner_add_right,inner_smul_left_eq_smul,inner_smul_left_eq_smul,
      inner_smul_right_eq_smul]
    simp only [Complex.add_im,Complex.real_smul,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,hm]
    ring
  rw [he]
  have hp := mul_nonneg (sq_nonneg a) (hs u)
  nlinarith only [hp]

#print axioms signed_pairing

end
end UnifiedTheory.Audit.KFCausalYosidaSignedPairing
