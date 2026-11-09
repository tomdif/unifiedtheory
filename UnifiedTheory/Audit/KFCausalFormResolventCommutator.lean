/- A variational resolvent converts the form commutator of a regularized
bounded observable into a bounded physical resolvent commutator. -/
import UnifiedTheory.Audit.KFCausalMovingSandwichCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 700000

namespace UnifiedTheory.Audit.KFCausalFormResolventCommutator
noncomputable section
open scoped ComplexConjugate
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem pairing (J : V →L[ℂ] H) (Q : V →L[ℂ] V) (A : H →L[ℂ] V)
    (R D : H →L[ℂ] H) (a : ℝ)
    (hQ : ∀ x y, inner ℂ x (Q y) = conj (inner ℂ y (Q x)))
    (hR : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y))
    (hv : ∀ f z, inner ℂ (A f) (Q z) = (a:ℂ)*inner ℂ (f-R f) (J z)) (x : V) :
    inner ℂ x (Q (A (D (R (J x)))))-conj (inner ℂ x (Q (A (D.adjoint (R (J x)))))) =
      (a:ℂ)*inner ℂ (J x) (D (R (J x))-R (D (J x))) := by
  have hl (f : H) : inner ℂ x (Q (A f)) = (a:ℂ)*inner ℂ (J x) (f-R f) := by
    rw [hQ,hv,map_mul,Complex.conj_ofReal,inner_conj_symm]
  have hr (f : H) : conj (inner ℂ x (Q (A f))) = (a:ℂ)*inner ℂ (f-R f) (J x) := by
    simpa only [map_mul,Complex.conj_ofReal,inner_conj_symm] using congrArg conj (hl f)
  rw [hl,hr]
  simp only [inner_sub_right,inner_sub_left,hR,D.adjoint_inner_left]
  ring

#print axioms pairing
end
end UnifiedTheory.Audit.KFCausalFormResolventCommutator
