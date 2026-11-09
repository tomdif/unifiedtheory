/- A form-preserving physical test converts the bounded resolvent
commutator into the original form commutator at the regularized state. -/
import UnifiedTheory.Audit.KFCausalFormResolventCommutator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace UnifiedTheory.Audit.KFCausalFormResolventTestPairing
noncomputable section
open scoped ComplexConjugate
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem pairing (J : V →L[ℂ] H) (Q : V →L[ℂ] V) (A : H →L[ℂ] V)
    (R D Dstar : H →L[ℂ] H) (F Fstar : V →L[ℂ] V) (a : ℝ)
    (hR : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y))
    (hD : ∀ x y, inner ℂ (Dstar x) y = inner ℂ x (D y))
    (hF : ∀ z, J (F z) = D (J z)) (hFstar : ∀ z, J (Fstar z) = Dstar (J z))
    (hA : ∀ f, J (A f) = R f)
    (hv : ∀ f z, inner ℂ (A f) (Q z) = (a:ℂ)*inner ℂ (f-R f) (J z)) (f : H) :
    inner ℂ (A f) (Q (F (A f)))-conj (inner ℂ (A f) (Q (Fstar (A f)))) =
      (a:ℂ)*inner ℂ f (D (R f)-R (D f)) := by
  rw [hv,hv,hF,hFstar,hA,map_mul,Complex.conj_ofReal,inner_conj_symm]
  simp only [inner_sub_left,inner_sub_right,hD,hR,map_sub]
  ring

#print axioms pairing
end
end UnifiedTheory.Audit.KFCausalFormResolventTestPairing
