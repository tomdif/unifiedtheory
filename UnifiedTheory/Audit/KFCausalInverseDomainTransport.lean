/- Differentiable identifications between domains represented by an
invertible bounded form curve. This transport is not time evolution. -/
import UnifiedTheory.Audit.KFCausalInverseCurve
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalInverseDomainTransport
noncomputable section
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

def transport (P Q : ℝ → R) (s t : ℝ) : R := P t*Q s

omit [NormedAlgebra ℝ R] in
theorem transport_initial (P Q : ℝ → R) (hl : ∀ t, P t*Q t = 1) (s : ℝ) :
    transport P Q s s = 1 := hl s

omit [NormedAlgebra ℝ R] in
theorem transport_intertwines (P Q : ℝ → R) (hr : ∀ t, Q t*P t = 1) (s t : ℝ) :
    Q t*transport P Q s t = Q s := by
  rw [transport,← mul_assoc,hr,one_mul]

omit [NormedAlgebra ℝ R] in
theorem transport_compose (P Q : ℝ → R) (hr : ∀ t, Q t*P t = 1) (s r t : ℝ) :
    transport P Q r t*transport P Q s r = transport P Q s t := by
  simp only [transport]
  calc
    P t*Q r*(P r*Q s) = P t*(Q r*P r)*Q s := by simp only [mul_assoc]
    _ = P t*Q s := by rw [hr,mul_one]

theorem transport_derivative (P Q D : ℝ → R)
    (hd : ∀ t, HasDerivAt P (-(P t*D t*P t)) t) (s t : ℝ) :
    HasDerivAt (transport P Q s) (-(P t*D t*transport P Q s t)) t := by
  convert (hd t).mul_const (Q s) using 1
  simp only [transport,neg_mul,mul_assoc]

theorem transport_reverse_derivative (P Q D : ℝ → R)
    (hd : ∀ t, HasDerivAt Q (D t) t) (s t : ℝ) :
    HasDerivAt (fun r => transport P Q r s) (P s*D t) t :=
  (hd t).const_mul (P s)

omit [NormedAlgebra ℝ R] in
theorem connection_identity (P Q D : ℝ → R) (hr : ∀ t, Q t*P t = 1) (s t : ℝ) :
    transport P Q t s*(-(P t*D t*transport P Q s t)) =
      -(P s*D t*transport P Q s t) := by
  simp only [transport,mul_neg]
  congr 1
  calc
    P s*Q t*(P t*D t*(P t*Q s)) = P s*(Q t*P t)*D t*(P t*Q s) := by simp only [mul_assoc]
    _ = P s*D t*(P t*Q s) := by rw [hr,mul_one]

omit [NormedAlgebra ℝ R] in
theorem inverse_connection_identity (P Q D : ℝ → R) (hr : ∀ t, Q t*P t = 1)
    (s t : ℝ) :
    transport P Q s t*(P s*D t*transport P Q s t) =
      -(-(P t*D t*transport P Q s t)) := by
  simp only [neg_neg,transport]
  calc
    P t*Q s*(P s*D t*(P t*Q s)) = P t*(Q s*P s)*D t*(P t*Q s) := by
      simp only [mul_assoc]
    _ = P t*D t*(P t*Q s) := by rw [hr,mul_one]

#print axioms inverse_connection_identity
#print axioms transport_initial
#print axioms transport_intertwines
#print axioms transport_compose
#print axioms transport_derivative
#print axioms transport_reverse_derivative
#print axioms connection_identity
end
end UnifiedTheory.Audit.KFCausalInverseDomainTransport
