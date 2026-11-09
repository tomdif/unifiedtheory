/- Derive the Hermite differential equation from the repository's recurrence.
These are polynomial identities, prior to identifying an unbounded operator. -/
import UnifiedTheory.Audit.KFCausalHermitePolynomials
import Mathlib.Algebra.Polynomial.Derivative

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalHermiteOscillatorPolynomial
noncomputable section
open Polynomial
open KFCausalNeutralHermiteDomain (physicistsHermite multiplier)

theorem ladder_identities (n : ℕ) :
    (physicistsHermite (n+1)).derivative = C (2*((n+1:ℕ):ℂ))*physicistsHermite n ∧
    physicistsHermite (n+1) = C 2*X*physicistsHermite n-(physicistsHermite n).derivative := by
  induction n with
  | zero => simp [physicistsHermite]
  | succ n ih =>
    constructor
    · rw [show n+1+1 = n+2 by omega,KFCausalNeutralHermiteDomain.physicistsHermite_recurrence]
      simp only [derivative_sub,derivative_mul,derivative_C,derivative_X,zero_mul,
        zero_add,mul_one,ih.1]
      have hr := ih.2
      simp only [Nat.cast_add,Nat.cast_one,map_add,map_mul,map_ofNat,map_natCast,map_one] at hr ⊢
      linear_combination -(2*((n:Polynomial ℂ)+1))*hr
    · rw [show n+1+1 = n+2 by omega,KFCausalNeutralHermiteDomain.physicistsHermite_recurrence,ih.1]

theorem derivative_succ (n : ℕ) :
    (physicistsHermite (n+1)).derivative = C (2*((n+1:ℕ):ℂ))*physicistsHermite n :=
  (ladder_identities n).1

theorem raising (n : ℕ) :
    physicistsHermite (n+1) = C 2*X*physicistsHermite n-(physicistsHermite n).derivative :=
  (ladder_identities n).2

/-- The physicists' Hermite differential equation at every degree. -/
theorem hermite_ode (n : ℕ) :
    (physicistsHermite n).derivative.derivative-C 2*X*(physicistsHermite n).derivative+
      C (2*(n:ℂ))*physicistsHermite n = 0 := by
  have he := congrArg Polynomial.derivative (raising n)
  rw [derivative_succ] at he
  simp only [derivative_sub,derivative_mul,derivative_C,derivative_X,zero_mul,
    zero_add,mul_one] at he
  simp only [Nat.cast_add,Nat.cast_one,map_add,map_mul,map_ofNat,map_natCast,map_one] at he ⊢
  linear_combination he

/-- Conjugating `-d²/dx² + 4 a² x²` by `exp(-a x²)` yields this polynomial operator. -/
def oscillator (a : ℂ) (P : Polynomial ℂ) : Polynomial ℂ :=
  -P.derivative.derivative+C (4*a)*X*P.derivative+C (2*a)*P

theorem oscillator_scaled (a k c : ℂ) (hk : k^2 = 2*a) (n : ℕ) :
    oscillator a (C c*(physicistsHermite n).comp (C k*X)) =
      C (2*a*(2*(n:ℂ)+1))*(C c*(physicistsHermite n).comp (C k*X)) := by
  have he := congrArg (fun P : Polynomial ℂ => P.comp (C k*X)) (hermite_ode n)
  simp only [sub_comp,add_comp,mul_comp,C_comp,X_comp,zero_comp] at he
  unfold oscillator
  simp only [derivative_mul,derivative_C,derivative_X,derivative_comp,zero_mul,
    zero_add,mul_one]
  have hkp : (C k)^2 = 2*C a := by
    rw [← map_pow,hk,map_mul,map_ofNat]
  simp only [map_add,map_mul,map_ofNat,map_natCast,map_one] at he ⊢
  linear_combination -C c*(2*C a)*he +
    (-C c*((physicistsHermite n).derivative.derivative.comp (C k*X)))*hkp

/-- Every degree of the existing normalized multiplier has the oscillator eigenvalue. -/
theorem multiplier_eigenvalue (a : ℝ) (ha : 0 < a) (n : ℕ) :
    oscillator (a:ℂ) (multiplier a 0 n) =
      C (2*(a:ℂ)*(2*(n:ℂ)+1))*multiplier a 0 n := by
  have hk : (Real.sqrt (2*a):ℂ)^2 = 2*(a:ℂ) := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt (by positivity)]
    push_cast
    rfl
  simpa only [multiplier,Complex.ofReal_zero,map_zero,sub_zero] using
    oscillator_scaled (a:ℂ) (Real.sqrt (2*a):ℂ)
      ((Real.sqrt ((2:ℝ)^n*n.factorial):ℂ)⁻¹) hk n

#print axioms ladder_identities
#print axioms hermite_ode
#print axioms oscillator_scaled
#print axioms multiplier_eigenvalue
end
end UnifiedTheory.Audit.KFCausalHermiteOscillatorPolynomial
