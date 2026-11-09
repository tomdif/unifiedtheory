/-
  A formal variational-jet calculation for a proposed diagonal metric clock.

  Spatial metric diag(exp(x),exp(y),exp(z)), fields depending on spatial y.
  e = exp(-(x+y+z)/2), f = exp((x-y+z)/2); hence e*f = exp(-y).
  The polynomial proof treats e,f as independent symbols and implements
  their chain rules explicitly. It does not assert a microscopic origin,
  prove the curvature formula, or construct an integrated Poisson algebra.
  The accompanying Python audit derives the curvature and Euler derivatives
  independently from the metric. Boundary integration is a separate step.
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDiagonalClockDynamics
noncomputable section
open MvPolynomial
open scoped BigOperators

/- Jet order: e,f, dx,dy,dz, ddx,ddy,ddz, px,py,pz,
   dpx,dpy,dpz, N,dN,ddN, M,dM,ddM. -/
abbrev P := MvPolynomial (Fin 20) ℝ

def velocity : Fin 20 → P :=
  ![-C (1/2) * X 0 * (X 2+X 3+X 4),
    C (1/2) * X 1 * (X 2-X 3+X 4),
    X 5,X 6,X 7,0,0,0,X 11,X 12,X 13,0,0,0,X 15,X 16,0,X 18,X 19,0]

/-- Spatial chain rule on the jets used here; no third derivatives are used. -/
def spatialD : Derivation ℝ P P := mkDerivation ℝ velocity

@[simp] theorem spatialD_X (j : Fin 20) : spatialD (X j) = velocity j :=
  mkDerivation_X _ _ _

@[simp] theorem spatialD_C (a : ℝ) : spatialD (C a) = 0 := derivation_C _ _

@[simp] theorem spatialD_nat (n : ℕ) : spatialD (n : P) = 0 := by
  rw [← map_natCast C n]
  exact spatialD_C n

@[simp] theorem spatialD_two : spatialD (2 : P) = 0 := spatialD_nat 2

def logPartial (i : Fin 3) (F : P) : P :=
  -C (1/2) * X 0 * pderiv 0 F +
    (if i = 1 then -C (1/2) else C (1/2)) * X 1 * pderiv 1 F

/-- Euler derivative with respect to the i-th logarithmic metric field. -/
def euler (i : Fin 3) (F : P) : P :=
  logPartial i F - spatialD (pderiv (![2,3,4] i) F) +
    spatialD (spatialD (pderiv (![5,6,7] i) F))

def density (a b lam : ℝ) : P :=
  C a * X 0 * (X 8^2+X 9^2+X 10^2-C lam*(X 8+X 9+X 10)^2) +
    C b * X 1 * (X 5+X 7+C (1/2)*(X 2^2+X 4^2+X 2*X 4-X 3*(X 2+X 4)))

/-- Actual canonical variational bracket density, before spatial integration. -/
def clockBracket (a b lam : ℝ) : P :=
  ∑ i : Fin 3,
    (euler i (X 14*density a b lam) * pderiv (![8,9,10] i) (X 17*density a b lam) -
      pderiv (![8,9,10] i) (X 14*density a b lam) * euler i (X 17*density a b lam))

def firstLapseCoefficient (a b lam : ℝ) : P :=
  C a*C b*X 0*X 1 *
    (2*X 2*C lam*(X 8+X 9+X 10)-X 2*(X 9+X 10) -
     2*X 3*C lam*(X 8+X 9+X 10)+X 3*(X 8+X 10) +
     2*X 4*C lam*(X 8+X 9+X 10)-X 4*(X 8+X 9))

def secondLapseCoefficient (a b lam : ℝ) : P :=
  2*C a*C b*X 0*X 1*(2*C lam*(X 8+X 9+X 10)-X 8-X 10)

set_option maxHeartbeats 2000000 in
/-- Derived from Euler and momentum derivatives, not an assumed closure law. -/
theorem clockBracket_expansion (a b lam : ℝ) :
    clockBracket a b lam =
      firstLapseCoefficient a b lam * (X 14*X 18-X 17*X 15) +
        secondLapseCoefficient a b lam * (X 14*X 19-X 17*X 16) := by
  apply MvPolynomial.funext
  intro values
  simp [clockBracket, euler, logPartial, density, firstLapseCoefficient,
    secondLapseCoefficient, Fin.sum_univ_succ,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    velocity]
  ring

/-- Coefficient after the one integration by parts needed for smearing. -/
def bracketCurrent (a b lam : ℝ) : P :=
  firstLapseCoefficient a b lam - spatialD (secondLapseCoefficient a b lam)

def lapseW : P := X 14*X 18-X 17*X 15

theorem spatialD_lapseW : spatialD lapseW = X 14*X 19-X 17*X 16 := by
  simp [lapseW, Derivation.leibniz, smul_eq_mul, velocity]
  ring

/-- Exact local identity exhibiting the boundary term. Removing its integral
    requires periodic fields or appropriate boundary conditions. -/
theorem clockBracket_divergence_identity (a b lam : ℝ) :
    clockBracket a b lam = bracketCurrent a b lam * lapseW +
      spatialD (secondLapseCoefficient a b lam * lapseW) := by
  rw [clockBracket_expansion]
  rw [Derivation.leibniz, spatialD_lapseW]
  simp only [smul_eq_mul, bracketCurrent, lapseW]
  ring

def spatialConstraint : P := X 8*X 2+X 9*X 3+X 10*X 4-2*X 12
def traceAnomaly : P :=
  2*(X 11+X 12+X 13)-(X 2+X 3+X 4)*(X 8+X 9+X 10)

theorem bracketCurrent_identity (a b lam : ℝ) :
    bracketCurrent a b lam = C a*C b*X 0*X 1 *
      (spatialConstraint-(2*C lam-1)*traceAnomaly) := by
  apply MvPolynomial.funext
  intro values
  simp [bracketCurrent, firstLapseCoefficient, secondLapseCoefficient,
    spatialConstraint, traceAnomaly, Derivation.leibniz, smul_eq_mul, velocity]
  ring

/-- The corrected kinetic trace coefficient closes this diagonal normal bracket. -/
theorem corrected_clock_current (a b : ℝ) :
    bracketCurrent a b (1/2) = C a*C b*X 0*X 1*spatialConstraint := by
  rw [bracketCurrent_identity]
  apply MvPolynomial.funext
  intro values
  simp

/-- Flat metric, zero momentum at the point, but a nonzero x-momentum
    derivative along spatial y. The spatial constraint still vanishes. -/
def flatTraceJet (t : ℝ) : Fin 20 → ℝ :=
  ![1,1,0,0,0,0,0,0,0,0,0,t,0,0,0,0,0,0,0,0]

theorem flat_trace_witness (a b lam t : ℝ) :
    eval (flatTraceJet t) (bracketCurrent a b lam) = 2*a*b*(1-2*lam)*t := by
  rw [bracketCurrent_identity]
  simp [flatTraceJet, spatialConstraint, traceAnomaly]
  ring

/-- Nonzero kinetic and curvature couplings force the trace correction
    if the proposed off-shell current is to close for every field jet. -/
theorem clock_current_closes_iff (a b lam : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ values : Fin 20 → ℝ, eval values (bracketCurrent a b lam) =
      a*b*values 0*values 1*eval values spatialConstraint) ↔ lam = 1/2 := by
  constructor
  · intro h
    have hw := h (flatTraceJet 1)
    rw [flat_trace_witness] at hw
    have he : (2*a*b)*(1-2*lam) = 0 := by
      simpa [flatTraceJet, spatialConstraint] using hw
    have hn : 2*a*b ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) ha) hb
    have hz := (mul_eq_zero.mp he).resolve_left hn
    linarith
  · rintro rfl values
    rw [corrected_clock_current]
    simp

theorem positive_kinetic_fails_clock_test (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ (∀ values : Fin 20 → ℝ, eval values (bracketCurrent a b 0) =
      a*b*values 0*values 1*eval values spatialConstraint) := by
  rw [clock_current_closes_iff a b 0 ha hb]
  norm_num

#print axioms clockBracket_expansion
#print axioms clockBracket_divergence_identity
#print axioms bracketCurrent_identity
#print axioms corrected_clock_current
#print axioms clock_current_closes_iff
#print axioms positive_kinetic_fails_clock_test

end
end UnifiedTheory.Audit.KFCausalDiagonalClockDynamics
