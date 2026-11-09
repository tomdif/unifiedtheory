/- Finite-rank primitives of Bernstein approximations. The construction
approximates a derivative first, so derivative control is retained. -/
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalBernsteinPrimitive
noncomputable section
open MeasureTheory Set Filter
open scoped Topology unitInterval

def basis (n k : ℕ) (t : ℝ) : ℝ := (bernsteinPolynomial ℝ n k).eval t

theorem basis_continuous (n k : ℕ) : Continuous (basis n k) :=
  (bernsteinPolynomial ℝ n k).continuous

theorem basis_on_unit (n k : ℕ) (t : I) : basis n k t = bernstein n k t := rfl

def primitive (n k : ℕ) (t : ℝ) : ℝ := ∫ u in 0..t, basis n k u

theorem primitive_derivative (n k : ℕ) (t : ℝ) :
    HasDerivAt (primitive n k) (basis n k t) t :=
  ((basis_continuous n k).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem primitive_continuous (n k : ℕ) : Continuous (primitive n k) :=
  continuous_iff_continuousAt.mpr (fun t => (primitive_derivative n k t).continuousAt)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def derivativeApprox (n : ℕ) (g : C(I,E)) (t : ℝ) : E :=
  ∑ k : Fin (n+1), basis n k t • g (bernstein.z k)

def valueApprox (n : ℕ) (v : E) (g : C(I,E)) (t : ℝ) : E :=
  v + ∑ k : Fin (n+1), primitive n k t • g (bernstein.z k)

theorem derivativeApprox_continuous (n : ℕ) (g : C(I,E)) :
    Continuous (derivativeApprox n g) :=
  continuous_finset_sum _ (fun k _ => (basis_continuous n k).smul continuous_const)

theorem valueApprox_derivative (n : ℕ) (v : E) (g : C(I,E)) (t : ℝ) :
    HasDerivAt (valueApprox n v g) (derivativeApprox n g t) t := by
  exact (HasDerivAt.fun_sum (fun (k : Fin (n+1)) _ =>
    (primitive_derivative n k t).smul_const (g (bernstein.z k)))).const_add v

theorem valueApprox_continuous (n : ℕ) (v : E) (g : C(I,E)) :
    Continuous (valueApprox n v g) :=
  continuous_iff_continuousAt.mpr (fun t => (valueApprox_derivative n v g t).continuousAt)

theorem valueApprox_zero (n : ℕ) (v : E) (g : C(I,E)) : valueApprox n v g 0 = v := by
  simp [valueApprox,primitive]

theorem valueApprox_eq_integral [CompleteSpace E] (n : ℕ) (v : E) (g : C(I,E)) (t : ℝ) :
    valueApprox n v g t = v + ∫ u in 0..t, derivativeApprox n g u := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => valueApprox_derivative n v g u)
    ((derivativeApprox_continuous n g).intervalIntegrable 0 t)
  rw [valueApprox_zero] at h
  rw [h]
  abel

theorem derivativeApprox_on_unit (n : ℕ) (g : C(I,E)) (t : I) :
    derivativeApprox n g t = bernsteinApproximation n g t := by
  simp only [derivativeApprox,basis_on_unit,bernsteinApproximation.apply]

#print axioms basis_continuous
#print axioms basis_on_unit
#print axioms primitive_derivative
#print axioms primitive_continuous
#print axioms derivativeApprox_continuous
#print axioms valueApprox_derivative
#print axioms valueApprox_continuous
#print axioms valueApprox_zero
#print axioms valueApprox_eq_integral
#print axioms derivativeApprox_on_unit
end
end UnifiedTheory.Audit.KFCausalBernsteinPrimitive
