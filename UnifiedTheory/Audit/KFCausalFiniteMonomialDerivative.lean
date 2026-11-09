/- Coordinate monomials have an exact lowering derivative under one
affine coordinate translation. The formula includes zero exponents. -/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalFiniteMonomialDerivative
noncomputable section

def monomial (n : Fin 4 → ℕ) (z : Fin 4 → ℂ) : ℂ := ∏ j, (z j)^(n j)
def lower (n : Fin 4 → ℕ) (j : Fin 4) : Fin 4 → ℕ := Function.update n j (n j-1)
def raise (n : Fin 4 → ℕ) (j : Fin 4) : Fin 4 → ℕ := Function.update n j (n j+1)

private theorem split (n : Fin 4 → ℕ) (z : Fin 4 → ℂ) (k : Fin 4) :
    monomial n z=(z k)^(n k)*(∏ j ∈ Finset.univ.erase k, (z j)^(n j)) :=
  (Finset.mul_prod_erase Finset.univ (fun j => (z j)^(n j)) (Finset.mem_univ k)).symm

theorem coordinate_update (n : Fin 4 → ℕ) (z : Fin 4 → ℂ) (k : Fin 4) (u : ℂ) :
    monomial n (Function.update z k u)=u^(n k)*(∏ j ∈ Finset.univ.erase k,(z j)^(n j)) := by
  rw [split n (Function.update z k u) k,Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem exponent_update (n : Fin 4 → ℕ) (z : Fin 4 → ℂ) (k : Fin 4) (m : ℕ) :
    monomial (Function.update n k m) z=(z k)^m*(∏ j ∈ Finset.univ.erase k,(z j)^(n j)) := by
  rw [split (Function.update n k m) z k,Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem raising (n : Fin 4 → ℕ) (z : Fin 4 → ℂ) (k : Fin 4) :
    monomial (raise n k) z=z k*monomial n z := by
  rw [raise,exponent_update,split n z k,pow_succ]
  ring

theorem affine_derivative (n : Fin 4 → ℕ) (z : Fin 4 → ℂ) (k : Fin 4) (a : ℂ) :
    HasDerivAt (fun t : ℝ => monomial n (Function.update z k (z k+a*(t:ℂ))))
      (a*(n k:ℂ)*monomial (lower n k) z) 0 := by
  simp only [coordinate_update,lower,exponent_update]
  have hd := ((((hasDerivAt_id (0:ℝ)).ofReal_comp.const_mul a).const_add (z k)).pow (n k)).mul_const
    (∏ j ∈ Finset.univ.erase k,(z j)^(n j))
  convert hd using 1
  simp only [id_eq,Complex.ofReal_zero,Complex.ofReal_one,mul_zero,add_zero,mul_one]
  ring

#print axioms coordinate_update
#print axioms exponent_update
#print axioms raising
#print axioms affine_derivative
end
end UnifiedTheory.Audit.KFCausalFiniteMonomialDerivative
