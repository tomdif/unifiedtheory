/-
  Audit/KFCausalSetPartitionCoefficientStructure.lean

  A COEFFICIENT-POSITIVITY NO-GO

  Better critical condition bounds cannot come from a universal positivity
  claim for the real parent-polynomial coefficients.  The obstruction occurs
  at the first nontrivial parent: for the two-event antichain, the coefficient
  of X^2 is exactly -1, while the constant coefficient is exactly 1.

  This is the finite algebraic shadow of the chiral phase.  The coefficient at
  a fixed ancestor number is a signed count, separated by maximal-count class
  modulo four; destructive interference is present in the coefficients before
  any coupling is evaluated.
-/

import UnifiedTheory.Audit.KFCausalSetRationalCriticalFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetPartitionCoefficientStructure

noncomputable section

open scoped BigOperators
open Polynomial
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetChiralDynamics
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw

/-! ## 1. An explicit precursor chart for the two-antichain -/

def twoAntichainPast (bits : Bool × Bool) :
    CausalPastSet (cardinalCausalAntichain 2) where
  mem := fun i => if i = 0 then bits.1 else bits.2
  downwardClosed := by
    intro x y hx hyx
    have hyx' : y = x := of_decide_eq_true hyx
    subst y
    exact hx

def twoAntichainPastEquiv :
    Bool × Bool ≃ CausalPastSet (cardinalCausalAntichain 2) where
  toFun := twoAntichainPast
  invFun := fun past => (past.mem 0, past.mem 1)
  left_inv := by
    intro bits
    cases bits
    simp [twoAntichainPast]
  right_inv := by
    intro past
    apply CausalPastSet.ext
    funext i
    fin_cases i <;> simp [twoAntichainPast]

/-! ## 2. Exact mixed-sign coefficient obstruction -/

/-- The full two-element precursor has two maximal elements and contributes
the phase i^2=-1 at pair exponent two.  All other precursor contributions to
that coefficient vanish. -/
theorem twoAntichain_realPartitionPolynomial_coeff_two :
    (interactingChiralRealPartitionPolynomial
      (cardinalCausalAntichain 2)).coeff 2 = -1 := by
  unfold interactingChiralRealPartitionPolynomial
  rw [finset_sum_coeff]
  rw [← twoAntichainPastEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  have hConstant (z : ℤ) : (z : ℤ[X]).coeff 2 = 0 := by
    cases z <;> norm_num [Polynomial.coeff_one]
  norm_num [twoAntichainPastEquiv, twoAntichainPast,
    cardinalCausalAntichain, CausalPastSet.ancestorCount,
    CausalPastSet.maximalCount, CausalPastSet.IsMaximal,
    ancestorPairExponent, gaussianIPow, gaussianMulI,
    coeff_C_mul_X_pow, Polynomial.coeff_C, Polynomial.coeff_one,
    hConstant]

theorem twoAntichain_realPartitionPolynomial_has_mixed_signs :
    (interactingChiralRealPartitionPolynomial
        (cardinalCausalAntichain 2)).coeff 0 = 1 ∧
      (interactingChiralRealPartitionPolynomial
        (cardinalCausalAntichain 2)).coeff 2 = -1 := by
  exact ⟨interactingChiralRealPartitionPolynomial_coeff_zero _,
    twoAntichain_realPartitionPolynomial_coeff_two⟩

/-- There can be no all-parent theorem asserting nonnegative real partition
coefficients.  Any improved conditioning argument must use subtler cancellation
structure, the imaginary coordinate, or restricted parent classes. -/
theorem no_universal_realPartition_coefficient_positivity :
    ¬ (∀ (n : ℕ) (parent : CardinalCausalOrder n) (k : ℕ),
      0 ≤ (interactingChiralRealPartitionPolynomial parent).coeff k) := by
  intro hPositive
  have hAtTwo := hPositive 2 (cardinalCausalAntichain 2) 2
  rw [twoAntichain_realPartitionPolynomial_coeff_two] at hAtTwo
  norm_num at hAtTwo

#print axioms twoAntichain_realPartitionPolynomial_coeff_two
#print axioms no_universal_realPartition_coefficient_positivity

end

end UnifiedTheory.Audit.KFCausalSetPartitionCoefficientStructure
