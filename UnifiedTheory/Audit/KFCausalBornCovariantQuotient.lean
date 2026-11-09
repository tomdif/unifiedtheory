/-
  Causality and the metric on grouped transition amplitudes.

  Grouping m identical precursor amplitudes gives A=m*a. The quadratic
  weight inherited from the precursor space is |A|^2/m, not |A|^2.
  These are finite kinematic identities, not completion of a GUT or GR.
-/

import UnifiedTheory.Audit.KFCausalSetTransitionEdges
import UnifiedTheory.Audit.KFCausalBornMicroscopicSelection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornCovariantQuotient
noncomputable section
open scoped BigOperators
open KFCausalSetSequentialGrowth KFCausalSetTransitionEdges

section Quotient
variable {ι : Type*} [Fintype ι]

def groupedAmplitude (m : ι → ℕ) (a : ι → ℂ) (i : ι) : ℂ := (m i : ℂ) * a i

def quotientBornMass (m : ι → ℕ) (a : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (groupedAmplitude m a i) / m i

theorem quotientBornMass_eq (m : ι → ℕ) (a : ι → ℂ) :
    quotientBornMass m a = ∑ i, (m i : ℝ) * Complex.normSq (a i) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [groupedAmplitude, map_mul, Complex.normSq_natCast]
  by_cases hm : m i = 0
  · simp [hm]
  · have hmR : (m i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    field_simp

/-- The flat norm counts each identical amplitude once too often for every
additional precursor in a fiber. The exact excess isolates the problem. -/
theorem flatBorn_excess_identity (m : ι → ℕ) (a : ι → ℂ) :
    (∑ i, Complex.normSq (groupedAmplitude m a i)) - quotientBornMass m a =
      ∑ i, (m i : ℝ) * (m i - 1) * Complex.normSq (a i) := by
  rw [quotientBornMass_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [groupedAmplitude, map_mul, Complex.normSq_natCast]
  ring

theorem flatBorn_strictly_larger (m : ι → ℕ) (a : ι → ℂ)
    (hdup : ∃ i, 2 ≤ m i ∧ a i ≠ 0) :
    quotientBornMass m a < ∑ i, Complex.normSq (groupedAmplitude m a i) := by
  rw [quotientBornMass_eq]
  apply Finset.sum_lt_sum
  · intro i _
    simp only [groupedAmplitude, map_mul, Complex.normSq_natCast]
    have hm : (m i : ℝ) ≤ (m i : ℝ) * m i := by
      exact_mod_cast (Nat.le_mul_self (m i))
    exact mul_le_mul_of_nonneg_right hm (Complex.normSq_nonneg _)
  · obtain ⟨i, hi, hai⟩ := hdup
    refine ⟨i, Finset.mem_univ i, ?_⟩
    simp only [groupedAmplitude, map_mul, Complex.normSq_natCast]
    have hm : (2 : ℝ) ≤ m i := by exact_mod_cast hi
    have ha := Complex.normSq_pos.mpr hai
    have hmc : (m i : ℝ) < (m i : ℝ) * m i := by nlinarith
    exact mul_lt_mul_of_pos_right hmc ha

/-- On each nonempty fiber, norm preservation uniquely fixes the diagonal
coefficient of the grouped amplitude to the inverse multiplicity. -/
theorem inverse_multiplicity_unique (m : ℕ) (hm : 0 < m) (d : ℝ)
    (hisometry : ∀ z : ℂ, d * Complex.normSq ((m : ℂ) * z) =
      (m : ℝ) * Complex.normSq z) : d = 1 / m := by
  have h := hisometry 1
  simp only [mul_one, Complex.normSq_natCast, map_one] at h
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  apply (eq_div_iff hmR).mpr
  apply (mul_right_cancel₀ hmR)
  nlinarith

/-- Refinement multiplies the history multiplicity by the outgoing link
multiplicity. The inherited quadratic norm is then preserved at each row. -/
theorem quotient_history_norm_step (m : ι → ℕ) (a : ι → ℂ)
    (M : ℕ) (z : ℂ) (hrow : quotientBornMass m a = 1) :
    (∑ i, Complex.normSq (groupedAmplitude m a i * z) / ((M : ℝ) * m i)) =
      Complex.normSq z / M := by
  calc
    _ = (Complex.normSq z / M) * quotientBornMass m a := by
      rw [quotientBornMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [map_mul, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hrow, mul_one]

theorem quotient_history_coherent_step (m : ι → ℕ) (a : ι → ℂ) (z : ℂ)
    (hrow : ∑ i, groupedAmplitude m a i = 1) :
    (∑ i, groupedAmplitude m a i * z) = z := by
  rw [← Finset.sum_mul, hrow, one_mul]
end Quotient

/-- This uses the repository's actual precursor fibers and invariant link
multiplicity, rather than introducing a separate abstract multiplicity. -/
theorem causal_quotientBornMass_eq_precursor_mass {n : ℕ}
    (parent : CardinalCausalOrder n)
    (a : UnlabeledCardinalCausalOrder (n + 1) → ℂ) :
    quotientBornMass (causalTransitionMultiplicity (Quotient.mk _ parent)) a =
      ∑ past : CausalPastSet parent, Complex.normSq (a (causalTransitionTarget parent past)) := by
  rw [quotientBornMass_eq]
  calc
    _ = ∑ child, ∑ _past : LabeledCausalTransitionFiber parent child,
        Complex.normSq (a child) := by
      apply Finset.sum_congr rfl
      intro child _
      simp [causalTransitionMultiplicity_mk, labeledCausalTransitionMultiplicity, nsmul_eq_mul]
    _ = _ := Fintype.sum_fiberwise' (g := causalTransitionTarget parent)
      (f := fun child => Complex.normSq (a child))

theorem causal_grouping_preserves_coherent_sum {n : ℕ}
    (parent : CardinalCausalOrder n)
    (a : UnlabeledCardinalCausalOrder (n + 1) → ℂ) :
    (∑ child, groupedAmplitude (causalTransitionMultiplicity (Quotient.mk _ parent)) a child) =
      ∑ past : CausalPastSet parent, a (causalTransitionTarget parent past) :=
  rideoutSorkin_multiplicity_weighted_sum parent a

/-- The rank-two obstruction is independent of an insertion reference or
particular score. Equal empty-cut and singleton-cut masses in a chain and
antichain contradict Bell ratios and full support. The two antichain slots
are related by an automorphism; their common probability is b1. -/
theorem parent_independent_cuts_Bell_obstruction
    (c0 c1 b0 b1 e0 e1 : ℝ) (he0 : 0 < e0) (hb1 : 0 < b1)
    (hempty : c0 = b0) (hsingle : c1 = 2 * b1)
    (hchain : c1 * e0 = c0 * e1) (hanti : b1 * e0 = b0 * e1) : False := by
  rw [hempty, hsingle] at hchain
  nlinarith [mul_pos hb1 he0]

section Percolation

def bondAmplitude (n : ℕ) (a b : ℂ) (choices : Fin n → Bool) : ℂ :=
  ∏ i, if choices i then a else b

/-- Coherent normalization of independent proposed-bond amplitudes. -/
theorem bondAmplitude_coherent (n : ℕ) (a b : ℂ) (h : a + b = 1) :
    ∑ choices, bondAmplitude n a b choices = 1 := by
  unfold bondAmplitude
  rw [← Fintype.prod_sum (fun (_ : Fin n) (choice : Bool) => if choice then a else b)]
  simp [h]

/-- Born normalization is a separate equation and is compatible with the
coherent one, for example a=(1+i)/2 and b=(1-i)/2. -/
theorem bondAmplitude_born (n : ℕ) (a b : ℂ)
    (h : Complex.normSq a + Complex.normSq b = 1) :
    ∑ choices, Complex.normSq (bondAmplitude n a b choices) = 1 := by
  simp only [bondAmplitude, map_prod, apply_ite]
  rw [← Fintype.prod_sum
    (fun (_ : Fin n) (choice : Bool) => if choice then Complex.normSq a else Complex.normSq b)]
  simp [h]

def precursorAmplitude (a b : ℂ) (maximal missing : ℕ) : ℂ := a ^ maximal * b ^ missing

theorem precursorAmplitude_born (a b : ℂ) (maximal missing : ℕ) :
    Complex.normSq (precursorAmplitude a b maximal missing) =
      Complex.normSq a ^ maximal * Complex.normSq b ^ missing := by
  simp [precursorAmplitude, map_mul, map_pow]

/-- A common spectator factor cancels from the division-free complex Bell
equation. Actual deletion preserves m and adds the same missing count. -/
theorem precursorAmplitude_Bell (a b : ℂ) (m1 m2 u1 u2 spectators : ℕ) :
    precursorAmplitude a b m1 (u1 + spectators) * precursorAmplitude a b m2 u2 =
      precursorAmplitude a b m2 (u2 + spectators) * precursorAmplitude a b m1 u1 := by
  simp only [precursorAmplitude, pow_add]
  ring

/-- In the percolation ansatz, rank-running coefficients cannot retain the
singleton-versus-empty Bell ratio unless the coefficient is constant. -/
theorem percolation_Bell_forces_constant (a b a0 b0 : ℂ)
    (h : a + b = 1) (h0 : a0 + b0 = 1) (hBell : a * b0 = b * a0) : a = a0 := by
  linear_combination a0 * h - a * h0 + hBell

theorem precursor_path_product {ι : Type*} [Fintype ι]
    (a b : ℂ) (m u : ι → ℕ) :
    (∏ i, precursorAmplitude a b (m i) (u i)) =
      a ^ (∑ i, m i) * b ^ (∑ i, u i) := by
  simp [precursorAmplitude, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
end Percolation

#print axioms quotientBornMass_eq
#print axioms flatBorn_strictly_larger
#print axioms inverse_multiplicity_unique
#print axioms quotient_history_norm_step
#print axioms causal_quotientBornMass_eq_precursor_mass
#print axioms parent_independent_cuts_Bell_obstruction
#print axioms bondAmplitude_coherent
#print axioms bondAmplitude_born
#print axioms precursorAmplitude_Bell
#print axioms percolation_Bell_forces_constant
#print axioms precursor_path_product

end
end UnifiedTheory.Audit.KFCausalBornCovariantQuotient
