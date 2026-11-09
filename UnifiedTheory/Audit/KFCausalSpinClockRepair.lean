/-
  Occupation-dependent repair of the finite-spin clock amplitudes.

  A spin annihilator has amplitude sqrt(n) sqrt(1-(N-1)/R).
  Multiplication on the right by a polynomial in N compensates the
  second factor. The first two corrections have fixed degree and give
  quadratic/cubic errors, respectively. Exact compensation removes
  the amplitude defect, but cannot remove the top occupation boundary.

  The finite sums below are weighted-shift coordinate norm estimates,
  not an all-time clock position estimate. The full six-flavor finite
  matrix evolution is checked separately in spin_clock_repair_audit.py.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSpinClockRepair
noncomputable section
open scoped BigOperators

def firstFactor (x : ℝ) : ℝ := Real.sqrt (1-x) * (1+x/2)
def secondFactor (x : ℝ) : ℝ := Real.sqrt (1-x) * (1+x/2+3*x^2/8)

theorem first_factor_square (x : ℝ) (hx : x ≤ 1) :
    (firstFactor x)^2 = 1-3*x^2/4-x^3/4 := by
  unfold firstFactor
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  ring

theorem second_factor_square (x : ℝ) (hx : x ≤ 1) :
    (secondFactor x)^2 = 1-5*x^3/8-15*x^4/64-9*x^5/64 := by
  unfold secondFactor
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  ring

theorem first_factor_error (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ 1-firstFactor x ∧ 1-firstFactor x ≤ x^2 := by
  have hf : 0 ≤ firstFactor x := by unfold firstFactor; positivity
  have hs := first_factor_square x hx1
  have hx3 : 0 ≤ x^3 := by positivity
  have hupper : firstFactor x ≤ 1 := by nlinarith [sq_nonneg x]
  have hc : x^3 ≤ x^2 := by nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1)]
  constructor
  · linarith
  · nlinarith [mul_nonneg hf (sub_nonneg.mpr hupper)]

theorem second_factor_error (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ 1-secondFactor x ∧ 1-secondFactor x ≤ x^3 := by
  have hf : 0 ≤ secondFactor x := by unfold secondFactor; positivity
  have hs := second_factor_square x hx1
  have hx3 : 0 ≤ x^3 := by positivity
  have hx4 : 0 ≤ x^4 := by positivity
  have hx5 : 0 ≤ x^5 := by positivity
  have hc4 : x^4 ≤ x^3 := by
    nlinarith [mul_nonneg hx3 (sub_nonneg.mpr hx1)]
  have hc5 : x^5 ≤ x^4 := by
    nlinarith [mul_nonneg hx4 (sub_nonneg.mpr hx1)]
  have hupper : secondFactor x ≤ 1 := by nlinarith
  constructor
  · linarith
  · nlinarith [mul_nonneg hf (sub_nonneg.mpr hupper)]

theorem second_factor_improves_first (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ 1-secondFactor x ∧ 1-secondFactor x ≤ 1-firstFactor x := by
  refine ⟨(second_factor_error x hx hx1).1, ?_⟩
  unfold firstFactor secondFactor
  nlinarith [mul_nonneg (Real.sqrt_nonneg (1-x)) (sq_nonneg x)]

/-- The original defect is linear near the dilute limit, whereas the
first and second corrected defects are bounded above by x² and x³. -/
theorem bare_factor_error (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x/2 ≤ 1-Real.sqrt (1-x) ∧ 1-Real.sqrt (1-x) ≤ x := by
  have hs := Real.sq_sqrt (show 0 ≤ 1-x by linarith)
  have hn := Real.sqrt_nonneg (1-x)
  constructor
  · nlinarith [sq_nonneg (1-Real.sqrt (1-x))]
  · nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]

/-- With 1 ≤ N ≤ R, x=(N-1)/R is strictly below one, even at N=R.
The vacuum amplitude vanishes, so it needs no inverse correction. -/
theorem finite_spin_parameter (R N : ℝ) (hR : 0 < R) (hN : 1 ≤ N)
    (hNR : N ≤ R) : 0 ≤ (N-1)/R ∧ (N-1)/R < 1 := by
  constructor
  · exact div_nonneg (by linarith) hR.le
  · exact (div_lt_one hR).mpr (by linarith)

theorem exact_amplitude_compensation (n x : ℝ) (hx : x < 1) :
    (Real.sqrt n * Real.sqrt (1-x)) * (Real.sqrt (1-x))⁻¹ = Real.sqrt n := by
  have hp : 0 < Real.sqrt (1-x) := Real.sqrt_pos.mpr (by linarith)
  field_simp

/-- Per-basis-state error of either corrected annihilator. -/
theorem amplitude_error (n r e : ℝ)
    (hr : 0 ≤ 1-r) (he : 1-r ≤ e) :
    |Real.sqrt n*r-Real.sqrt n| ≤ Real.sqrt n*e := by
  rw [show Real.sqrt n*r-Real.sqrt n = -(Real.sqrt n*(1-r)) by ring,
    abs_neg, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg n) hr)]
  exact mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg n)

/-- Dimension-independent squared norm bound for the annihilation
error, in the occupation basis. Lowering a fixed flavor maps distinct
nonzero input basis states to distinct output basis states. -/
theorem weighted_shift_error {ι : Type*} [Fintype ι]
    (n r : ι → ℝ) (ψ : ι → ℂ) (m e : ℝ)
    (hn : ∀ i, 0 ≤ n i) (hnm : ∀ i, n i ≤ m)
    (hr : ∀ i, 0 ≤ 1-r i) (hre : ∀ i, 1-r i ≤ e) :
    (∑ i, ‖(((Real.sqrt (n i)*r i-Real.sqrt (n i) : ℝ) : ℂ)*ψ i)‖^2) ≤
      m*e^2 * ∑ i, ‖ψ i‖^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have ha := amplitude_error (n i) (r i) e (hr i) (hre i)
  have he : 0 ≤ e := (hr i).trans (hre i)
  have hs := Real.sq_sqrt (hn i)
  calc
    _ ≤ (Real.sqrt (n i)*e)^2 := by
      nlinarith [abs_nonneg (Real.sqrt (n i)*r i-Real.sqrt (n i)),
        mul_nonneg (Real.sqrt_nonneg (n i)) he]
    _ = n i*e^2 := by rw [mul_pow, hs]
    _ ≤ m*e^2 := mul_le_mul_of_nonneg_right (hnm i) (sq_nonneg e)

theorem first_corrected_shift_bound {ι : Type*} [Fintype ι]
    (n x : ι → ℝ) (ψ : ι → ℂ) (m δ : ℝ)
    (hn : ∀ i, 0 ≤ n i) (hnm : ∀ i, n i ≤ m)
    (hx : ∀ i, 0 ≤ x i) (hxδ : ∀ i, x i ≤ δ) (hδ : δ ≤ 1) :
    (∑ i, ‖(((Real.sqrt (n i)*firstFactor (x i)-Real.sqrt (n i) : ℝ) : ℂ)*ψ i)‖^2) ≤
      m*(δ^2)^2 * ∑ i, ‖ψ i‖^2 := by
  apply weighted_shift_error n (fun i => firstFactor (x i)) ψ m (δ^2) hn hnm
  · intro i; exact (first_factor_error _ (hx i) ((hxδ i).trans hδ)).1
  · intro i
    have hb := (first_factor_error _ (hx i) ((hxδ i).trans hδ)).2
    have hd : 0 ≤ δ := (hx i).trans (hxδ i)
    nlinarith [hxδ i, hx i]

theorem second_corrected_shift_bound {ι : Type*} [Fintype ι]
    (n x : ι → ℝ) (ψ : ι → ℂ) (m δ : ℝ)
    (hn : ∀ i, 0 ≤ n i) (hnm : ∀ i, n i ≤ m)
    (hx : ∀ i, 0 ≤ x i) (hxδ : ∀ i, x i ≤ δ) (hδ : δ ≤ 1) :
    (∑ i, ‖(((Real.sqrt (n i)*secondFactor (x i)-Real.sqrt (n i) : ℝ) : ℂ)*ψ i)‖^2) ≤
      m*(δ^3)^2 * ∑ i, ‖ψ i‖^2 := by
  apply weighted_shift_error n (fun i => secondFactor (x i)) ψ m (δ^3) hn hnm
  · intro i; exact (second_factor_error _ (hx i) ((hxδ i).trans hδ)).1
  · intro i
    exact (second_factor_error _ (hx i) ((hxδ i).trans hδ)).2.trans
      (pow_le_pow_left₀ (hx i) (hxδ i) 3)

/-- Missing creation-annihilation loops in the compressed free kinetic
energy: one (n_a+1)/4 contribution per flavor at the top boundary. -/
theorem top_boundary_energy {ι : Type*} [Fintype ι] (n : ι → ℝ) :
    (∑ i, (n i+1)/4) = ((∑ i, n i)+(Fintype.card ι : ℝ))/4 := by
  simp only [add_div, Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

/-- No finite-dimensional repair can give an exact canonical commutator
on every state. The occupation-boundary defect is unavoidable. -/
theorem no_finite_exact_commutator {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B : Matrix ι ι ℂ) : A*B-B*A ≠ 1 := by
  classical
  intro he
  have ht := congrArg Matrix.trace he
  rw [Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self, Matrix.trace_one] at ht
  have hc : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact hc ht.symm

/-- If a defect is confined to the boundary by D = B† D B, its
expectation is controlled by the boundary probability, not its square
root. Establishing that support identity for a concrete Hamiltonian
is a separate obligation (checked for the six-flavor matrices). -/
theorem boundary_expectation_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (B D : E →L[ℂ] E) (hD : D = B.adjoint.comp (D.comp B)) (ψ : E) :
    ‖inner ℂ ψ (D ψ)‖ ≤ ‖D‖ * ‖B ψ‖^2 := by
  have hi : inner ℂ ψ (D ψ) = inner ℂ (B ψ) (D (B ψ)) := by
    conv_lhs => rw [hD]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [hi]
  calc
    _ ≤ ‖B ψ‖ * ‖D (B ψ)‖ := norm_inner_le_norm _ _
    _ ≤ ‖B ψ‖ * (‖D‖ * ‖B ψ‖) := mul_le_mul_of_nonneg_left
      (D.le_opNorm (B ψ)) (norm_nonneg _)
    _ = _ := by ring

#print axioms first_factor_error
#print axioms second_factor_error
#print axioms second_factor_improves_first
#print axioms bare_factor_error
#print axioms finite_spin_parameter
#print axioms exact_amplitude_compensation
#print axioms amplitude_error
#print axioms weighted_shift_error
#print axioms first_corrected_shift_bound
#print axioms second_corrected_shift_bound
#print axioms top_boundary_energy
#print axioms no_finite_exact_commutator
#print axioms boundary_expectation_bound

end
end UnifiedTheory.Audit.KFCausalSpinClockRepair
