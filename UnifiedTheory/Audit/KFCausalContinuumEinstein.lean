/-
  Free-overlap error bounds and the variational bridge for a chosen
  classical metric lattice action. The actual spectral, metric, and
  quadrature suppliers are analytic in CONTINUUM_EINSTEIN_BRIDGE.md.
  No emergence of geometry or existence of smooth critical limits is assumed proved.
-/
import UnifiedTheory.Audit.KFCausalUniformReferenceLocality
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalContinuumEinstein
noncomputable section
open scoped BigOperators
open Filter Topology

/-- Combines the actual scalar and Clifford-vector remainder estimates. -/
theorem overlap_remainder_polynomial (u : ℝ) (hu : 0 ≤ u) (h1 : u ≤ 1) :
    u ^ 2 / 2 + u ^ 4 / 8 + u ^ 3 / 6 + u ^ 5 / 8 ≤ u ^ 2 := by
  have h3 : u ^ 3 ≤ u ^ 2 := pow_le_pow_of_le_one hu h1 (by norm_num)
  have h4 : u ^ 4 ≤ u ^ 2 := pow_le_pow_of_le_one hu h1 (by norm_num)
  have h5 : u ^ 5 ≤ u ^ 2 := pow_le_pow_of_le_one hu h1 (by norm_num)
  nlinarith [sq_nonneg u]

/-- Dividing the dimensionless overlap error by the lattice spacing. -/
theorem overlap_scaled_error (a p error : ℝ) (ha : 0 < a)
    (he : error ≤ (a * p) ^ 2) : error / a ≤ a * p ^ 2 := by
  apply (div_le_iff₀ ha).mpr
  nlinarith

/-- The inverse-metric variation follows from differentiating the inverse identity. -/
theorem inverse_variation {R : Type*} [Ring R] (g gi h dgi : R)
    (hinv : gi * g = 1) (hproduct : h * gi + g * dgi = 0) :
    dgi = -(gi * h * gi) := by
  have he := congrArg (fun x => gi * x) hproduct
  dsimp at he
  rw [mul_add, ← mul_assoc gi g, hinv, one_mul, mul_zero] at he
  have he' : gi * h * gi + dgi = 0 := by simpa only [mul_assoc] using he
  exact eq_neg_of_add_eq_zero_right he'

section DiscreteVariation
variable {X M : Type*} [Fintype X] [Fintype M]

def centralDifference (p : Equiv.Perm X) (a : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  (f (p x) - f (p.symm x)) / (2 * a)

def forwardDifference (p : Equiv.Perm X) (a : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  (f (p x) - f x) / a

def backwardDifference (p : Equiv.Perm X) (a : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  (f x - f (p.symm x)) / a

omit [Fintype M] in
theorem shift_sum (p : Equiv.Perm X) (A B : X → ℝ) :
    (∑ x, A x * B (p x)) = ∑ x, A (p.symm x) * B x := by
  simpa using (Equiv.sum_comp p (fun x => A (p.symm x) * B x))

omit [Fintype M] in
/-- The forward stencil has the negative backward stencil as its adjoint. -/
theorem forward_summation_by_parts (p : Equiv.Perm X) (a : ℝ) (A B : X → ℝ) :
    (∑ x, A x * forwardDifference p a B x) =
      -(∑ x, backwardDifference p a A x * B x) := by
  calc
    _ = ((∑ x, A x * B (p x)) - (∑ x, A x * B x)) / a := by
      simp only [forwardDifference, ← mul_div_assoc, mul_sub, ← Finset.sum_div,
        Finset.sum_sub_distrib]
    _ = ((∑ x, A (p.symm x) * B x) - (∑ x, A x * B x)) / a := by
      rw [shift_sum p A B]
    _ = _ := by
      simp only [backwardDifference, div_mul_eq_mul_div, sub_mul, ← Finset.sum_div,
        Finset.sum_sub_distrib]
      ring

omit [Fintype M] in
theorem backward_summation_by_parts (p : Equiv.Perm X) (a : ℝ) (A B : X → ℝ) :
    (∑ x, A x * backwardDifference p a B x) =
      -(∑ x, forwardDifference p a A x * B x) := by
  have he := forward_summation_by_parts p a B A
  have hh : (∑ x, backwardDifference p a B x * A x) =
      -(∑ x, B x * forwardDifference p a A x) := by linarith
  simpa only [mul_comm] using hh

omit [Fintype M] in
/-- Exact summation by parts for the actual centered periodic stencil. -/
theorem central_summation_by_parts (p : Equiv.Perm X) (a : ℝ) (A B : X → ℝ) :
    (∑ x, A x * centralDifference p a B x) =
      -(∑ x, centralDifference p a A x * B x) := by
  calc
    _ = ((∑ x, A x * B (p x)) - (∑ x, A x * B (p.symm x))) / (2 * a) := by
      simp only [centralDifference, ← mul_div_assoc, mul_sub, ← Finset.sum_div,
        Finset.sum_sub_distrib]
    _ = ((∑ x, A (p.symm x) * B x) - (∑ x, A (p x) * B x)) / (2 * a) := by
      rw [shift_sum p A B, shift_sum p.symm A B]
      rfl
    _ = _ := by
      simp only [centralDifference, div_mul_eq_mul_div, sub_mul, ← Finset.sum_div,
        Finset.sum_sub_distrib]
      ring

/-- The finite first variation yields an explicit discrete Euler derivative. -/
theorem discrete_euler_identity (p : M → Equiv.Perm X) (a : ℝ)
    (A h : X → ℝ) (B : M → X → ℝ) :
    (∑ x, (A x * h x + ∑ μ, B μ x * centralDifference (p μ) a h x)) =
      ∑ x, (A x - ∑ μ, centralDifference (p μ) a (B μ) x) * h x := by
  rw [Finset.sum_add_distrib,
    Finset.sum_comm (f := fun x μ => B μ x * centralDifference (p μ) a h x)]
  simp_rw [central_summation_by_parts]
  rw [Finset.sum_neg_distrib,
    Finset.sum_comm (f := fun μ x => centralDifference (p μ) a (B μ) x * h x)]
  simp only [sub_mul, Finset.sum_mul, Finset.sum_sub_distrib]
  ring

omit [Fintype M] in
theorem finite_variation_nondegenerate (E : X → ℝ)
    (hE : ∀ h : X → ℝ, ∑ x, E x * h x = 0) : ∀ x, E x = 0 := by
  classical
  intro x
  simpa using hE (fun y => if y = x then 1 else 0)

theorem discrete_stationarity (p : M → Equiv.Perm X) (a : ℝ)
    (A : X → ℝ) (B : M → X → ℝ)
    (hs : ∀ h : X → ℝ,
      ∑ x, (A x * h x + ∑ μ, B μ x * centralDifference (p μ) a h x) = 0) :
    ∀ x, A x - ∑ μ, centralDifference (p μ) a (B μ) x = 0 := by
  apply finite_variation_nondegenerate
  intro h
  rw [← discrete_euler_identity p a A h B]
  exact hs h

end DiscreteVariation

/-- Averaging quadratic actions retains the term lost by averaging stencils. -/
theorem averaged_quadratic_action {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (x y : V) :
    (B (x + y) (x + y) + B (x - y) (x - y)) / 2 = B x x + B y y := by
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  ring

/-- The central stencil cancels the even Taylor term; the analytic C^3
Taylor bounds supplying the two hypotheses are separate. -/
theorem central_taylor_error (a M fp fm f₀ v w : ℝ) (ha : 0 < a)
    (hp : |fp - f₀ - a * v - a ^ 2 * w / 2| ≤ M * a ^ 3 / 6)
    (hm : |fm - f₀ + a * v - a ^ 2 * w / 2| ≤ M * a ^ 3 / 6) :
    |(fp - fm) / (2 * a) - v| ≤ M * a ^ 2 / 6 := by
  have he : (fp - fm) / (2 * a) - v =
      ((fp - f₀ - a * v - a ^ 2 * w / 2) -
       (fm - f₀ + a * v - a ^ 2 * w / 2)) / (2 * a) := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (by positivity : 0 < 2 * a)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * a)).mpr
  have ht := abs_sub_le (fp - f₀ - a * v - a ^ 2 * w / 2) 0
    (fm - f₀ + a * v - a ^ 2 * w / 2)
  simp only [sub_zero, zero_sub, abs_neg] at ht
  nlinarith

/-- Quantitative transfer from a small discrete variation to its continuum one. -/
theorem first_variation_error (discrete continuum consistency residual : ℝ)
    (hc : |discrete - continuum| ≤ consistency) (hr : |discrete| ≤ residual) :
    |continuum| ≤ consistency + residual := by
  have h := abs_sub_le (continuum - discrete) 0 (-discrete)
  simp only [sub_zero, sub_neg_eq_add, sub_add_cancel, zero_add] at h
  rw [abs_sub_comm continuum discrete] at h
  linarith

/-- Consistency plus convergence of fields transfers stationary limits.
The actual O(a^2) consistency and compactness/existence are not assumed proved here. -/
theorem stationary_continuum_limit (a error : ℕ → ℝ) (C variation : ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (he : Tendsto error atTop (𝓝 0))
    (hb : ∀ n, |variation| ≤ C * (a n) ^ 2 + error n) : variation = 0 := by
  have hl : Tendsto (fun n => C * (a n) ^ 2 + error n) atTop (𝓝 0) := by
    simpa using ((ha.pow 2).const_mul C).add he
  have hzero : |variation| ≤ 0 := ge_of_tendsto' hl hb
  exact abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))

/-- The covariant-metric first variation has the physical source sign. -/
theorem einstein_source_from_variation (κ G g T Λ : ℝ) (hκ : κ ≠ 0)
    (hstationary : -(G + Λ * g) / (2 * κ) + T / 2 = 0) :
    G + Λ * g = κ * T := by
  field_simp at hstationary
  nlinarith

section Counterexample

def rippleAction (n x : ℝ) : ℝ := x - Real.sin (n * x) / n

/-- Action values approach x uniformly, even though the origin stays stationary. -/
theorem ripple_uniform_bound (n x : ℝ) (hn : 0 < n) :
    |rippleAction n x - x| ≤ 1 / n := by
  have he : rippleAction n x - x = -(Real.sin (n * x) / n) := by unfold rippleAction; ring
  rw [he, abs_neg, abs_div, abs_of_pos hn]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hn.le

theorem ripple_stationary (n : ℝ) (hn : n ≠ 0) :
    HasDerivAt (rippleAction n) 0 0 := by
  have hd := (hasDerivAt_id (0 : ℝ)).sub
    ((((hasDerivAt_id (0 : ℝ)).const_mul n).sin).div_const n)
  simpa [rippleAction, hn] using hd

/-- The limiting action's derivative at that same point is nonzero. -/
theorem limiting_action_not_stationary : ¬HasDerivAt (fun x : ℝ => x) 0 0 := by
  intro h
  have he := h.unique (hasDerivAt_id (0 : ℝ))
  norm_num at he

theorem ripple_bound_tends_to_zero :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

end Counterexample

#print axioms overlap_remainder_polynomial
#print axioms overlap_scaled_error
#print axioms inverse_variation
#print axioms shift_sum
#print axioms forward_summation_by_parts
#print axioms backward_summation_by_parts
#print axioms central_summation_by_parts
#print axioms discrete_euler_identity
#print axioms finite_variation_nondegenerate
#print axioms discrete_stationarity
#print axioms averaged_quadratic_action
#print axioms central_taylor_error
#print axioms first_variation_error
#print axioms stationary_continuum_limit
#print axioms einstein_source_from_variation
#print axioms ripple_uniform_bound
#print axioms ripple_stationary
#print axioms limiting_action_not_stationary
#print axioms ripple_bound_tends_to_zero

end
end UnifiedTheory.Audit.KFCausalContinuumEinstein
