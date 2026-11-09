import UnifiedTheory.Audit.KFCausalConformal4DDiamondMeasure

/-! Actual conformal metric tangent cones, with the time orientation fixed by
the zeroth coordinate. Strict timelikeness excludes zeros of the conformal
factor. The temporal cutoff slab has a derived positive conformal factor. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalConformal4DTimelikeTangents
noncomputable section
open scoped BigOperators
open KFCausalConformal4DDiamondBenchmark
open KFCausalConformal4DBoostedMoments (lorentzSquare)
open KFCausalConformal4DDiamondAffine (future)

def metricSquare (att spatial : ℝ) (p v : Point) : ℝ :=
  ∑ i, ∑ j, metric att spatial p i j * v i * v j

def futureTangent (att spatial : ℝ) (p v : Point) : Prop :=
  0 < v 0 ∧ metricSquare att spatial p v < 0

theorem metric_square (att spatial : ℝ) (p v : Point) :
    metricSquare att spatial p v = omega att spatial p ^ 2 * lorentzSquare v := by
  simp only [metricSquare, metric, eta, sign, Fin.sum_univ_four, lorentzSquare]
  norm_num [Fin.ext_iff]
  ring

theorem future_tangent_implies (att spatial : ℝ) (p v : Point)
    (hv : futureTangent att spatial p v) : future v := by
  refine ⟨hv.1, ?_⟩
  have hn := hv.2
  rw [metric_square] at hn
  by_contra h
  exact (not_lt_of_ge (mul_nonneg (sq_nonneg _) (le_of_not_gt h))) hn

theorem future_tangent_iff (att spatial : ℝ) (p v : Point)
    (hω : omega att spatial p ≠ 0) : futureTangent att spatial p v ↔ future v := by
  refine ⟨future_tangent_implies att spatial p v, ?_⟩
  intro hv
  refine ⟨hv.1, ?_⟩
  rw [metric_square]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hω) hv.2

theorem temporal_omega (c : ℝ) (p : Point) :
    omega (2 * c) 0 p = 1 + c * p 0 ^ 2 := by
  simp only [omega, zero_mul, zero_div, add_zero]
  ring

theorem temporal_omega_lower (c : ℝ) (hc : |c| ≤ 1 / 54) (p : Point)
    (hp : |p 0| ≤ 2) : 25 / 27 ≤ omega (2 * c) 0 p := by
  have hc' := (abs_le.mp hc).1
  have hp' : p 0 ^ 2 ≤ 4 := by nlinarith [sq_abs (p 0), abs_nonneg (p 0)]
  have hmul := mul_le_mul_of_nonneg_right hc' (sq_nonneg (p 0))
  rw [temporal_omega]
  nlinarith

theorem temporal_future_tangent_iff (c : ℝ) (hc : |c| ≤ 1 / 54) (p v : Point)
    (hp : |p 0| ≤ 2) : futureTangent (2 * c) 0 p v ↔ future v := by
  apply future_tangent_iff
  have h := temporal_omega_lower c hc p hp
  linarith

#print axioms metric_square
#print axioms future_tangent_implies
#print axioms future_tangent_iff
#print axioms temporal_omega
#print axioms temporal_omega_lower
#print axioms temporal_future_tangent_iff
end
end UnifiedTheory.Audit.KFCausalConformal4DTimelikeTangents
