/-
  Finite support for seed growth, metric collapse, and a gated neutral probe.
  Graph surgery, neighborhood recognition, and propagator path counting
  remain analytic/executable suppliers; no Einstein or full-model claim.
-/
import UnifiedTheory.Audit.KFCausalNeutralPatch
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPatchGrowth
noncomputable section
open scoped BigOperators Matrix
open Filter Topology

/-- The cubic lattice has 4r²+2 vertices in its positive-radius shell. -/
theorem cubic_ball_polynomial (r : ℕ) :
    3 * (1 + ∑ i ∈ Finset.range r, (4 * (i + 1) ^ 2 + 2)) =
      4 * r ^ 3 + 6 * r ^ 2 + 8 * r + 3 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ]
    nlinarith

/-- The constructed cell/tree route gives an explicit normalized bound. -/
theorem normalized_route_bound (diameter height side cells : ℝ)
    (hh : 0 ≤ height) (hs : 3 ≤ side) (hc : 0 < cells)
    (hroute : diameter ≤ (2 * height + 1) * (3 * side + 3) + 2 * height) :
    diameter / (cells * side) ≤ (9 * height + 4) / cells := by
  have hspos : 0 < side := by linarith
  have hp : 0 ≤ height * (3 * side - 8) :=
    mul_nonneg hh (by linarith)
  have hd : diameter ≤ (9 * height + 4) * side := by nlinarith
  calc
    _ ≤ ((9 * height + 4) * side) / (cells * side) :=
      div_le_div_of_nonneg_right hd (mul_pos hc hspos).le
    _ = _ := by field_simp

/-- The growing-neighborhood counterexample still collapses in diameter. -/
theorem explicit_diameter_envelope :
    Tendsto (fun h : ℕ => (27 * (h : ℝ) + 4) / 2 ^ h) atTop (𝓝 0) := by
  have h1 : Tendsto (fun h : ℕ => (h : ℝ) / 2 ^ h) atTop (𝓝 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : 1 < (2 : ℝ))
  have h0 : Tendsto (fun h : ℕ => (1 : ℝ) / 2 ^ h) atTop (𝓝 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : 1 < (2 : ℝ))
  have heq : (fun h : ℕ => (27 * (h : ℝ) + 4) / 2 ^ h) =
      (fun h : ℕ => 27 * ((h : ℝ) / 2 ^ h) + 4 * ((1 : ℝ) / 2 ^ h)) := by
    funext h
    ring
  rw [heq]
  simpa using (h1.const_mul 27).add (h0.const_mul 4)

theorem diameter_collapse (diameter : ℕ → ℝ) (hn : ∀ h, 0 ≤ diameter h)
    (hb : ∀ h, diameter h ≤ (27 * (h : ℝ) + 4) / 2 ^ h) :
    Tendsto diameter atTop (𝓝 0) :=
  squeeze_zero hn hb explicit_diameter_envelope

/-- A uniform cubic volume upper bound enforces a nonzero diameter scale. -/
theorem normalized_volume_bound (scale diameter C : ℝ) (hs : 0 < scale)
    (hvolume : scale ^ 3 ≤ C * diameter ^ 3) :
    1 ≤ C * (diameter / scale) ^ 3 := by
  have h : 1 ≤ C * diameter ^ 3 / scale ^ 3 :=
    (le_div_iff₀ (pow_pos hs 3)).mpr (by simpa using hvolume)
  simpa only [div_pow, mul_div_assoc] using h

theorem collapse_excludes_uniform_volume (diameter : ℕ → ℝ) (C : ℝ)
    (hd : Tendsto diameter atTop (𝓝 0))
    (hv : ∀ h, 1 ≤ C * diameter h ^ 3) : False := by
  have hlim : Tendsto (fun h => C * diameter h ^ 3) atTop (𝓝 0) := by
    simpa using (hd.pow 3).const_mul C
  have h : (1 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto'
    (tendsto_const_nhds (x := (1 : ℝ))) hlim hv
  norm_num at h

/-- The unchanged neighborhoods supply zero errors on the protected roots. -/
theorem local_observable_sum_bound {X : Type*} [Fintype X]
    (value error : X → ℝ) (reference : ℝ)
    (he : ∀ x, |value x - reference| ≤ error x) :
    |∑ x, (value x - reference)| ≤ ∑ x, error x := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun x _ => he x))

/-- A zero gate at either endpoint deletes that hopping matrix element. -/
theorem gate_removes_edge {X : Type*} [Fintype X] [DecidableEq X]
    (gate : X → ℂ) (A : Matrix X X ℂ) (i j : X)
    (hg : gate i = 0 ∨ gate j = 0) :
    (Matrix.diagonal gate * A * Matrix.diagonal gate) i j = 0 := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases hg with h | h <;> simp [h]

theorem gate_preserves_self_adjoint {X : Type*} [Fintype X]
    (D A : Matrix X X ℂ) (hD : Dᴴ = D) (hA : Aᴴ = A) :
    (D * A * D)ᴴ = D * A * D := by
  simp only [Matrix.conjTranspose_mul, hD, hA, Matrix.mul_assoc]

/-- The ninth-order walk and exponential remainder supply these bounds. -/
theorem soft_transmission_lower_bound (amplitude leading remainder : ℝ)
    (hl : 0 ≤ leading) (ht : remainder ≤ leading / 5)
    (ha : leading - remainder ≤ amplitude) : leading / 2 ≤ amplitude := by
  linarith

#print axioms cubic_ball_polynomial
#print axioms normalized_route_bound
#print axioms explicit_diameter_envelope
#print axioms diameter_collapse
#print axioms normalized_volume_bound
#print axioms collapse_excludes_uniform_volume
#print axioms local_observable_sum_bound
#print axioms gate_removes_edge
#print axioms gate_preserves_self_adjoint
#print axioms soft_transmission_lower_bound

end
end UnifiedTheory.Audit.KFCausalPatchGrowth
