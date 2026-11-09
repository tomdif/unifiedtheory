/-
  Algebraic ingredients for weak charts about arbitrary flat holonomies.
  The seam geometry and overlap spectral/locality estimates are analytic
  suppliers, documented in TORON_WEAK_CHART_EXTENSION.md, not assumed closed
  by these finite algebra and quantitative implication results.
-/
import UnifiedTheory.Audit.KFCausalCompactHolonomy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalToronLocality
noncomputable section
open scoped BigOperators

section RingIdentities
variable {R : Type*} [Ring R]

/-- The difference of two inverse kernels inserts their operator difference. -/
theorem resolvent_difference (A B RA RB : R)
    (hA : RA * A = 1) (hB : B * RB = 1) :
    RA - RB = RA * (B - A) * RB := by
  rw [mul_sub, sub_mul, mul_assoc RA B, hB, mul_one, hA, one_mul]

/-- The even resolvent numerator leaves only the one- and three-Clifford
terms after taking the spin trace. X is the scalar imaginary spectral part. -/
theorem even_resolvent_numerator (X H V K : R) :
    (X + H) * V * (X + K) + (-X + H) * V * (-X + K) =
      H * V * K + H * V * K + (X * V * X + X * V * X) := by
  noncomm_ring

end RingIdentities

/-- A sawtooth coordinate difference 1-L*k moves the uniform phase to a cut. -/
theorem uniform_potential_to_seam (θ L k : ℝ) (hL : L ≠ 0) :
    θ / L - θ / L * (1 - L * k) = θ * k := by
  field_simp
  ring

/-- A closed chain reaches the distant seam and returns. The fixed number
of edge insertions accounts for the distance not spent in resolvents. -/
theorem seam_chain_distance (L d outgoing incoming insertions r : ℝ)
    (hd : L / 2 - 1 ≤ d) (ho : d ≤ outgoing) (hi : d ≤ incoming)
    (hr : outgoing + incoming - insertions ≤ r) :
    L - 2 - insertions ≤ r := by linarith

theorem seam_exponential_bound (C α r L m : ℝ)
    (hC : 0 ≤ C) (hα : 0 ≤ α) (hr : L - 2 - m ≤ r) :
    C * Real.exp (-α * r) ≤
      (C * Real.exp (α * (2 + m))) * Real.exp (-α * L) := by
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  nlinarith

section ChargeCancellation
variable {I : Type*} [Fintype I]

/-- Cubic cancellation removes the common reference, leaving only the
holonomy-dependent difference. It does not set that difference to zero. -/
theorem subtract_common_reference (w f : I → ℝ) (b : ℝ)
    (hw : ∑ i, w i = 0) :
    (∑ i, w i * f i) = ∑ i, w i * (f i - b) := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, zero_mul, sub_zero]

theorem cancelled_family_bound (w f : I → ℝ) (b ε : ℝ)
    (hw : ∑ i, w i = 0) (hf : ∀ i, |f i - b| ≤ ε) :
    |∑ i, w i * f i| ≤ (∑ i, |w i|) * ε := by
  rw [subtract_common_reference w f b hw]
  calc
    _ ≤ ∑ i, |w i * (f i - b)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| * ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The descent only needs a volume-small base coefficient, not exact zero. -/
theorem small_base_transport (a d : I → ℝ) (g g₀ ε δ : ℝ)
    (hg : g = g₀ + ∑ i, a i * d i) (hbase : |g₀| ≤ ε)
    (hd : ∀ i, |d i| ≤ δ) :
    |g| ≤ ε + (∑ i, |a i|) * δ := by
  rw [hg]
  calc
    _ ≤ |g₀| + |∑ i, a i * d i| := abs_add_le _ _
    _ ≤ ε + (∑ i, |a i * d i|) :=
      add_le_add hbase (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ε + (∑ i, |a i| * δ) := by
      refine add_le_add le_rfl ?_
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hd i) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

end ChargeCancellation

section ReferenceConnection
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Varying the flat reference contributes without the radial t weight. -/
theorem radial_tangent_split (F : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (a b e : V) (t : ℝ) :
    F a (b + t • e) = F a b + t * F a e := by simp

end ReferenceConnection

#print axioms resolvent_difference
#print axioms even_resolvent_numerator
#print axioms uniform_potential_to_seam
#print axioms seam_chain_distance
#print axioms seam_exponential_bound
#print axioms subtract_common_reference
#print axioms cancelled_family_bound
#print axioms small_base_transport
#print axioms radial_tangent_split

end
end UnifiedTheory.Audit.KFCausalToronLocality
