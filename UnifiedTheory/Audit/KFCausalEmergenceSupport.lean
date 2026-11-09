/-
  Support obstruction and a removable lapse compactness obstruction.
  The harmonic-law stochastic suppliers and the full metric variation
  are analytic in EMERGENCE_SUPPORT_AND_GAUGE_COMPACTNESS.md.
  These results do not construct a spacetime-selecting microscopic law.
-/
import UnifiedTheory.Audit.KFCausalContinuumEinstein
import Mathlib.MeasureTheory.Measure.WithDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalEmergenceSupport
noncomputable section
open scoped BigOperators MeasureTheory ENNReal
open Filter Topology MeasureTheory
open KFCausalContinuumEinstein

/-- Actual cross-pair counting; the reconstruction must supply the inclusion. -/
theorem cross_pair_count {X : Type*}
    (A B : Finset X) (I : Finset (X × X)) (h : A ×ˢ B ⊆ I) :
    A.card * B.card ≤ I.card := by
  simpa using Finset.card_le_card h

/-- Positive limiting cross-set densities contradict a vanishing pair density. -/
theorem positive_density_excludes_collapse (u v missing : ℕ → ℝ) (p q : ℝ)
    (hu : Tendsto u atTop (𝓝 p)) (hv : Tendsto v atTop (𝓝 q))
    (hm : Tendsto missing atTop (𝓝 0)) (hp : 0 < p) (hq : 0 < q)
    (hcount : ∀ n, u n * v n ≤ missing n) : False := by
  have h : p * q ≤ 0 := le_of_tendsto_of_tendsto' (hu.mul hv) hm hcount
  exact (not_le_of_gt (mul_pos hp hq)) h

/-- Absolute continuity cannot move mass outside an almost-sure collapse event. -/
theorem dominated_geometry_null {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) (C G : Set X) (hcollapse : P Cᶜ = 0)
    (hgeometry : G ⊆ Cᶜ) (hdominated : Q ≪ P) : Q G = 0 :=
  hdominated (measure_mono_null hgeometry hcollapse)

theorem positive_geometry_not_dominated {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) (C G : Set X) (hcollapse : P Cᶜ = 0)
    (hgeometry : G ⊆ Cᶜ) (hpositive : Q G ≠ 0) : ¬Q ≪ P := by
  intro h
  exact hpositive (dominated_geometry_null P Q C G hcollapse hgeometry h)

/-- Includes normalized integrable Gibbs weights; even an arbitrary density
cannot charge the excluded event. Finite-stage singular limits remain possible. -/
theorem density_tilt_geometry_null {X : Type*} [MeasurableSpace X]
    (P : Measure X) (C G : Set X) (w : X → ℝ≥0∞)
    (hcollapse : P Cᶜ = 0) (hgeometry : G ⊆ Cᶜ) :
    P.withDensity w G = 0 :=
  dominated_geometry_null P (P.withDensity w) C G hcollapse hgeometry
    (withDensity_absolutelyContinuous P w)

/-- The one-step barrier used to improve the bad-maximum probability to O(n^-2).
The stochastic recurrence and initial bound are supplied separately. -/
theorem inverse_square_barrier (c A B n : ℝ) (hn : 0 < n) (hB : 0 ≤ B)
    (hA : A ≤ c * B / 2) (hlarge : 4 ≤ c * n) :
    (1 - c) * (B / n ^ 2) + A / n ^ 2 ≤ B / (n + 1) ^ 2 := by
  have hnp : 0 < n + 1 := by linarith
  have hgeom : (1 - c / 2) * (n + 1) ^ 2 ≤ n ^ 2 := by
    have hc : 0 ≤ c := by nlinarith
    have hc2 : 4 * n ≤ c * n ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hlarge hn.le]
    nlinarith
  have hstep : (1 - c) * B + A ≤ (1 - c / 2) * B := by nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos hnp)).mpr
  have he : ((1 - c) * (B / n ^ 2) + A / n ^ 2) * (n + 1) ^ 2 =
      (((1 - c) * B + A) * (n + 1) ^ 2) / n ^ 2 := by ring
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  calc
    ((1 - c) * B + A) * (n + 1) ^ 2 ≤
        ((1 - c / 2) * B) * (n + 1) ^ 2 :=
      mul_le_mul_of_nonneg_right hstep (sq_nonneg _)
    _ ≤ B * n ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hgeom hB]

/-- Elementary two-event tilt normalization, with event mass p and target q. -/
theorem event_tilt_normalized (p q : ℝ) (hp : p ≠ 0) (hpc : 1 - p ≠ 0) :
    (q / p) * p + ((1 - q) / (1 - p)) * (1 - p) = 1 := by
  field_simp
  ring

theorem event_tilt_target (p q : ℝ) (hp : p ≠ 0) : (q / p) * p = q := by
  exact div_mul_cancel₀ q hp

/-- Spatially invariant coefficients annihilate every periodic forward variation. -/
theorem invariant_forward_variation {X : Type*} [Fintype X]
    (p : Equiv.Perm X) (a : ℝ) (A h : X → ℝ) (hA : ∀ x, A (p x) = A x) :
    (∑ x, A x * forwardDifference p a h x) = 0 := by
  rw [forward_summation_by_parts]
  have hs : ∀ x, A x = A (p.symm x) := by
    intro x
    simpa using hA (p.symm x)
  have hz : ∀ x, backwardDifference p a A x = 0 := by
    intro x
    unfold backwardDifference
    rw [hs x, sub_self, zero_div]
  simp [hz]

theorem invariant_backward_variation {X : Type*} [Fintype X]
    (p : Equiv.Perm X) (a : ℝ) (A h : X → ℝ) (hA : ∀ x, A (p x) = A x) :
    (∑ x, A x * backwardDifference p a h x) = 0 := by
  rw [backward_summation_by_parts]
  simp [forwardDifference, hA]

def properTime (k c t : ℝ) : ℝ := t + c / k * Real.sin (k * t)

theorem proper_time_derivative (k c t : ℝ) (hk : k ≠ 0) :
    HasDerivAt (properTime k c) (1 + c * Real.cos (k * t)) t := by
  have h := (hasDerivAt_id t).add
    ((((hasDerivAt_id t).const_mul k).sin).const_mul (c / k))
  convert h using 1
  dsimp [properTime]
  field_simp

theorem proper_time_positive (k c t : ℝ) (hc : |c| < 1) :
    0 < 1 + c * Real.cos (k * t) := by
  have hb : |c * Real.cos (k * t)| ≤ |c| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg c) (Real.abs_cos_le_one _)
  have hl := (abs_le.mp hb).1
  linarith

theorem proper_time_uniform_error (k c t : ℝ) :
    |properTime k c t - t| ≤ |c| / |k| := by
  simp only [properTime, add_sub_cancel_left, abs_mul, abs_div]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)

/-- The time component of the pullback of Minkowski under dτ=L dt. -/
theorem lapse_pullback (L dt : ℝ) : -(L * dt) ^ 2 = -(L ^ 2) * dt ^ 2 := by
  ring

/-- Adjacent alternating lapse metrics force a divergent coordinate Lipschitz bound. -/
theorem lapse_lipschitz_lower_bound (c a K : ℝ) (hc : 0 ≤ c) (ha : 0 < a)
    (hdata : |(-(1 + c) ^ 2) - (-(1 - c) ^ 2)| ≤ K * a) :
    4 * c / a ≤ K := by
  have he : (-(1 + c) ^ 2) - (-(1 - c) ^ 2) = -(4 * c) := by ring
  rw [he, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 4 * c)] at hdata
  exact (div_le_iff₀ ha).mpr hdata

#print axioms cross_pair_count
#print axioms positive_density_excludes_collapse
#print axioms dominated_geometry_null
#print axioms positive_geometry_not_dominated
#print axioms density_tilt_geometry_null
#print axioms inverse_square_barrier
#print axioms event_tilt_normalized
#print axioms event_tilt_target
#print axioms invariant_forward_variation
#print axioms invariant_backward_variation
#print axioms proper_time_derivative
#print axioms proper_time_positive
#print axioms proper_time_uniform_error
#print axioms lapse_pullback
#print axioms lapse_lipschitz_lower_bound

end
end UnifiedTheory.Audit.KFCausalEmergenceSupport
