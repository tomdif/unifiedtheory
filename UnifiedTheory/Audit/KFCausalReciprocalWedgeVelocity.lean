/- Exact clock transport of the positive-quadrant coordinates. The cross
coefficient is nonpositive, and the neutral exponential decreases at
fixed points inside the wedge. All coefficients extend across Im(r)=0. -/
import UnifiedTheory.Audit.KFCausalReciprocalWedgeGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace UnifiedTheory.Audit.KFCausalReciprocalWedgeVelocity
noncomputable section
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalReciprocalWedgeGeometry (first second wedge)
open KFCausalNeutralPlaneClockGeometry (velocity denominator)
open KFCausalNeutralPlaneNormalizedGeometry

def radius (r : ℂ) : ℝ := r.re^2+r.im^2
def drift (t : ℝ) (r : ℂ) : ℝ :=
  -t/(4*denominator (1-t) t r)*
    (2*(r.re^2*realNumerator t r-r.im^2*imagNumerator t r)/area r+
      realNumerator t r+imagNumerator t r)
def shrink (t : ℝ) (r : ℂ) : ℝ := t*(radius r)^2/(2*denominator (1-t) t r*area r)
def cooling (β t : ℝ) (r : ℂ) : ℝ :=
  4*β*t*r.im^2*radius r/(denominator (1-t) t r*area r)
def neutralExponent (α β : ℝ) (r z : ℂ) : ℝ := 8*β*r.im^2*first α r z

theorem numerator_difference (t : ℝ) (r : ℂ) :
    realNumerator t r-imagNumerator t r = 2*radius r := by
  unfold realNumerator imagNumerator radius
  ring

theorem shrink_nonnegative (t : ℝ) (r : ℂ) (ht : t ∈ Set.Icc 0 1) (hA : 0 < area r) :
    0 ≤ shrink t r := by
  have hd := normalized_denominator_positive t r ht hA
  have ht0 := ht.1
  unfold shrink
  positivity

theorem cooling_nonnegative (β t : ℝ) (r : ℂ) (hβ : 0 ≤ β)
    (ht : t ∈ Set.Icc 0 1) (hA : 0 < area r) : 0 ≤ cooling β t r := by
  have hd := normalized_denominator_positive t r ht hA
  have ht0 := ht.1
  unfold cooling radius
  positivity

theorem first_derivative (r : ℝ → ℂ) (α t s : ℝ) (z : ℂ)
    (hr : HasDerivAt r (velocity (1-t) t (r s)) s)
    (hα : α ≠ 0) (hA : area (r s) ≠ 0) (ha : (r s).re ≠ 0) (hb : (r s).im ≠ 0)
    (hD : denominator (1-t) t (r s) ≠ 0) :
    HasDerivAt (fun u => first α (r u) z)
      (drift t (r s)*first α (r s) z-shrink t (r s)*second α (r s) z) s := by
  have hx := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hr
  have hy := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hr
  have h1 : α*((r s).re^2-(r s).im^2) ≠ 0 := mul_ne_zero hα hA
  have h2 : (2*α)*((r s).re*(r s).im) ≠ 0 := by positivity
  have hd := ((hasDerivAt_const s z.re).div (((hx.pow 2).sub (hy.pow 2)).const_mul α) h1).add
    ((hasDerivAt_const s z.im).div ((hx.mul hy).const_mul (2*α)) h2)
  convert hd using 1
  · funext u
    dsimp [first,area]
    congr 1
    ring
  · dsimp
    rw [normalized_velocity_re,normalized_velocity_im]
    unfold drift shrink first second radius area realNumerator imagNumerator
    unfold area at hA
    field_simp
    ring

theorem second_derivative (r : ℝ → ℂ) (α t s : ℝ) (z : ℂ)
    (hr : HasDerivAt r (velocity (1-t) t (r s)) s)
    (hα : α ≠ 0) (hA : area (r s) ≠ 0) (ha : (r s).re ≠ 0) (hb : (r s).im ≠ 0)
    (hD : denominator (1-t) t (r s) ≠ 0) :
    HasDerivAt (fun u => second α (r u) z)
      (drift t (r s)*second α (r s) z-shrink t (r s)*first α (r s) z) s := by
  have hd := first_derivative r α t s (starRingEnd ℂ z) hr hα hA ha hb hD
  simpa only [first,second,Complex.conj_re,Complex.conj_im,neg_div,neg_neg,
    sub_neg_eq_add,sub_eq_add_neg] using hd

theorem neutralExponent_derivative (r : ℝ → ℂ) (α β t s : ℝ) (z : ℂ)
    (hr : HasDerivAt r (velocity (1-t) t (r s)) s)
    (hα : α ≠ 0) (hA : area (r s) ≠ 0) (ha : (r s).re ≠ 0) (hb : (r s).im ≠ 0)
    (hD : denominator (1-t) t (r s) ≠ 0) :
    HasDerivAt (fun u => neutralExponent α β (r u) z)
      (-cooling β t (r s)*
        ((3*(r s).re^2-(r s).im^2)*first α (r s) z+radius (r s)*second α (r s) z)) s := by
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hr
  have hd := ((hi.pow 2).const_mul (8*β)).mul (first_derivative r α t s z hr hα hA ha hb hD)
  convert hd using 1
  dsimp
  rw [normalized_velocity_im]
  unfold cooling drift shrink radius first second area realNumerator imagNumerator
  unfold area at hA
  field_simp
  ring

theorem coordinate_velocity_upper (α t : ℝ) (r z : ℂ) (ht : t ∈ Set.Icc 0 1)
    (hA : 0 < area r) (hz : z ∈ wedge α r) :
    drift t r*first α r z-shrink t r*second α r z ≤ drift t r*first α r z := by
  exact sub_le_self _ (mul_nonneg (shrink_nonnegative t r ht hA) hz.2)

theorem neutral_velocity_nonpositive (α β t : ℝ) (r z : ℂ) (hβ : 0 ≤ β)
    (ht : t ∈ Set.Icc 0 1) (hA : 0 < area r) (hz : z ∈ wedge α r) :
    -cooling β t r*((3*r.re^2-r.im^2)*first α r z+radius r*second α r z) ≤ 0 := by
  have ha : 0 ≤ 3*r.re^2-r.im^2 := by unfold area at hA; nlinarith [sq_nonneg r.re]
  have hn : 0 ≤ radius r := by unfold radius; positivity
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (cooling_nonnegative β t r hβ ht hA))
    (add_nonneg (mul_nonneg ha hz.1) (mul_nonneg hn hz.2))

theorem drift_continuousOn :
    ContinuousOn (fun p : ℝ × ℂ => drift p.1 p.2) KFCausalNeutralPlaneUniformScore.region := by
  intro p hp
  have hA : 0 < area p.2 := lt_of_lt_of_le KFCausalNeutralPlaneUniformScore.areaFloor_positive hp.2.2
  have hd := normalized_denominator_positive p.1 p.2 hp.1 hA
  apply ContinuousAt.continuousWithinAt
  unfold drift realNumerator imagNumerator denominator area
  unfold denominator at hd
  unfold area at hA
  fun_prop (disch := positivity)

theorem exists_uniform_drift :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ KFCausalNeutralPlaneUniformScore.region, |drift p.1 p.2| ≤ M := by
  obtain ⟨M,hM⟩ := ((KFCausalNeutralPlaneUniformScore.region_compact.image_of_continuousOn
    drift_continuousOn).image continuous_abs).bddAbove
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro p hp
  exact (hM (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hp))).trans (le_max_left _ _)

#print axioms numerator_difference
#print axioms shrink_nonnegative
#print axioms cooling_nonnegative
#print axioms first_derivative
#print axioms second_derivative
#print axioms neutralExponent_derivative
#print axioms coordinate_velocity_upper
#print axioms neutral_velocity_nonpositive
#print axioms drift_continuousOn
#print axioms exists_uniform_drift
end
end UnifiedTheory.Audit.KFCausalReciprocalWedgeVelocity
