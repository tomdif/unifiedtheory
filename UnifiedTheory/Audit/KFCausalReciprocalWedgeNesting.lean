/- The actual clock motion gives nested wedges. This geometric statement
is uniform in the number and separation of reciprocal packet widths and
does not divide by a Gram eigenvalue. -/
import UnifiedTheory.Audit.KFCausalReciprocalWedgeVelocity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalReciprocalWedgeNesting
noncomputable section
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalReciprocalWedgeGeometry (first second wedge)
open KFCausalReciprocalWedgeVelocity (drift shrink radius)
open KFCausalNeutralPlaneClockGeometry
open KFCausalNeutralPlaneNormalizedGeometry
open KFCausalClockFloorRelativeShift (scale)

def aperture (r : ℂ) : ℝ := 4*r.re^2*r.im^2/(area r)^2

theorem aperture_nonnegative (r : ℂ) : 0 ≤ aperture r := by unfold aperture; positivity

private theorem nonneg_of_sum_prod (x y : ℝ) (hs : 0 ≤ x+y) (hp : 0 ≤ x*y) :
    0 ≤ x ∧ 0 ≤ y := by
  constructor
  · by_contra hx
    have hx' : x < 0 := lt_of_not_ge hx
    have hy : 0 < y := by linarith
    linarith [mul_neg_of_neg_of_pos hx' hy]
  · by_contra hy
    have hy' : y < 0 := lt_of_not_ge hy
    have hx : 0 < x := by linarith
    linarith [mul_neg_of_pos_of_neg hx hy']

theorem wedge_characterization (α : ℝ) (r z : ℂ) (hα : 0 < α) (hA : 0 < area r)
    (ha : r.re ≠ 0) (hb : r.im ≠ 0) :
    z ∈ wedge α r ↔ 0 ≤ z.re ∧ z.im^2 ≤ aperture r*z.re^2 := by
  have hd : 0 < α*area r := mul_pos hα hA
  have hn : 0 < (2*α*r.re*r.im)^2 := sq_pos_of_ne_zero (by positivity)
  have hs : (first α r z+second α r z)*(α*area r) = 2*z.re := by
    unfold first second
    field_simp
    ring
  have hp : (first α r z*second α r z)*(2*α*r.re*r.im)^2 = aperture r*z.re^2-z.im^2 := by
    unfold first second aperture
    field_simp
    ring
  constructor
  · intro hz
    have hs' := mul_nonneg (add_nonneg hz.1 hz.2) hd.le
    have hp' := mul_nonneg (mul_nonneg hz.1 hz.2) hn.le
    rw [hs] at hs'
    rw [hp] at hp'
    constructor <;> linarith
  · rintro ⟨hz,hq⟩
    have hs' : 0 ≤ first α r z+second α r z := by nlinarith
    have hp' : 0 ≤ first α r z*second α r z := by nlinarith
    exact nonneg_of_sum_prod _ _ hs' hp'

theorem aperture_derivative (r : ℝ → ℂ) (t s : ℝ)
    (hr : HasDerivAt r (velocity (1-t) t (r s)) s)
    (hA : area (r s) ≠ 0) (hD : denominator (1-t) t (r s) ≠ 0) :
    HasDerivAt (fun u => aperture (r u)) (-4*shrink t (r s)*aperture (r s)) s := by
  have hx := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hr
  have hy := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hr
  have hd := (((hx.pow 2).mul (hy.pow 2)).const_mul 4).div
    (((hx.pow 2).sub (hy.pow 2)).pow 2) (pow_ne_zero 2 hA)
  convert hd using 1
  · funext u
    dsimp [aperture,area]
    ring
  · dsimp
    rw [normalized_velocity_re,normalized_velocity_im]
    unfold aperture shrink radius area realNumerator imagNumerator
    unfold area at hA
    field_simp
    ring

theorem actual_aperture_derivative (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (fun u => aperture (scale ε y u))
      (-4*shrink (fraction ε s) (scale ε y s)*aperture (scale ε y s)) s := by
  have ht := fraction_bounds ε s hε
  have hA := scale_square_re_positive ε y s hε hy
  exact aperture_derivative (scale ε y) _ s (actual_normalized_velocity ε y s hε hy) hA.ne'
    (normalized_denominator_positive _ _ ⟨ht.1.le,ht.2.le⟩ hA).ne'

theorem actual_aperture_antitone (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Antitone (fun s => aperture (scale ε y s)) := by
  apply antitone_of_deriv_nonpos (fun s => (actual_aperture_derivative ε y s hε hy).differentiableAt)
  intro s
  rw [(actual_aperture_derivative ε y s hε hy).deriv]
  have ht := fraction_bounds ε s hε
  have hs := KFCausalReciprocalWedgeVelocity.shrink_nonnegative _ _ ⟨ht.1.le,ht.2.le⟩
    (scale_square_re_positive ε y s hε hy)
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hs)
    (aperture_nonnegative _)

theorem actual_wedge_nested (α ε y s t : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) (hst : s ≤ t) :
    wedge α (scale ε y t) ⊆ wedge α (scale ε y s) := by
  intro z hz
  have hc (u : ℝ) := wedge_characterization α (scale ε y u) z hα
    (scale_square_re_positive ε y u hε hy) (scale_re_positive ε y u hε hy).ne'
    (scale_im_ne_zero ε y u hε hy hy0)
  rw [hc t] at hz
  rw [hc s]
  exact ⟨hz.1,hz.2.trans (mul_le_mul_of_nonneg_right
    (actual_aperture_antitone ε y hε hy hst) (sq_nonneg z.re))⟩

#print axioms aperture_nonnegative
#print axioms wedge_characterization
#print axioms aperture_derivative
#print axioms actual_aperture_derivative
#print axioms actual_aperture_antitone
#print axioms actual_wedge_nested
end
end UnifiedTheory.Audit.KFCausalReciprocalWedgeNesting
