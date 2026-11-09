/- The wedge Jacobian and field coefficient have regular logarithmic
slopes. Compactness gives bounds independent of all packet coefficients
and widths, in the smaller strip used for strong Hamiltonian domains. -/
import UnifiedTheory.Audit.KFCausalReciprocalWedgeNesting
import Mathlib.Analysis.Calculus.Deriv.Abs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalReciprocalWedgePrefactor
noncomputable section
open Set
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalReciprocalWedgeVelocity (drift)
open KFCausalNeutralPlaneClockGeometry (velocity denominator)
open KFCausalNeutralPlaneNormalizedGeometry
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalClockFloorRelativeShift (scale)

def signedJacobian (α : ℝ) (r : ℂ) : ℝ := 1/(α^2*area r*r.re*r.im)
def jacobian (α : ℝ) (r : ℂ) : ℝ := |signedJacobian α r|
def cap : ℝ := Real.exp (Real.pi/12)
def region : Set (ℝ × ℂ) := KFCausalNeutralPlaneUniformScore.region ∩ {p | p.2.re ≤ cap}
def fieldScore (t : ℝ) (r : ℂ) : ℝ :=
  -t*r.re*realNumerator t r/(denominator (1-t) t r*fieldSlope r)

theorem cap_lt_three_halves : cap < 3/2 := by
  have hx : 0 < Real.pi/12 := by positivity
  have hx' : Real.pi/12 ≤ 1/3 := by linarith [Real.pi_le_four]
  have he := Real.exp_bound_div_one_sub_of_interval' hx (by linarith)
  have hq : 1/(1-Real.pi/12) ≤ (3:ℝ)/2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1-Real.pi/12)).mpr
    linarith
  exact he.trans_le hq

theorem region_compact : IsCompact region :=
  KFCausalNeutralPlaneUniformScore.region_compact.inter_right
    (isClosed_le (Complex.continuous_re.comp continuous_snd) continuous_const)

theorem region_field_positive (p : ℝ × ℂ) (hp : p ∈ region) : 0 < fieldSlope p.2 := by
  have hb : p.2.re ≤ cap := hp.2
  have hc := cap_lt_three_halves
  unfold fieldSlope
  linarith

theorem actual_mem_region (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/6) :
    (fraction ε s,scale ε y s) ∈ region := by
  have hy' : |y| ≤ Real.pi*ε/3 := by nlinarith [Real.pi_pos]
  refine ⟨KFCausalNeutralPlaneUniformScore.actual_mem_region ε y s hε hy',?_⟩
  change (scale ε y s).re ≤ Real.exp (Real.pi/12)
  apply (Complex.re_le_norm _).trans
  apply (KFCausalClockFloorRelativeShift.scale_bound ε y s hε hy').trans
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ (by positivity : 0 < 2*ε)).mpr
  nlinarith

theorem signedJacobian_derivative (r : ℝ → ℂ) (α t s : ℝ)
    (hr : HasDerivAt r (velocity (1-t) t (r s)) s)
    (hα : α ≠ 0) (hA : area (r s) ≠ 0) (ha : (r s).re ≠ 0) (hb : (r s).im ≠ 0)
    (hD : denominator (1-t) t (r s) ≠ 0) :
    HasDerivAt (fun u => signedJacobian α (r u))
      (2*drift t (r s)*signedJacobian α (r s)) s := by
  have hx := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hr
  have hy := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hr
  have hn : α^2*((r s).re^2-(r s).im^2)*(r s).re*(r s).im ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hα) hA) ha) hb
  have hd := (hasDerivAt_const s (1:ℝ)).div
    (((((hx.pow 2).sub (hy.pow 2)).const_mul (α^2)).mul hx).mul hy) hn
  convert hd using 1
  dsimp
  rw [normalized_velocity_re,normalized_velocity_im]
  unfold signedJacobian drift area realNumerator imagNumerator
  unfold area at hA
  field_simp
  ring

theorem jacobian_derivative (r : ℝ → ℂ) (α t s : ℝ)
    (hr : HasDerivAt r (velocity (1-t) t (r s)) s)
    (hα : α ≠ 0) (hA : area (r s) ≠ 0) (ha : (r s).re ≠ 0) (hb : (r s).im ≠ 0)
    (hD : denominator (1-t) t (r s) ≠ 0) :
    HasDerivAt (fun u => jacobian α (r u)) (2*drift t (r s)*jacobian α (r s)) s := by
  have hd := signedJacobian_derivative r α t s hr hα hA ha hb hD
  have hn : signedJacobian α (r s) ≠ 0 := by unfold signedJacobian; positivity
  rcases lt_or_gt_of_ne hn with hj | hj
  · convert (hasDerivAt_abs_neg hj).comp s hd using 1
    rw [jacobian,abs_of_neg hj]
    ring
  · convert (hasDerivAt_abs_pos hj).comp s hd using 1
    rw [jacobian,abs_of_pos hj]
    ring

theorem fieldSlope_derivative (r : ℝ → ℂ) (t s : ℝ)
    (hr : HasDerivAt r (velocity (1-t) t (r s)) s)
    (hD : denominator (1-t) t (r s) ≠ 0) (hf : fieldSlope (r s) ≠ 0) :
    HasDerivAt (fun u => fieldSlope (r u)) (fieldScore t (r s)*fieldSlope (r s)) s := by
  have hd := ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hr).const_mul 2).const_sub 3
  convert hd using 1
  dsimp
  rw [normalized_velocity_re]
  unfold fieldScore
  field_simp

theorem fieldScore_continuousOn : ContinuousOn (fun p : ℝ × ℂ => fieldScore p.1 p.2) region := by
  intro p hp
  have hA : 0 < area p.2 := lt_of_lt_of_le KFCausalNeutralPlaneUniformScore.areaFloor_positive hp.1.2.2
  have hd := normalized_denominator_positive p.1 p.2 hp.1.1 hA
  have hf := region_field_positive p hp
  apply ContinuousAt.continuousWithinAt
  unfold fieldScore realNumerator denominator fieldSlope
  unfold denominator at hd
  unfold fieldSlope at hf
  fun_prop (disch := positivity)

theorem exists_uniform_scores :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ region, |drift p.1 p.2| ≤ M ∧ |fieldScore p.1 p.2| ≤ M := by
  obtain ⟨D,hD,hd⟩ := KFCausalReciprocalWedgeVelocity.exists_uniform_drift
  obtain ⟨F,hF⟩ := ((region_compact.image_of_continuousOn fieldScore_continuousOn).image continuous_abs).bddAbove
  refine ⟨max D F,le_trans hD (le_max_left _ _),?_⟩
  intro p hp
  exact ⟨(hd p hp.1).trans (le_max_left _ _),
    (hF (mem_image_of_mem _ (mem_image_of_mem _ hp))).trans (le_max_right _ _)⟩

#print axioms cap_lt_three_halves
#print axioms region_compact
#print axioms region_field_positive
#print axioms actual_mem_region
#print axioms signedJacobian_derivative
#print axioms jacobian_derivative
#print axioms fieldSlope_derivative
#print axioms fieldScore_continuousOn
#print axioms exists_uniform_scores
end
end UnifiedTheory.Audit.KFCausalReciprocalWedgePrefactor
