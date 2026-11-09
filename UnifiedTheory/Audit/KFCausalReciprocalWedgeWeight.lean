/- A uniform one-sided derivative bound for the proposed positive wedge
weight, including its Jacobian, neutral exponential and quartic moment.
The representation of the physical Gram kernel by this weight is a
separate obligation; no matrix response inequality is asserted here. -/
import UnifiedTheory.Audit.KFCausalReciprocalWedgePrefactor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalReciprocalWedgeWeight
noncomputable section
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalReciprocalWedgeGeometry (first second wedge)
open KFCausalReciprocalWedgeVelocity (drift shrink cooling radius neutralExponent)
open KFCausalReciprocalWedgePrefactor (jacobian fieldScore region)
open KFCausalNeutralPlaneClockGeometry (velocity denominator)
open KFCausalNeutralPlaneNormalizedGeometry
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalClockFloorRelativeShift (scale)

def polynomial (c0 c1 c2 T : ℝ) : ℝ := c0+c1*T+c2*T^2
def moment (α η : ℝ) (r z : ℂ) : ℝ := η*(fieldSlope r)^2*first α r z

def momentSlope (α η t : ℝ) (r z : ℂ) : ℝ :=
  (2*fieldScore t r+drift t r)*moment α η r z-
    η*(fieldSlope r)^2*shrink t r*second α r z

def neutralSlope (α β η t : ℝ) (r z : ℂ) : ℝ :=
  η*(-cooling β t r*((3*r.re^2-r.im^2)*first α r z+radius r*second α r z))

def weight (α β η c0 c1 c2 : ℝ) (r z : ℂ) : ℝ :=
  jacobian α r*Real.exp (η*neutralExponent α β r z)*polynomial c0 c1 c2 (moment α η r z)

def weightSlope (α β η c0 c1 c2 t : ℝ) (r z : ℂ) : ℝ :=
  jacobian α r*Real.exp (η*neutralExponent α β r z)*
    ((2*drift t r+neutralSlope α β η t r z)*polynomial c0 c1 c2 (moment α η r z)+
      (c1+2*c2*moment α η r z)*momentSlope α η t r z)

theorem moment_derivative (r : ℝ → ℂ) (α η t s : ℝ) (z : ℂ)
    (hr : HasDerivAt r (velocity (1-t) t (r s)) s)
    (hα : α ≠ 0) (hA : area (r s) ≠ 0) (ha : (r s).re ≠ 0) (hb : (r s).im ≠ 0)
    (hD : denominator (1-t) t (r s) ≠ 0) (hf : fieldSlope (r s) ≠ 0) :
    HasDerivAt (fun u => moment α η (r u) z) (momentSlope α η t (r s) z) s := by
  have hd := (((KFCausalReciprocalWedgePrefactor.fieldSlope_derivative r t s hr hD hf).pow 2).const_mul η).mul
    (KFCausalReciprocalWedgeVelocity.first_derivative r α t s z hr hα hA ha hb hD)
  convert hd using 1
  dsimp
  unfold momentSlope moment
  ring

theorem weight_derivative (r : ℝ → ℂ) (α β η c0 c1 c2 t s : ℝ) (z : ℂ)
    (hr : HasDerivAt r (velocity (1-t) t (r s)) s)
    (hα : α ≠ 0) (hA : area (r s) ≠ 0) (ha : (r s).re ≠ 0) (hb : (r s).im ≠ 0)
    (hD : denominator (1-t) t (r s) ≠ 0) (hf : fieldSlope (r s) ≠ 0) :
    HasDerivAt (fun u => weight α β η c0 c1 c2 (r u) z)
      (weightSlope α β η c0 c1 c2 t (r s) z) s := by
  have hj := KFCausalReciprocalWedgePrefactor.jacobian_derivative r α t s hr hα hA ha hb hD
  have hn := (KFCausalReciprocalWedgeVelocity.neutralExponent_derivative r α β t s z hr hα hA ha hb hD).const_mul η
  have hm := moment_derivative r α η t s z hr hα hA ha hb hD hf
  have hp := ((hm.const_mul c1).const_add c0).add ((hm.pow 2).const_mul c2)
  have hd := (hj.mul hn.exp).mul hp
  convert hd using 1
  dsimp
  unfold weightSlope neutralSlope polynomial
  ring

theorem weight_nonnegative (α β η c0 c1 c2 : ℝ) (r z : ℂ)
    (hη : 0 ≤ η) (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (hz : z ∈ wedge α r) :
    0 ≤ weight α β η c0 c1 c2 r z := by
  have hx := hz.1
  unfold weight jacobian polynomial moment
  positivity

private theorem polynomial_growth (c0 c1 c2 T d M : ℝ)
    (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hd : d ≤ 3*M*T) :
    (c1+2*c2*T)*d ≤ 6*M*polynomial c0 c1 c2 T := by
  have hc : 0 ≤ c1+2*c2*T := by positivity
  calc
    _ ≤ (c1+2*c2*T)*(3*M*T) := mul_le_mul_of_nonneg_left hd hc
    _ ≤ _ := by
      unfold polynomial
      nlinarith [mul_nonneg hM h0,mul_nonneg (mul_nonneg hM h1) hT]

theorem weightSlope_upper (α β η c0 c1 c2 t M : ℝ) (r z : ℂ)
    (hβ : 0 ≤ β) (hη : 0 ≤ η) (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (ht : t ∈ Set.Icc 0 1) (hA : 0 < area r) (hz : z ∈ wedge α r)
    (hM : 0 ≤ M) (hd : |drift t r| ≤ M) (hf : |fieldScore t r| ≤ M) :
    weightSlope α β η c0 c1 c2 t r z ≤ 8*M*weight α β η c0 c1 c2 r z := by
  have hx := hz.1
  have hy := hz.2
  have hT : 0 ≤ moment α η r z := by unfold moment; positivity
  have hP : 0 ≤ polynomial c0 c1 c2 (moment α η r z) := by unfold polynomial; positivity
  have hd' : drift t r ≤ M := (le_abs_self _).trans hd
  have hf' : fieldScore t r ≤ M := (le_abs_self _).trans hf
  have hn : neutralSlope α β η t r z ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hη
      (KFCausalReciprocalWedgeVelocity.neutral_velocity_nonpositive α β t r z hβ ht hA hz)
  have hs := KFCausalReciprocalWedgeVelocity.shrink_nonnegative t r ht hA
  have hT' : momentSlope α η t r z ≤ 3*M*moment α η r z := by
    unfold momentSlope
    have hn' : 0 ≤ η*(fieldSlope r)^2*shrink t r*second α r z := by positivity
    have hg := mul_le_mul_of_nonneg_right (show 2*fieldScore t r+drift t r ≤ 3*M by linarith) hT
    linarith
  have hp := polynomial_growth c0 c1 c2 (moment α η r z) (momentSlope α η t r z) M h0 h1 h2 hT hM hT'
  have hj := mul_le_mul_of_nonneg_right (show 2*drift t r+neutralSlope α β η t r z ≤ 2*M by linarith) hP
  have hb' :
      (2*drift t r+neutralSlope α β η t r z)*polynomial c0 c1 c2 (moment α η r z)+
        (c1+2*c2*moment α η r z)*momentSlope α η t r z ≤
          8*M*polynomial c0 c1 c2 (moment α η r z) := by linarith
  unfold weightSlope weight
  have hpos : 0 ≤ jacobian α r*Real.exp (η*neutralExponent α β r z) := by unfold jacobian; positivity
  nlinarith [mul_le_mul_of_nonneg_left hb' hpos]

theorem exists_uniform_weight_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α β η c0 c1 c2 ε y s : ℝ,
      0 < α → 0 ≤ β → 0 ≤ η → 0 ≤ c0 → 0 ≤ c1 → 0 ≤ c2 →
      0 < ε → |y| ≤ Real.pi*ε/6 → y ≠ 0 → ∀ z ∈ wedge α (scale ε y s),
      deriv (fun u => weight α β η c0 c1 c2 (scale ε y u) z) s ≤
        C*weight α β η c0 c1 c2 (scale ε y s) z := by
  obtain ⟨M,hM,hbound⟩ := KFCausalReciprocalWedgePrefactor.exists_uniform_scores
  refine ⟨8*M,by positivity,?_⟩
  intro α β η c0 c1 c2 ε y s hα hβ hη h0 h1 h2 hε hy hy0 z hz
  have hy' : |y| ≤ Real.pi*ε/3 := by nlinarith [Real.pi_pos]
  have hp := KFCausalReciprocalWedgePrefactor.actual_mem_region ε y s hε hy
  have hA := KFCausalNeutralPlaneClockGeometry.scale_square_re_positive ε y s hε hy'
  have ht := fraction_bounds ε s hε
  have hd := normalized_denominator_positive _ _ ⟨ht.1.le,ht.2.le⟩ hA
  have hf := KFCausalReciprocalWedgePrefactor.region_field_positive _ hp
  have he := weight_derivative (scale ε y) α β η c0 c1 c2 (fraction ε s) s z
    (actual_normalized_velocity ε y s hε hy') hα.ne' hA.ne'
    (KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy').ne'
    (KFCausalNeutralPlaneClockGeometry.scale_im_ne_zero ε y s hε hy' hy0) hd.ne' hf.ne'
  rw [he.deriv]
  exact weightSlope_upper α β η c0 c1 c2 _ M _ z hβ hη h0 h1 h2
    ⟨ht.1.le,ht.2.le⟩ hA hz hM (hbound _ hp).1 (hbound _ hp).2

#print axioms moment_derivative
#print axioms weight_derivative
#print axioms weight_nonnegative
#print axioms weightSlope_upper
#print axioms exists_uniform_weight_bound
end
end UnifiedTheory.Audit.KFCausalReciprocalWedgeWeight
