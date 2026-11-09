/- Exact generating profile for the reciprocal-width charged family.
Its first two pointwise parameter derivatives recover the paired quadratic
and corrected quartic polynomials. These are profile derivative statements,
not unproved Hilbert or energy-graph differentiability assertions. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalChargedGeneratingProfile
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalQuarticChargeProfiles (chargedRadius quarticPolynomial)
open KFCausalChargedPairCoordinates (pairPolynomial)
open KFCausalReciprocalGaussianStates (quadratic configurationDensity)
open KFCausalReciprocalGaussianCharge (ratio generatingState)

def scalar (A B t : ℝ) : ℝ := Real.exp ((A*t+B*t^2)/(1-t^2))/(1-t^2)
def slope (A B t : ℝ) : ℝ :=
  (A+2*B*t+2*t)/(1-t^2)+2*t*(A*t+B*t^2)/(1-t^2)^2

theorem scalar_initial (A B : ℝ) : scalar A B 0 = 1 := by simp [scalar]

theorem scalar_derivative (A B t : ℝ) (ht : 1-t^2 ≠ 0) :
    HasDerivAt (scalar A B) (scalar A B t*slope A B t) t := by
  have hu := ((hasDerivAt_id t).const_mul A).add (((hasDerivAt_id t).pow 2).const_mul B)
  have hv := ((hasDerivAt_id t).pow 2).const_sub 1
  have he := (((hu.div hv ht).exp).div hv ht)
  convert he using 1
  simp only [scalar,slope]
  dsimp
  field_simp
  ring

private theorem slope_derivative_zero (A B : ℝ) :
    HasDerivAt (slope A B) (2*B+2) 0 := by
  have hi := hasDerivAt_id (0:ℝ)
  have hv := (hi.pow 2).const_sub 1
  have hn : (1:ℝ)-(0:ℝ)^2 ≠ 0 := by norm_num
  have hu := ((hi.const_mul (2*B)).const_add A).add (hi.const_mul 2)
  have hw := (hi.const_mul 2).mul ((hi.const_mul A).add ((hi.pow 2).const_mul B))
  have hd := (hu.div hv hn).add (hw.div (hv.pow 2) (pow_ne_zero 2 hn))
  convert hd using 1
  simp

theorem scalar_second_derivative_zero (A B : ℝ) :
    HasDerivAt (deriv (scalar A B)) (A^2+2*B+2) 0 := by
  have hd := (scalar_derivative A B 0 (by norm_num)).mul (slope_derivative_zero A B)
  have he : HasDerivAt (fun t => scalar A B t*slope A B t) (A^2+2*B+2) 0 := by
    convert hd using 1
    simp [scalar_initial,slope]
    ring
  have hn : ∀ᶠ t : ℝ in 𝓝 0, 1-t^2 ≠ 0 :=
    (continuous_const.sub (continuous_id.pow 2)).continuousAt.eventually_ne (by norm_num)
  apply he.congr_of_eventuallyEq
  filter_upwards [hn] with t ht
  exact (scalar_derivative A B t ht).deriv

theorem quadratic_ratio (t : ℝ) (ht : |t| < 1) (q : Transverse) :
    quadratic (ratio t) q =
      chargedRadius q-(4*t*pairPolynomial q-2*t^2*chargedRadius q)/(1-t^2) := by
  have hb := abs_lt.mp ht
  have hp : 1+t ≠ 0 := by linarith
  have hm : 1-t ≠ 0 := by linarith
  have hd : 1-t^2 ≠ 0 := by nlinarith [sq_abs t,abs_nonneg t]
  unfold quadratic ratio
  field_simp
  ring

def multiplier (α t : ℝ) (q : Transverse) : ℝ :=
  scalar (4*α*pairPolynomial q) (-2*α*chargedRadius q) t

theorem profile_identity (α β t : ℝ) (ht : |t| < 1)
    (g : ℝ → ℂ) (x : Configuration) :
    ((1/(1-t^2):ℝ):ℂ)*configurationDensity α β (ratio t) g x =
      (multiplier α t x.2:ℂ)*configurationDensity α β 1 g x := by
  have hq := quadratic_ratio t ht x.2
  have hq1 : quadratic 1 x.2 = chargedRadius x.2 := by simp [quadratic]
  have he : -(α*quadratic (ratio t) x.2+β*(x.2 4)^2) =
      ((4*α*pairPolynomial x.2)*t+(-2*α*chargedRadius x.2)*t^2)/(1-t^2)-
        (α*chargedRadius x.2+β*(x.2 4)^2) := by
    rw [hq]
    ring
  simp only [configurationDensity,hq1,← Complex.ofReal_neg,he,
    Complex.ofReal_sub,Complex.exp_sub,multiplier,scalar,Complex.ofReal_div,
    Complex.ofReal_exp,Complex.ofReal_one]
  rw [Complex.ofReal_neg,Complex.exp_neg]
  ring

theorem generating_configuration_coe (ε a h t : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (ht : |t| < 1) :
    generatingState ε a h hε ha hh t ht =ᵐ[volume] fun x : Configuration =>
      (multiplier (KFCausalChargeGaussianGeometry.groundWidth h) t x.2:ℂ)*
        configurationDensity (KFCausalChargeGaussianGeometry.groundWidth h)
          (KFCausalClockFloorInvariantTrial.neutralWidth h) 1
            (KFCausalClockFloorInvariantTrial.clockFunction ε a) x := by
  filter_upwards [Lp.coeFn_smul ((1/(1-t^2):ℝ):ℂ)
    (KFCausalReciprocalGaussianCharge.state ε a h (ratio t) hε ha hh
      (KFCausalReciprocalGaussianCharge.ratio_positive t ht)),
    KFCausalReciprocalGaussianCharge.state_configuration_coe ε a h (ratio t) hε ha hh
      (KFCausalReciprocalGaussianCharge.ratio_positive t ht)] with x hx hs
  change generatingState ε a h hε ha hh t ht x = _ at hx
  rw [hx,Pi.smul_apply,smul_eq_mul,hs]
  exact profile_identity _ _ t ht _ x

theorem multiplier_first_derivative_zero (α : ℝ) (q : Transverse) :
    HasDerivAt (fun t => multiplier α t q) (4*α*pairPolynomial q) 0 := by
  convert scalar_derivative (4*α*pairPolynomial q) (-2*α*chargedRadius q) 0 (by norm_num) using 1
  simp [scalar_initial,slope]

theorem multiplier_second_derivative_zero (α : ℝ) (hα : 0 < α) (q : Transverse) :
    HasDerivAt (deriv (fun t => multiplier α t q)) (16*α^2*quarticPolynomial α q) 0 := by
  convert scalar_second_derivative_zero (4*α*pairPolynomial q) (-2*α*chargedRadius q) using 1
  unfold quarticPolynomial
  field_simp
  ring

#print axioms scalar_initial
#print axioms scalar_derivative
#print axioms scalar_second_derivative_zero
#print axioms quadratic_ratio
#print axioms profile_identity
#print axioms generating_configuration_coe
#print axioms multiplier_first_derivative_zero
#print axioms multiplier_second_derivative_zero
end
end UnifiedTheory.Audit.KFCausalChargedGeneratingProfile
