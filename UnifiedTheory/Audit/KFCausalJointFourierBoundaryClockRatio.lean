/- The exact clock balances control the ratio of tangential to normal
motion at the coupled charged/neutral boundary. This coefficient estimate
does not assert a global response or boundary trace inequality. -/
import UnifiedTheory.Audit.KFCausalJointFourierRealDilationClock
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointFourierBoundaryClockRatio
noncomputable section
open KFCausalClockFloorRelativeShift
open KFCausalClockFloorExactScaleRegion
open KFCausalNeutralPlaneClockGeometry
open KFCausalNeutralPlaneNormalizedGeometry

theorem tangent_support (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : v < Real.pi/2) :
    (Real.tan v-Real.tan u)*Real.cos u^2 ≥ v-u := by
  have hc : ∀ x ∈ Set.Icc u v, 0 < Real.cos x := by
    intro x hx
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hx.1],by linarith [hx.2]⟩
  have hd : ∀ x ∈ Set.Icc u v,
      HasDerivAt (fun x => Real.tan x*Real.cos u^2-x)
        ((1/Real.cos x^2)*Real.cos u^2-1) x := by
    intro x hx
    exact ((Real.hasDerivAt_tan (hc x hx).ne').mul_const _).sub (hasDerivAt_id x)
  have hm : MonotoneOn (fun x => Real.tan x*Real.cos u^2-x) (Set.Icc u v) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc u v)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    have hx' : x ∈ Set.Icc u v := interior_subset hx
    have hcx := hc x hx'
    have hcu := hc u ⟨le_rfl,huv⟩
    have hle := Real.cos_le_cos_of_nonneg_of_le_pi hu
      (show x ≤ Real.pi by linarith [hx'.2,Real.pi_pos]) hx'.1
    have hs : Real.cos x^2 ≤ Real.cos u^2 := by nlinarith
    have hh : 1 ≤ Real.cos u^2/Real.cos x^2 :=
      (le_div_iff₀ (sq_pos_of_pos hcx)).mpr (by simpa using hs)
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using sub_nonneg.mpr hh
  have h := hm ⟨le_rfl,huv⟩ ⟨huv,le_rfl⟩ huv
  nlinarith

theorem clock_tangent_growth (q θ φ : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hθhi : θ ≤ Real.pi/3) (hφ : φ ≤ Real.pi/3)
    (he : φ = θ+q*Real.sin θ) :
    (1+q)*Real.tan (θ/2) ≤ Real.tan (φ/2) := by
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ
    (by linarith [Real.pi_pos])
  have hθφ : θ ≤ φ := by
    have hp := mul_nonneg hq hs
    linarith
  have hc : 0 < Real.cos (θ/2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hdouble : Real.sin θ = 2*Real.tan (θ/2)*Real.cos (θ/2)^2 := by
    conv_lhs => rw [show θ = 2*(θ/2) by ring,Real.sin_two_mul]
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have ht := tangent_support (θ/2) (φ/2) (by linarith) (by linarith)
    (by linarith [Real.pi_pos])
  have hpos := sq_pos_of_pos hc
  rw [hdouble] at he
  apply (mul_le_mul_iff_left₀ hpos).mp
  nlinarith

theorem clock_ratio_envelope (τ R θ φ : ℝ) (hτ : 0 ≤ τ) (hR : 1 ≤ R)
    (hθ : 0 ≤ θ) (hθhi : θ ≤ Real.pi/3) (hφ : φ ≤ Real.pi/3)
    (hA : R*Real.cos θ ≤ 1)
    (himag : φ = θ+τ*R*Real.sin θ) :
    |(1-R*Real.cos θ)-τ*(R^2-R*Real.cos θ)| ≤
      (1+τ)*(R*Real.sin θ)*Real.tan (φ/2) := by
  have hRp : 0 < R := by linarith
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ
    (by linarith [Real.pi_pos])
  have hhalf : 0 < Real.cos (θ/2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hg := clock_tangent_growth (τ*R) θ φ (mul_nonneg hτ hRp.le)
    hθ hθhi hφ himag
  have hhalfidentity : Real.sin θ*Real.tan (θ/2) = 1-Real.cos θ := by
    rw [show θ = 2*(θ/2) by ring,Real.sin_two_mul,Real.cos_two_mul,
      Real.tan_eq_sin_div_cos]
    have hsq := Real.sin_sq_add_cos_sq (θ/2)
    field_simp
    nlinarith
  have hpad : 0 ≤ (τ+τ*R+τ^2*R)*(R-R*Real.cos θ) := by
    apply mul_nonneg
    · positivity
    · linarith
  have hlower : 0 ≤ (R-1)*(1+τ^2*R)+(1-R*Real.cos θ)*(2+τ*R+τ^2*R) := by
    apply add_nonneg
    · exact mul_nonneg (by linarith) (by positivity)
    · exact mul_nonneg (by linarith) (by positivity)
  have hnonneg : 0 ≤ τ*(R^2-R*Real.cos θ) := by
    have hsq : 1 ≤ R^2 := by nlinarith
    exact mul_nonneg hτ (by linarith)
  have hbound : |(1-R*Real.cos θ)-τ*(R^2-R*Real.cos θ)| ≤
      (1+τ)*(1+τ*R)*(R-R*Real.cos θ) := by
    apply abs_le.mpr
    constructor <;> nlinarith
  apply hbound.trans
  have hh := mul_le_mul_of_nonneg_left hg
    (mul_nonneg (show 0 ≤ 1+τ by linarith) (mul_nonneg hRp.le hs))
  calc
    _ = (1+τ)*(R*Real.sin θ)*((1+τ*R)*Real.tan (θ/2)) := by
      rw [show R-R*Real.cos θ = R*(1-Real.cos θ) by ring,← hhalfidentity]
      ring
    _ ≤ _ := hh

theorem scale_squared_trigonometry (ε y s : ℝ) :
    (scale ε y s).re^2-(scale ε y s).im^2 =
      ((scale ε y s).re^2+(scale ε y s).im^2)*Real.cos (relative ε y s).im ∧
    2*(scale ε y s).re*(scale ε y s).im =
      ((scale ε y s).re^2+(scale ε y s).im^2)*Real.sin (relative ε y s).im := by
  have he := KFCausalClockFloorShearBounds.complexScale_square (relative ε y s)
  change (scale ε y s)^2 = Complex.exp (relative ε y s) at he
  rw [scale_norm_square]
  constructor
  · have hh := congrArg Complex.re he
    simp only [pow_two,Complex.mul_re,Complex.exp_re] at hh
    nlinarith
  · have hh := congrArg Complex.im he
    simp only [pow_two,Complex.mul_im,Complex.exp_im] at hh
    nlinarith

variable (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
local notation "r" => scale ε y s
local notation "ψ" => Complex.im (relative ε y s)
local notation "R" => (Complex.re (scale ε y s))^2+(Complex.im (scale ε y s))^2
include hε hy

theorem imaginary_clock_balance :
    Real.exp s*(2*(r).re*(r).im)+ε*ψ = y := by
  have he := KFCausalComplexClockInverse.complexInverse_right ε hε
    (argument ε y s) (argument_mem ε y s hε hy)
  change Complex.exp (inverse ε y s)+(ε:ℂ)*inverse ε y s = argument ε y s at he
  rw [← scale_square] at he
  have hi := congrArg Complex.im he
  simp only [argument,KFCausalRegularizedLongitudinalChart.chart,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,pow_two] at hi
  simp only [relative,Complex.sub_im,Complex.ofReal_im,sub_zero]
  nlinarith

theorem absolute_clock_phase_balance :
    |y|/ε = |ψ|+(Real.exp s/ε)*R*Real.sin |ψ| := by
  have hψ : |ψ| ≤ Real.pi/3 := by
    apply (Complex.abs_im_le_norm _).trans
    apply (relative_bound ε y s hε hy).trans
    exact (div_le_iff₀ hε).mpr (by nlinarith)
  have hb := imaginary_clock_balance ε y s hε hy
  rw [(scale_squared_trigonometry ε y s).2] at hb
  have he : y/ε = ψ+(Real.exp s/ε)*R*Real.sin ψ := by
    apply (div_eq_iff hε.ne').mpr
    field_simp
    nlinarith [hb]
  have hp : 0 ≤ (Real.exp s/ε)*R := by positivity
  have hh := congrArg abs he
  rw [abs_div,abs_of_pos hε] at hh
  by_cases hsign : 0 ≤ ψ
  · have hs : 0 ≤ Real.sin ψ := Real.sin_nonneg_of_nonneg_of_le_pi hsign
      (by linarith [abs_le.mp hψ,Real.pi_pos])
    rw [abs_of_nonneg (show 0 ≤ ψ+(Real.exp s/ε)*R*Real.sin ψ by positivity)] at hh
    simpa only [abs_of_nonneg hsign] using hh
  · have hsign' : ψ ≤ 0 := le_of_not_ge hsign
    have hs : Real.sin ψ ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le hsign'
      (by linarith [(abs_le.mp hψ).1,Real.pi_pos])
    rw [abs_of_nonpos (show ψ+(Real.exp s/ε)*R*Real.sin ψ ≤ 0 by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hp hs])] at hh
    rw [abs_of_nonpos hsign',Real.sin_neg]
    nlinarith [hh]

theorem actual_boundary_numerator_tangent_bound :
    |realNumerator (fraction ε s) r-2*(r).im^2| ≤
      |2*(r).re*(r).im| * Real.tan (|y|/ε/2) := by
  have hψ : |ψ| ≤ Real.pi/3 := by
    apply (Complex.abs_im_le_norm _).trans
    apply (relative_bound ε y s hε hy).trans
    exact (div_le_iff₀ hε).mpr (by nlinarith)
  have hR := norm_square_one_le ε y s hε hy
  have hA := square_re_le_one ε y s hε hy
  have htrig := scale_squared_trigonometry ε y s
  have hcos : R*Real.cos |ψ| = (r).re^2-(r).im^2 := by
    rw [Real.cos_abs]
    exact htrig.1.symm
  have hsin : R*Real.sin |ψ| = |2*(r).re*(r).im| := by
    rw [← Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [Real.pi_pos] : |ψ| ≤ Real.pi)]
    rw [← abs_of_nonneg (show 0 ≤ R by positivity),← abs_mul,← htrig.2]
  have henv := clock_ratio_envelope (Real.exp s/ε) R |ψ| (|y|/ε)
    (by positivity) hR (abs_nonneg _) hψ
    ((div_le_iff₀ hε).mpr (by nlinarith))
    (by rw [hcos]; exact hA) (absolute_clock_phase_balance ε y s hε hy)
  rw [hcos,hsin] at henv
  have hn : (1+Real.exp s/ε)*(realNumerator (fraction ε s) r-2*(r).im^2) =
      (1-((r).re^2-(r).im^2))-(Real.exp s/ε)*(R^2-((r).re^2-(r).im^2)) := by
    unfold realNumerator fraction
    field_simp
    ring
  rw [← hn,abs_mul,abs_of_pos (show 0 < 1+Real.exp s/ε by positivity)] at henv
  apply (mul_le_mul_iff_right₀ (show 0 < 1+Real.exp s/ε by positivity)).mp
  simpa only [mul_assoc] using henv

theorem actual_boundary_numerator_bound :
    |realNumerator (fraction ε s) r-2*(r).im^2| ≤
      |2*(r).re*(r).im|/Real.sqrt 3 := by
  have ht : Real.tan (|y|/ε/2) ≤ Real.tan (Real.pi/6) := by
    apply Real.strictMonoOn_tan.monotoneOn
    · constructor
      · have hp : 0 ≤ |y|/ε/2 := by positivity
        linarith [Real.pi_pos]
      · have hp : |y|/ε ≤ Real.pi/3 := (div_le_iff₀ hε).mpr (by nlinarith)
        linarith [Real.pi_pos]
    · constructor <;> linarith [Real.pi_pos]
    · have hp : |y|/ε ≤ Real.pi/3 := (div_le_iff₀ hε).mpr (by nlinarith)
      linarith
  rw [Real.tan_pi_div_six] at ht
  exact (actual_boundary_numerator_tangent_bound ε y s hε hy).trans
    (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left ht (abs_nonneg (2*(r).re*(r).im)))

theorem actual_boundary_ratio_bound :
    |(realNumerator (fraction ε s) r-2*(r).im^2)/(2*(r).re*(r).im)| ≤
      1/Real.sqrt 3 := by
  by_cases hb : 2*(r).re*(r).im = 0
  · rw [hb,div_zero,abs_zero]
    positivity
  · rw [abs_div]
    apply (div_le_iff₀ (abs_pos.mpr hb)).mpr
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using
      actual_boundary_numerator_bound ε y s hε hy

theorem actual_boundary_square_bound :
    3*(realNumerator (fraction ε s) r-2*(r).im^2)^2 ≤
      4*(r).re^2*(r).im^2 := by
  have hb := actual_boundary_numerator_bound ε y s hε hy
  have hs : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h := (le_div_iff₀ hs).mp hb
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hh := sq_le_sq₀ (by positivity : 0 ≤
    |realNumerator (fraction ε s) r-2*(r).im^2| * Real.sqrt 3)
    (abs_nonneg (2*(r).re*(r).im))
  have hh' := hh.mpr h
  rw [mul_pow,sq_abs,hsq,sq_abs] at hh'
  nlinarith

#print axioms tangent_support
#print axioms clock_tangent_growth
#print axioms clock_ratio_envelope
#print axioms scale_squared_trigonometry
#print axioms imaginary_clock_balance
#print axioms absolute_clock_phase_balance
#print axioms actual_boundary_numerator_tangent_bound
#print axioms actual_boundary_numerator_bound
#print axioms actual_boundary_ratio_bound
#print axioms actual_boundary_square_bound
end
end UnifiedTheory.Audit.KFCausalJointFourierBoundaryClockRatio
