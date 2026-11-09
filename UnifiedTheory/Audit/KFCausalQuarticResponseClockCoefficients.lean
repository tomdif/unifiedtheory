/- Physical clock certificates for the combined quartic response.
The field residual is quadratic in the imaginary shift. Its Young
certificate is polynomial and remains valid at zero shift. -/
import UnifiedTheory.Audit.KFCausalJointFourierRealDilationClock
import UnifiedTheory.Audit.KFCausalChargedCoolingBoundaryScore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalQuarticResponseClockCoefficients
noncomputable section
open KFCausalClockFloorRelativeShift (scale)
open KFCausalClockFloorExactScaleRegion
open KFCausalNeutralPlaneClockGeometry (denominator)
open KFCausalNeutralPlaneNormalizedGeometry
open KFCausalJointClockCoolingCoercivity (imaginaryRate normalized_denominator_bounds)
open KFCausalJointFourierDissipationClock
open KFCausalJointFourierRealDilationClock
open KFCausalChargedCoolingBoundaryScore (scoreRate)
open KFCausalReciprocalWedgeVelocity (radius)
open KFCausalChargedPairCoordinates (fieldSlope)

def residual (t : ℝ) (r : ℂ) : ℝ :=
  (4/3:ℝ)*(t*normalizedRealCooling t r)*(scoreRate r/2)*fieldSlope r-t*normalizedFieldJet t r

theorem residual_identity (t : ℝ) (r : ℂ) (ha : r.re≠0) (hA : r.re^2-r.im^2≠0) :
    residual t r=2*(t*normalizedRealCooling t r)*fieldSlope r*r.im^2/
      (3*r.re*(r.re^2-r.im^2))+3*realDilationRate t r := by
  rw [rate_decomposition t r ha]
  rw [dilation_identity]
  unfold residual normalizedFieldJet scoreRate fieldSlope
  field_simp
  ring

variable (ε y s : ℝ) (hε : 0<ε) (hy : |y|≤Real.pi*ε/3)
local notation "r" => scale ε y s
include hε hy

theorem geometric_bounds : (5/6:ℝ)≤(r).re ∧ (r).re≤5/4 ∧
    (1/2:ℝ)≤(r).re^2-(r).im^2 ∧ 1≤radius r ∧ (r).im^2≤1/2 ∧
    0≤fieldSlope r ∧ fieldSlope r≤4/3 := by
  have ha := real_coordinate_bounds ε y s hε hy
  have hA := square_re_half_le ε y s hε hy
  have hR := norm_square_one_le ε y s hε hy
  have hb := imaginary_square_le_half ε y s hε hy
  have hL := fieldSlope_bounds ε y s hε hy
  have ha' : (5/6:ℝ)≤(r).re := by nlinarith [ha.1]
  refine ⟨ha',ha.2,hA,hR,hb,by linarith [hL.1],?_⟩
  unfold fieldSlope
  linarith

theorem score_bounds :
    3/(4*(r).re)≤scoreRate r/2 ∧ scoreRate r/2≤15/8 := by
  obtain ⟨ha,ha1,hA,_,_,_,_⟩ := geometric_bounds ε y s hε hy
  have hap : 0<(r).re := by linarith
  have hAp : 0<(r).re^2-(r).im^2 := by linarith
  have he : scoreRate r/2=(3*(r).re^2-(r).im^2)/(4*(r).re*((r).re^2-(r).im^2)) := by
    unfold scoreRate
    field_simp
    ring
  rw [he]
  constructor
  · apply (le_div_iff₀ (by positivity : 0<4*(r).re*((r).re^2-(r).im^2))).mpr
    field_simp
    nlinarith [sq_nonneg (r).im]
  · apply (div_le_iff₀ (by positivity : 0<4*(r).re*((r).re^2-(r).im^2))).mpr
    have he' : 3*(r).re^2-(r).im^2≤3*(r).re^2 := by nlinarith [sq_nonneg (r).im]
    have hm := mul_le_mul_of_nonneg_left hA (show 0≤(15/2:ℝ)*(r).re by positivity)
    have hh := mul_le_mul_of_nonneg_left ha1 (show 0≤3*(r).re by positivity)
    nlinarith only [he',hm,hh]

theorem real_rate_relative_bound (t : ℝ) (ht : t∈Set.Icc 0 1) :
    |realDilationRate t r|≤(12/5:ℝ)*(t*normalizedRealCooling t r)*(r).im^2 := by
  obtain ⟨ha,_,_,hR,_,_,_⟩ := geometric_bounds ε y s hε hy
  have ht0 := ht.1
  have hD := normalized_denominator_bounds ε y s hε hy t ht
  have hDp : 0<denominator (1-t) t r := by linarith [hD.1]
  have hN := real_numerator_bounds ε y s hε hy t ht
  have hn : |realNumerator t r|≤4*(r).im^2 := abs_le.mpr ⟨by nlinarith only [hN.1],hN.2⟩
  have hprod : (5/6:ℝ)≤(r).re*radius r := by
    have hm := mul_le_mul ha hR (by norm_num : (0:ℝ)≤1) (by linarith : 0≤(r).re)
    simpa only [mul_one] using hm
  unfold realDilationRate normalizedRealCooling
  rw [abs_div,abs_mul,abs_of_nonneg ht.1,abs_of_pos (by positivity : 0<2*denominator (1-t) t r)]
  apply (div_le_iff₀ (by positivity : 0<2*denominator (1-t) t r)).mpr
  have he : (12/5:ℝ)*(t*((r).re*radius r/denominator (1-t) t r))*(r).im^2*
      (2*denominator (1-t) t r)=(24/5:ℝ)*t*((r).re*radius r)*(r).im^2 := by
    field_simp
    ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hn ht.1
  have hh := mul_le_mul_of_nonneg_right hprod (show 0≤(24/5:ℝ)*t*(r).im^2 by positivity)
  nlinarith only [hm,hh]

theorem residual_bound (t : ℝ) (ht : t∈Set.Icc 0 1) :
    |residual t r|≤(28/3:ℝ)*(t*normalizedRealCooling t r)*(r).im^2 := by
  obtain ⟨ha,_,hA,_,_,hL,hL1⟩ := geometric_bounds ε y s hε hy
  have hap : 0<(r).re := by linarith
  have hAp : 0<(r).re^2-(r).im^2 := by linarith
  have hd := (real_cooling_bounds ε y s hε hy t ht).1
  have hδ : 0≤t*normalizedRealCooling t r := mul_nonneg ht.1 (by linarith)
  have hh := real_rate_relative_bound ε y s hε hy t ht
  have hfirst : 0≤2*(t*normalizedRealCooling t r)*fieldSlope r*(r).im^2/
      (3*(r).re*((r).re^2-(r).im^2)) := by positivity
  have hden : (5/4:ℝ)≤3*(r).re*((r).re^2-(r).im^2) := by
    have hm := mul_le_mul ha hA (by norm_num : (0:ℝ)≤1/2) (by linarith : 0≤(r).re)
    nlinarith only [hm]
  have hf : 2*(t*normalizedRealCooling t r)*fieldSlope r*(r).im^2/
      (3*(r).re*((r).re^2-(r).im^2))≤(32/15:ℝ)*(t*normalizedRealCooling t r)*(r).im^2 := by
    apply (div_le_iff₀ (by positivity : 0<3*(r).re*((r).re^2-(r).im^2))).mpr
    have hm := mul_le_mul_of_nonneg_left hL1 (show 0≤2*(t*normalizedRealCooling t r)*(r).im^2 by positivity)
    have hn := mul_le_mul_of_nonneg_left hden (show 0≤(32/15:ℝ)*(t*normalizedRealCooling t r)*(r).im^2 by positivity)
    nlinarith only [hm,hn]
  rw [residual_identity t r hap.ne' hAp.ne']
  have hab := abs_add_le (2*(t*normalizedRealCooling t r)*fieldSlope r*(r).im^2/
    (3*(r).re*((r).re^2-(r).im^2))) (3*realDilationRate t r)
  rw [abs_of_nonneg hfirst,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)] at hab
  linarith only [hab,hf,hh]

theorem young_certificate (t β : ℝ) (ht : t∈Set.Icc 0 1) (hβ : 0<β) :
    (residual t r)^2≤((t*normalizedRealCooling t r)*(scoreRate r/2)*(8*β*(r).im^2)/3)*
      (1/(4*β))*((9800/9:ℝ)*t) := by
  have ht0 := ht.1
  have hrb := residual_bound ε y s hε hy t ht
  have hb := imaginary_square_le_half ε y s hε hy
  obtain ⟨ha,ha1,_,_,_,_,_⟩ := geometric_bounds ε y s hε hy
  have hap : 0<(r).re := by linarith
  have hδb := real_cooling_bounds ε y s hε hy t ht
  have hg := score_bounds ε y s hε hy
  have hγ : 0<scoreRate r/2 := lt_of_lt_of_le (by positivity : 0<3/(4*(r).re)) hg.1
  have hδ : 0≤t*normalizedRealCooling t r := mul_nonneg ht.1 (by linarith [hδb.1])
  have hδγ : t*normalizedRealCooling t r≤(50/3:ℝ)*t*(scoreRate r/2) := by
    have hgl : (3/5:ℝ)≤scoreRate r/2 := by
      apply le_trans ?_ hg.1
      exact (le_div_iff₀ (by positivity : 0<4*(r).re)).mpr (by nlinarith only [ha1])
    have h1 := mul_le_mul_of_nonneg_left hδb.2 ht.1
    have h2 := mul_le_mul_of_nonneg_left hgl (show 0≤(50/3:ℝ)*t by positivity)
    nlinarith only [h1,h2]
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤(28/3:ℝ)*(t*normalizedRealCooling t r)*(r).im^2)).mpr hrb
  rw [sq_abs] at hs
  have h1 := mul_le_mul_of_nonneg_right hδγ
    (show 0≤(784/9:ℝ)*(t*normalizedRealCooling t r)*(r).im^2*((r).im^2) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hb
    (show 0≤(39200/27:ℝ)*(t*normalizedRealCooling t r)*t*(scoreRate r/2)*(r).im^2 by positivity)
  have he : ((t*normalizedRealCooling t r)*(scoreRate r/2)*(8*β*(r).im^2)/3)*
      (1/(4*β))*((9800/9:ℝ)*t)=
      (19600/27:ℝ)*(t*normalizedRealCooling t r)*t*(scoreRate r/2)*(r).im^2 := by field_simp; ring
  rw [he]
  nlinarith only [hs,h1,h2]

theorem loss_bound (t C : ℝ) (ht : t∈Set.Icc 0 1) (hC : 0≤C) :
    -4*imaginaryRate t r+(t*normalizedRealCooling t r)*((scoreRate r/2)*(C-2)/3-1/(r).re)+
      (9800/9:ℝ)*t≤(1200+25*C/4)*t := by
  have ht0 := ht.1
  have ha := (geometric_bounds ε y s hε hy).1
  have hap : 0<(r).re := by linarith
  have hδb := real_cooling_bounds ε y s hε hy t ht
  have hg := score_bounds ε y s hε hy
  have hγ : 0≤scoreRate r/2 := le_trans (by positivity : 0≤3/(4*(r).re)) hg.1
  have hδ : 0≤t*normalizedRealCooling t r := mul_nonneg ht.1 (by linarith [hδb.1])
  have hlam := (dilation_bounds ε y s hε hy t ht).1
  have hl := mul_le_mul_of_nonneg_left hlam ht.1
  rw [←dilation_identity] at hl
  have h1 := mul_le_mul_of_nonneg_left hδb.2 ht.1
  have h2 := mul_le_mul h1 hg.2 hγ (show 0≤t*10 by positivity)
  have h3 := mul_le_mul_of_nonneg_right h2 (show 0≤C/3 by positivity)
  have h4 := mul_nonneg hδ (show 0≤2*(scoreRate r/2)/3+1/(r).re by positivity)
  nlinarith only [hl,h3,h4,ht.1]

#print axioms residual_identity
#print axioms geometric_bounds
#print axioms score_bounds
#print axioms real_rate_relative_bound
#print axioms residual_bound
#print axioms young_certificate
#print axioms loss_bound
end
end UnifiedTheory.Audit.KFCausalQuarticResponseClockCoefficients
