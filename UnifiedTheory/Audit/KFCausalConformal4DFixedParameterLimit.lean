/- A fixed-parameter continuum limit of the actual compact temporal-conformal
operator. The endpoint is the actual second jet of the constructed profile;
no derivative/limit interchange or assumed continuum supplier is used. -/
import UnifiedTheory.Audit.KFCausalConformal4DConePushforward
import UnifiedTheory.Audit.KFCausalConformal4DRadialInverseOrigin
import UnifiedTheory.Audit.KFCausalBDG4DSmoothCompactSupplier
import UnifiedTheory.Audit.KFCausalBDG4DActualTemporalVariation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalConformal4DFixedParameterLimit
noncomputable section
open Real Set MeasureTheory Filter Topology
open KFCausalConformal4DTransformedProfile KFCausalConformal4DConePushforward
open KFCausalConformal4DRadialInverse KFCausalConformal4DRadialInverseOrigin
open KFCausalConformal4DNormalizedVolume
open KFCausalConformal4DCompactKernelDerivative (outerIntegral cutoff)
open KFCausalMinkowski4DEulerQuadrant
open KFCausalMinkowski4DMoments (f4D)
open KFCausalBDG4DSmoothCompactPartials (du dv)
open KFCausalBDG4DCompactPhysicalTest (densityParameter field)
open KFCausalBDG4DActualTemporalVariation (operator)

theorem profile_origin (c : ℝ) (hc : |c|≤1/54) : profile c hc (0,0)=1 := by
  rw [profile,show nullMap (0,0)=0 by norm_num [nullMap]]
  rw [amplitude_eq c hc 0 (by norm_num [targetBox]),inverse_origin]
  simp [coefficient,KFCausalConformal4DTemporalVariation.density_polynomial,cutoff,
    jacobian_factor_origin,KFCausalBDG4DCompactProfile.origin_jet.1]

theorem profile_upper_support (c : ℝ) (hc : |c|≤1/54) : UpperSupport 5 5 (profile c hc) := by
  intro p hp
  by_contra hn
  have hb := profile_support c hc p hn
  rcases hp with hp | hp
  · linarith [le_abs_self p.1,hb.1]
  · linarith [le_abs_self p.2,hb.2]

def quadrant (c : ℝ) (hc : |c|≤1/54) (a : ℝ) : ℝ :=
  ∫ v in Ioi (0:ℝ), ∫ u in Ioi (0:ℝ),
    a*(v-u)^2*f4D (a*u^2*v^2)*profile c hc (u,v)

theorem quadrant_identity (rho c : ℝ) (hc : |c|≤1/54) :
    quadrant c hc (densityParameter rho)=16*(densityParameter rho)*outerIntegral rho c := by
  let a := densityParameter rho
  let H : (ℝ×ℝ)→ℝ := fun p => a*(p.2-p.1)^2*f4D (a*p.1^2*p.2^2)*profile c hc p
  have hH : Continuous H := by
    apply Continuous.mul _ (profile_smooth c hc).continuous
    dsimp [f4D]
    fun_prop
  have hHs : UpperSupport 5 5 H := by
    intro p hp
    dsimp [H]
    rw [profile_upper_support c hc p hp,mul_zero]
  have he := KFCausalMinkowski4DVariationCone.kernel_cone_normalization f4D
    (by unfold f4D; fun_prop) a 5 (by norm_num) (profile c hc)
    (profile_smooth c hc).continuous (profile_compact c hc) (profile_upper_support c hc)
    (profile_symmetric c hc)
  have ho : KFCausalMinkowski4DVariationCone.coneIntegral f4D a (profile c hc)=
      outerIntegral rho c := (outer_integral_eq_flat_cone rho c hc).symm
  rw [ho] at he
  change quadrantIntegral H=16*a*outerIntegral rho c at he
  rw [quadrant_eq_iterated 5 5 H hH hHs] at he
  exact he

theorem operator_normalization (rho c : ℝ) (hc : |c|≤1/54) (hrho : 0≤rho) :
    operator rho c=(48/sqrt π)*(sqrt (densityParameter rho)*
      (quadrant c hc (densityParameter rho)-1/6)) := by
  have hs : sqrt (π*rho/24)=sqrt π*sqrt rho/(2*sqrt 6) := by
    rw [sqrt_div (mul_nonneg pi_pos.le hrho),sqrt_mul pi_pos.le,
      show (24:ℝ)=2^2*6 by norm_num,sqrt_mul (by norm_num : (0:ℝ)≤2^2),
      sqrt_sq (by norm_num : (0:ℝ)≤2)]
  rw [operator,KFCausalBDG4DCompactPhysicalTest.field_zero,quadrant_identity]
  unfold densityParameter
  rw [hs]
  field_simp [ne_of_gt (sqrt_pos.mpr pi_pos),ne_of_gt (sqrt_pos.mpr (by norm_num : (0:ℝ)<6))]
  ring

theorem operator_tendsto (c : ℝ) (hc : |c|≤1/54) :
    Tendsto (fun rho => operator rho c) atTop
      (𝓝 (2*(du (du (profile c hc)) (0,0)+dv (dv (profile c hc)) (0,0))-
        8*dv (du (profile c hc)) (0,0))) := by
  have ht := KFCausalBDG4DSmoothCompactSupplier.smooth_compact_quadrant_tendsto
    (profile c hc) (profile_smooth c hc) (profile_compact c hc) (profile_symmetric c hc)
  rw [profile_origin] at ht
  have ht' := (ht.comp KFCausalBDG4DCompactPhysicalTest.densityParameter_tendsto).const_mul
    (48/sqrt π)
  have he : (48/sqrt π)*(sqrt π/24*
      (du (du (profile c hc)) (0,0)+dv (dv (profile c hc)) (0,0))-
      sqrt π/6*dv (du (profile c hc)) (0,0))=
        2*(du (du (profile c hc)) (0,0)+dv (dv (profile c hc)) (0,0))-
          8*dv (du (profile c hc)) (0,0) := by
    field_simp [ne_of_gt (sqrt_pos.mpr pi_pos)]
    ring
  rw [he] at ht'
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with rho hrho
  exact (operator_normalization rho c hc hrho).symm

#print axioms profile_origin
#print axioms profile_upper_support
#print axioms quadrant_identity
#print axioms operator_normalization
#print axioms operator_tendsto
end
end UnifiedTheory.Audit.KFCausalConformal4DFixedParameterLimit
