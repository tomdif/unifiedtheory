/- A full integrated response bound for the genuine second joint width/source
jet. The charged marginal estimate is proved for this profile, and all
outer integration and physical clock hypotheses are derived here. -/
import UnifiedTheory.Audit.KFCausalConfluentThreePhysicalMarginal
import UnifiedTheory.Audit.KFCausalJointSourceConfluenceQuadraticSplit
import UnifiedTheory.Audit.KFCausalConfluentThreePhysicalClockLoss
import UnifiedTheory.Audit.KFCausalChargedMarginalReordering
import UnifiedTheory.Audit.KFCausalClusteredResponseLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointSourceConfluenceQuadraticBound
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalJointSourceConfluenceFactors (limitDensity limitResponse)
open KFCausalJointSourceConfluenceQuadraticCooling (coolingResponse)
open KFCausalChargedMarginalReordering (outer_integrable integral_order)
open KFCausalConfluentThreePhysicalClockLoss (fieldLoss)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry (fraction actual_normalized_velocity)
open KFCausalJointClockCoolingCoercivity (imaginaryRate)
open KFCausalJointFourierDissipationClock

theorem cooling_integral_bound (α β w δ ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ)
    (hα : 0 < α) (hw : 1 ≤ w) (hr : |r.im| < r.re) (hδ : 0 < δ)
    (hβ : 0 < β) (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) :
    (∫ p, coolingResponse α β w δ (-2*δ-3*ell) r b ℓ P p ∂jointMeasure) ≤
      (16*(-2*δ-3*ell)^2/(δ*α*r.re*w))*
        ∫ p, limitDensity 2 α β w r b ℓ P p ∂jointMeasure := by
  have hR := KFCausalJointSourceConfluenceQuadraticSplit.cooling_integrable
    α β w δ ell r b ℓ P hw hβ hA hC
  have hE := KFCausalJointSourceConfluenceIntegrability.density_integrable
    2 α β w r b ℓ P hw hβ hA hC
  rw [integral_order _ hR,integral_order _ hE,← integral_const_mul]
  apply integral_mono (outer_integrable _ hR)
    ((outer_integrable _ hE).const_mul (16*(-2*δ-3*ell)^2/(δ*α*r.re*w)))
  intro q
  exact KFCausalConfluentThreePhysicalMarginal.physical_marginal_bound
    α β w δ (-2*δ-3*ell) r b ℓ P q.1 q.2 hα (zero_lt_one.trans_le hw) hr hδ

theorem response_integral_bound (α β w : ℝ) (r rd : ℂ) (ell : ℝ)
    (b ℓ : ℂ) (P : Polynomial ℂ) (hα : 0 < α) (hw : 1 ≤ w)
    (hr : |r.im| < r.re) (hδ : 0 < rd.re-ell*r.re) (hi : rd.im=ell*r.im)
    (hβ : 0 < β) (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) :
    (∫ p, limitResponse 2 α β w r rd b ℓ P p ∂jointMeasure) ≤
      (-4*ell+fieldLoss α w r rd ell)*
        ∫ p, limitDensity 2 α β w r b ℓ P p ∂jointMeasure := by
  have he : rd=((rd.re-ell*r.re:ℝ):ℂ)+(ell:ℂ)*r := by
    apply Complex.ext
    · simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
        zero_mul,sub_zero]
      ring
    · simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
        zero_mul,add_zero,zero_add] using hi
  have hs := KFCausalJointSourceConfluenceQuadraticSplit.response_integral
    α β w (rd.re-ell*r.re) ell r b ℓ P hw hβ hA hC
  rw [← he] at hs
  have hb := cooling_integral_bound α β w (rd.re-ell*r.re) ell r b ℓ P
    hα hw hr hδ hβ hA hC
  have hc : 16*(-2*(rd.re-ell*r.re)-3*ell)^2/((rd.re-ell*r.re)*α*r.re*w)=
      fieldLoss α w r rd ell := by
    unfold fieldLoss
    congr 1
    ring
  rw [hc] at hb
  rw [hs,add_mul]
  exact add_le_add le_rfl hb

theorem actual_integral_bound (α β w ε y s : ℝ) (b ℓ : ℂ) (P : Polynomial ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α) (hw : 1 ≤ w)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    (∫ p, limitResponse 2 α β w (scale ε y s) (deriv (scale ε y) s)
      b ℓ P p ∂jointMeasure) ≤
      ((48+331776/α)*fraction ε s)*
        ∫ p, limitDensity 2 α β w (scale ε y s) b ℓ P p ∂jointMeasure := by
  let r := scale ε y s
  let rd := deriv (scale ε y) s
  let ell := imaginaryRate (fraction ε s) r
  have hf := KFCausalClusteredResponseLimit.actual_width_floors α β ε y
    hα hβ hwidth hε hy s
  have hp := KFCausalChargedPairCompactGeometry.widthFloor_positive α hα
  have hδ : 0 < rd.re-ell*r.re := by
    dsimp only [rd,ell,r]
    rw [(actual_normalized_velocity ε y s hε hy).deriv]
    exact actual_real_cooling_positive ε y s hε hy
  have hi : rd.im=ell*r.im :=
    KFCausalJointFourierDilationJet.actual_imaginary_cancellation ε y s hε hy
  have hb := response_integral_bound α β w r rd ell b ℓ P hα hw
    (KFCausalChargedCoolingActualPhase.actual_sector ε y s hε hy) hδ hi hβ
    (hp.trans_le hf.1) (hp.trans_le hf.2)
  have hl := KFCausalConfluentThreePhysicalClockLoss.actual_loss_bound
    ε y s hε hy α w hα hw
  have hE : 0 ≤ ∫ p, limitDensity 2 α β w r b ℓ P p ∂jointMeasure :=
    integral_nonneg (KFCausalJointSourceConfluenceIntegrability.density_nonnegative
      2 α β w r b ℓ P)
  exact hb.trans (mul_le_mul_of_nonneg_right hl hE)

#print axioms cooling_integral_bound
#print axioms response_integral_bound
#print axioms actual_integral_bound
end
end UnifiedTheory.Audit.KFCausalJointSourceConfluenceQuadraticBound
