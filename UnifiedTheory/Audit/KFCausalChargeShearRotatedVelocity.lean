/- The infinitesimal vector field of the actual mixed shear, conjugated by
normalized charge rotations. Four quarter turns cancel exactly. This is
an unweighted differential identity, not an exponential force estimate. -/
import UnifiedTheory.Audit.KFCausalChargeShearJointFlow
import UnifiedTheory.Audit.KFCausalMixedRotationMomentumGraph
import Mathlib.Analysis.Calculus.FDeriv.WithLp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 300000

namespace UnifiedTheory.Audit.KFCausalChargeShearRotatedVelocity
noncomputable section
open UnifiedTheory.Audit.KFCausalChargeShearJointFlow
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (flowEquiv)
open UnifiedTheory.Audit.KFCausalMixedRotationMomentumGraph (linearFlow)

def velocity (x : Space) : Space := WithLp.toLp 2 fun
  | .inl i => -x (.inl i)/2
  | .inr i => ![0,x (.inr 1)/2,x (.inr 2)/2,2*scale*x (.inr 2)] i

theorem flow_derivative_zero (x : Space) :
    HasDerivAt (fun t => flow t x) (velocity x) 0 := by
  have hn : HasDerivAt (fun t : ℝ => Real.exp (-t/2)) (-(1/2)) 0 := by
    convert (((hasDerivAt_id (0:ℝ)).neg).div_const 2).exp using 1
    norm_num
  have hp : HasDerivAt (fun t : ℝ => Real.exp (t/2)) (1/2) 0 := by
    convert ((hasDerivAt_id (0:ℝ)).div_const 2).exp using 1
    norm_num
  have hd : HasDerivAt (fun t => WithLp.ofLp (flow t x)) (WithLp.ofLp (velocity x)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    rcases i with i | i
    · change HasDerivAt (fun t => Real.exp (-1*t/2)*x (.inl i)) (-x (.inl i)/2) 0
      simpa only [neg_one_mul] using (hn.mul_const (x (.inl i))).congr_deriv (by ring)
    · fin_cases i
      · exact hasDerivAt_const 0 (x (.inr 0))
      · change HasDerivAt (fun t => Real.exp (t/2)*x (.inr 1)) (x (.inr 1)/2) 0
        exact (hp.mul_const (x (.inr 1))).congr_deriv (by ring)
      · change HasDerivAt (fun t => Real.exp (t/2)*x (.inr 2)) (x (.inr 2)/2) 0
        exact (hp.mul_const (x (.inr 2))).congr_deriv (by ring)
      · change HasDerivAt (fun t => x (.inr 3)+4*scale*(Real.exp (t/2)-1)*x (.inr 2))
          (2*scale*x (.inr 2)) 0
        exact ((((hp.sub_const 1).const_mul (4*scale)).mul_const (x (.inr 2))).const_add
          (x (.inr 3))).congr_deriv (by ring)
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt 0 hd

def rotatedFlow (c : ℝ) (hc : c ≠ 0) (θ t : ℝ) (x : Space) : Space :=
  flowEquiv c hc θ (flow t (flowEquiv c hc (-θ) x))

def rotatedVelocity (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) : Space :=
  flowEquiv c hc θ (velocity (flowEquiv c hc (-θ) x))

theorem rotatedFlow_zero (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) :
    rotatedFlow c hc θ 0 x = x := by
  rw [rotatedFlow,flow_zero,KFCausalNormalizedChargeFlow.flow_compose,add_neg_cancel,
    KFCausalNormalizedChargeFlow.flow_zero]

theorem rotatedFlow_derivative (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) :
    HasDerivAt (fun t => rotatedFlow c hc θ t x) (rotatedVelocity c hc θ x) 0 :=
  (linearFlow c hc θ).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (flow_derivative_zero (flowEquiv c hc (-θ) x))

theorem rotatedVelocity_quarters (c : ℝ) (hc : c ≠ 0) (x : Space) :
    rotatedVelocity c hc 0 x + rotatedVelocity c hc (Real.pi/2) x +
      rotatedVelocity c hc Real.pi x + rotatedVelocity c hc (-Real.pi/2) x = 0 := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [rotatedVelocity,velocity,KFCausalNormalizedChargeFlow.flow_apply,
      KFCausalNormalizedChargeFlow.dilate,KFCausalPairedRotation.rotate,
      show -Real.pi/2 = -(Real.pi/2) by ring,Real.sin_neg,Real.cos_neg] <;>
    field_simp <;> ring

def differential (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (f : Space → ℂ) (x : Space) : ℂ :=
  (fderiv ℝ f x) (rotatedVelocity c hc θ x)

theorem expression_derivative (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (f : Space → ℂ)
    (x : Space) (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t => f (rotatedFlow c hc θ t x)) (differential c hc θ f x) 0 := by
  have hd : HasFDerivAt f (fderiv ℝ f x) (rotatedFlow c hc θ 0 x) := by
    rw [rotatedFlow_zero]
    exact hf.hasFDerivAt
  exact hd.comp_hasDerivAt 0 (rotatedFlow_derivative c hc θ x)

theorem differential_quarters (c : ℝ) (hc : c ≠ 0) (f : Space → ℂ) (x : Space) :
    differential c hc 0 f x + differential c hc (Real.pi/2) f x +
      differential c hc Real.pi f x + differential c hc (-Real.pi/2) f x = 0 := by
  simp only [differential,← map_add,rotatedVelocity_quarters,map_zero]

#print axioms flow_derivative_zero
#print axioms rotatedFlow_zero
#print axioms rotatedFlow_derivative
#print axioms rotatedVelocity_quarters
#print axioms expression_derivative
#print axioms differential_quarters
end
end UnifiedTheory.Audit.KFCausalChargeShearRotatedVelocity
