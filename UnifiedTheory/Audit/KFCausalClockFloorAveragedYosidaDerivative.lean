/- Operator-norm derivatives of the averaged resolvent and its bounded
Hamiltonian approximation, with an exact positive quadratic pairing. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida
import UnifiedTheory.Audit.KFCausalSplitTargetEnergyIdentities

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDerivative
noncomputable section
open UnifiedTheory.Audit.KFCausalSplitTargetShiftedForm
open UnifiedTheory.Audit.KFCausalSandwichCalculus
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida

def averagedResolventDerivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum a t : ℝ) :
    Hilbert →L[ℂ] Hilbert :=
  (embedding ε hε hbar hh hbound mass2 quartic vacuum 0).comp
    ((referenceInverseDerivative ε hε hbar hh hbound mass2 quartic vacuum a t).comp (referenceAdjoint ε hε hbar hh hbound mass2 quartic vacuum))

theorem averagedResolventDerivative_eq (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum a t : ℝ) :
    averagedResolventDerivative ε hε hbar hh hbound mass2 quartic vacuum a t =
      sandwichMap (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
        (embedding ε hε hbar hh hbound mass2 quartic vacuum 0) (referenceInverseDerivative ε hε hbar hh hbound mass2 quartic vacuum a t) := by
  have he := sandwichMap_apply (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
    (embedding ε hε hbar hh hbound mass2 quartic vacuum 0) (referenceInverseDerivative ε hε hbar hh hbound mass2 quartic vacuum a t)
  exact he.symm

theorem averagedResolvent_derivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) :
    HasDerivAt (shiftedResolvent ε hε hbar hh hbound mass2 quartic vacuum a)
      (averagedResolventDerivative ε hε hbar hh hbound mass2 quartic vacuum a t) t := by
  have hd := sandwich_derivative (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
    (embedding ε hε hbar hh hbound mass2 quartic vacuum 0) (referenceInverse ε hε hbar hh hbound mass2 quartic vacuum a)
    (referenceInverseDerivative ε hε hbar hh hbound mass2 quartic vacuum a t) t
    (referenceInverse_derivative ε hε hbar hh hbound mass2 quartic vacuum a t ha)
  simpa only [sandwichMap_apply] using hd

theorem averagedResolvent_derivative_continuous (ε : ℝ) (hε : 0 < ε)
    (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum a : ℝ) (ha : 0 < a) :
    Continuous (averagedResolventDerivative ε hε hbar hh hbound mass2 quartic vacuum a) :=
  continuous_const.clm_comp
    ((referenceInverse_derivative_continuous ε hε hbar hh hbound mass2 quartic vacuum a ha).clm_comp continuous_const)

def yosidaDerivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum a t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  -(a • (a • averagedResolventDerivative ε hε hbar hh hbound mass2 quartic vacuum a t))

theorem averagedYosida_derivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) :
    HasDerivAt (averagedYosida ε hε hbar hh hbound mass2 quartic vacuum a) (yosidaDerivative ε hε hbar hh hbound mass2 quartic vacuum a t) t :=
  (((averagedResolvent_derivative ε hε hbar hh hbound mass2 quartic vacuum a t ha).const_smul a).const_smul a).const_sub
    (a • ContinuousLinearMap.id ℂ Hilbert)

theorem averagedYosida_derivative_continuous (ε : ℝ) (hε : 0 < ε)
    (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum a : ℝ) (ha : 0 < a) : Continuous (yosidaDerivative ε hε hbar hh hbound mass2 quartic vacuum a) :=
  (((averagedResolvent_derivative_continuous ε hε hbar hh hbound mass2 quartic vacuum a ha).const_smul a).const_smul a).neg

theorem referenceInverse_inner_symm (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a)
    (u v : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    inner ℂ (referenceInverse ε hε hbar hh hbound mass2 quartic vacuum a t u) v =
      inner ℂ u (referenceInverse ε hε hbar hh hbound mass2 quartic vacuum a t v) :=
  inverse_inner_symm _ (referenceShift_isUnit ε hε hbar hh hbound mass2 quartic vacuum a t ha)
    (shiftForm_inner_symm _ _ _ a t) u v

theorem yosidaDerivative_sandwich (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum a t : ℝ) :
    yosidaDerivative ε hε hbar hh hbound mass2 quartic vacuum a t = a • (a •
      sandwichMap (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
        (embedding ε hε hbar hh hbound mass2 quartic vacuum 0)
        (referenceInverse ε hε hbar hh hbound mass2 quartic vacuum a t * referenceFormDerivative ε hε hbar hh hbound mass2 quartic vacuum t *
          referenceInverse ε hε hbar hh hbound mass2 quartic vacuum a t)) := by
  have he := sandwich_neg_scale (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
    (embedding ε hε hbar hh hbound mass2 quartic vacuum 0)
    (referenceInverse ε hε hbar hh hbound mass2 quartic vacuum a t * referenceFormDerivative ε hε hbar hh hbound mass2 quartic vacuum t *
      referenceInverse ε hε hbar hh hbound mass2 quartic vacuum a t) a
  exact he

theorem yosidaDerivative_diagonal (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a)
    (f : Hilbert) :
    (inner ℂ (yosidaDerivative ε hε hbar hh hbound mass2 quartic vacuum a t f) f).re =
      a^2*(2*Real.exp (2*t)*‖growingMap ε hε hbar hh hbound mass2 quartic vacuum
        (resolventFormLift ε hε hbar hh hbound mass2 quartic vacuum a t f)‖^2) := by
  have hpair : (inner ℂ (sandwichMap (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0)
      (referenceInverse ε hε hbar hh hbound mass2 quartic vacuum a t * referenceFormDerivative ε hε hbar hh hbound mass2 quartic vacuum t *
        referenceInverse ε hε hbar hh hbound mass2 quartic vacuum a t) f) f).re =
      (2*Real.exp (2*t))*‖growingMap ε hε hbar hh hbound mass2 quartic vacuum
        (resolventFormLift ε hε hbar hh hbound mass2 quartic vacuum a t f)‖^2 :=
    KFCausalSplitTargetEnergyIdentities.sandwich_gram_diagonal _ _ _ (referenceInverse_inner_symm ε hε hbar hh hbound mass2 quartic vacuum a t ha) _ f
  rw [yosidaDerivative_sandwich,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply,
    inner_smul_left_eq_smul,inner_smul_left_eq_smul]
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simpa only [pow_two,mul_assoc] using congrArg (fun z : ℝ => a*(a*z)) hpair

#print axioms averagedResolvent_derivative
#print axioms averagedResolvent_derivative_continuous
#print axioms averagedYosida_derivative
#print axioms averagedYosida_derivative_continuous
#print axioms referenceInverse_inner_symm
#print axioms yosidaDerivative_diagonal

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDerivative
