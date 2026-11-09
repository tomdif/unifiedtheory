/- The physical resolvent and bounded homogeneous Hamiltonian have
operator-norm time derivatives. The Hamiltonian derivative has an exact
positive quadratic pairing in the reference form space. -/
import UnifiedTheory.Audit.KFCausalRegularizedYosida
import UnifiedTheory.Audit.KFCausalSandwichCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedYosidaDerivative
noncomputable section
open UnifiedTheory.Audit.KFCausalShiftedForm
open UnifiedTheory.Audit.KFCausalSandwichCalculus
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
open UnifiedTheory.Audit.KFCausalRegularizedFormRegularity
open UnifiedTheory.Audit.KFCausalRegularizedShiftedResolvent
open UnifiedTheory.Audit.KFCausalRegularizedYosida

def physicalResolventDerivative (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) :
    Hilbert →L[ℂ] Hilbert :=
  (embedding ε hε hbar coupling 0).comp
    ((referenceInverseDerivative ε hε hbar coupling a t).comp (referenceAdjoint ε hε hbar coupling))

theorem physicalResolventDerivative_eq (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) :
    physicalResolventDerivative ε hε hbar coupling a t =
      sandwichMap (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
        (embedding ε hε hbar coupling 0) (referenceInverseDerivative ε hε hbar coupling a t) := by
  have he := sandwichMap_apply (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (embedding ε hε hbar coupling 0) (referenceInverseDerivative ε hε hbar coupling a t)
  exact he.symm

theorem physicalResolvent_derivative (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) :
    HasDerivAt (shiftedResolvent ε hε hbar coupling a)
      (physicalResolventDerivative ε hε hbar coupling a t) t := by
  have hd := sandwich_derivative (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (embedding ε hε hbar coupling 0) (referenceInverse ε hε hbar coupling a)
    (referenceInverseDerivative ε hε hbar coupling a t) t
    (referenceInverse_derivative ε hε hbar coupling a t ha)
  simpa only [sandwichMap_apply] using hd

theorem physicalResolvent_derivative_continuous (ε : ℝ) (hε : 0 < ε)
    (hbar coupling a : ℝ) (ha : 0 < a) :
    Continuous (physicalResolventDerivative ε hε hbar coupling a) :=
  continuous_const.clm_comp
    ((referenceInverse_derivative_continuous ε hε hbar coupling a ha).clm_comp continuous_const)

def yosidaDerivative (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  -(a • (a • physicalResolventDerivative ε hε hbar coupling a t))

theorem homogeneousYosida_derivative (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) :
    HasDerivAt (homogeneousYosida ε hε hbar coupling a) (yosidaDerivative ε hε hbar coupling a t) t :=
  (((physicalResolvent_derivative ε hε hbar coupling a t ha).const_smul a).const_smul a).const_sub
    (a • ContinuousLinearMap.id ℂ Hilbert)

theorem homogeneousYosida_derivative_continuous (ε : ℝ) (hε : 0 < ε)
    (hbar coupling a : ℝ) (ha : 0 < a) : Continuous (yosidaDerivative ε hε hbar coupling a) :=
  (((physicalResolvent_derivative_continuous ε hε hbar coupling a ha).const_smul a).const_smul a).neg

theorem referenceInverse_inner_symm (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a)
    (u v : FormSpace ε hε hbar coupling 0) :
    inner ℂ (referenceInverse ε hε hbar coupling a t u) v =
      inner ℂ u (referenceInverse ε hε hbar coupling a t v) :=
  inverse_inner_symm _ (referenceShift_isUnit ε hε hbar coupling a t ha)
    (shiftForm_inner_symm _ _ _ a t) u v

theorem yosidaDerivative_sandwich (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) :
    yosidaDerivative ε hε hbar coupling a t = a • (a •
      sandwichMap (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
        (embedding ε hε hbar coupling 0)
        (referenceInverse ε hε hbar coupling a t * referenceFormDerivative ε hε hbar coupling t *
          referenceInverse ε hε hbar coupling a t)) := by
  have he := sandwich_neg_scale (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (embedding ε hε hbar coupling 0)
    (referenceInverse ε hε hbar coupling a t * referenceFormDerivative ε hε hbar coupling t *
      referenceInverse ε hε hbar coupling a t) a
  rw [yosidaDerivative,physicalResolventDerivative_eq ε hε hbar coupling a t]
  exact he

theorem yosidaDerivative_diagonal (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a)
    (f : Hilbert) :
    (inner ℂ (yosidaDerivative ε hε hbar coupling a t f) f).re =
      a^2*(2*Real.exp (2*t)*‖momentumMap ε hε hbar coupling
        (resolventFormLift ε hε hbar coupling a t f)‖^2) := by
  have hh : (inner ℂ (sandwichMap (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
      (embedding ε hε hbar coupling 0)
      (referenceInverse ε hε hbar coupling a t * referenceFormDerivative ε hε hbar coupling t *
        referenceInverse ε hε hbar coupling a t) f) f).re =
      (2*Real.exp (2*t))*‖momentumMap ε hε hbar coupling
        (resolventFormLift ε hε hbar coupling a t f)‖^2 :=
    sandwich_gram_diagonal _ _ _ (referenceInverse_inner_symm ε hε hbar coupling a t ha) _ f
  rw [yosidaDerivative_sandwich,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply,
    inner_smul_left_eq_smul,inner_smul_left_eq_smul]
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hh]
  ring

#print axioms physicalResolvent_derivative
#print axioms physicalResolvent_derivative_continuous
#print axioms homogeneousYosida_derivative
#print axioms homogeneousYosida_derivative_continuous
#print axioms referenceInverse_inner_symm
#print axioms yosidaDerivative_diagonal

end
end UnifiedTheory.Audit.KFCausalRegularizedYosidaDerivative
