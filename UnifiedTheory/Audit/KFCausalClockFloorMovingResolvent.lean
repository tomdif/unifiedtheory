/- The scaled averaged resolvent has an operator-norm time derivative.
Its action on a form state is bounded by sqrt(energy/scale), which controls
the correction from regularizing an observable at the current time. -/
import UnifiedTheory.Audit.KFCausalClockFloorResolventEnergyControl
import UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorMovingResolvent
noncomputable section
open scoped ComplexConjugate
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDerivative
open UnifiedTheory.Audit.KFCausalClockFloorResolventTests
open UnifiedTheory.Audit.KFCausalClockFloorResolventEnergyControl
open UnifiedTheory.Audit.KFCausalSandwichCalculus (sandwichMap)
open UnifiedTheory.Audit.KFCausalBoundedFormCurve (gram)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "R" => regularizer ε hε h hne hh m g k
local notation "P" => referenceInverse ε hε h hne hh m g k
local notation "G" => growingMap ε hε h hne hh m g k
local notation "T" => growingLift ε hε h hne hh m g k
local notation "E" => timeEnergy ε hε h hne hh m g k

def derivative (a t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  a • averagedResolventDerivative ε hε h hne hh m g k a t

theorem regularizer_derivative (a t : ℝ) (ha : 0 < a) :
    HasDerivAt (R a) (derivative ε hε h hne hh m g k a t) t :=
  (averagedResolvent_derivative ε hε h hne hh m g k a t ha).const_smul a

theorem derivative_continuous (a : ℝ) (ha : 0 < a) :
    Continuous (derivative ε hε h hne hh m g k a) :=
  (averagedResolvent_derivative_continuous ε hε h hne hh m g k a ha).const_smul a

theorem derivative_sandwich (a t : ℝ) :
    derivative ε hε h hne hh m g k a t =
      a • sandwichMap J (-(P a t*((2*Real.exp (2*t)) • gram G)*P a t)) :=
  congrArg (fun B : Hilbert →L[ℂ] Hilbert => a • B)
    (averagedResolventDerivative_eq ε hε h hne hh m g k a t)

theorem derivative_pairing (a t : ℝ) (ha : 0 < a) (f z : Hilbert) :
    inner ℂ (derivative ε hε h hne hh m g k a t f) z =
      -((2/a:ℝ):ℂ)*inner ℂ (T a t f) (T a t z) :=
  (congrArg (fun B : Hilbert →L[ℂ] Hilbert => inner ℂ (B f) z)
    (derivative_sandwich ε hε h hne hh m g k a t)).trans
      (KFCausalMovingSandwichCalculus.scaled_gram_pairing J (P a t) G
        (referenceInverse_inner_symm ε hε h hne hh m g k a t ha) a t ha f z)

theorem derivative_symmetric (a t : ℝ) (ha : 0 < a) (f z : Hilbert) :
    inner ℂ (derivative ε hε h hne hh m g k a t f) z =
      inner ℂ f (derivative ε hε h hne hh m g k a t z) := by
  have hc := congrArg conj (derivative_pairing ε hε h hne hh m g k a t ha z f)
  simp only [map_mul,map_neg,Complex.conj_ofReal,inner_conj_symm] at hc
  exact (derivative_pairing ε hε h hne hh m g k a t ha f z).trans hc.symm

theorem derivative_error_square (a t : ℝ) (ha : 0 < a) (x : V₀) :
    ‖derivative ε hε h hne hh m g k a t (J x)‖^2 ≤ E t x/a :=
  KFCausalFormResolventEnergyBounds.gram_derivative_square
    (derivative ε hε h hne hh m g k a t) (T a t) a ha (J x) (E t x)
    (timeEnergy_nonneg ε hε h hne hh m g k t x)
    (derivative_pairing ε hε h hne hh m g k a t ha (J x))
    (growingLift_form_bound ε hε h hne hh m g k a t ha x)
    (growingLift_square_bound ε hε h hne hh m g k a t ha)

theorem derivative_error_norm (a t : ℝ) (ha : 0 < a) (x : V₀) :
    ‖derivative ε hε h hne hh m g k a t (J x)‖ ≤ Real.sqrt (E t x/a) :=
  (Real.le_sqrt (norm_nonneg _) (div_nonneg
    (timeEnergy_nonneg ε hε h hne hh m g k t x) ha.le)).mpr
      (derivative_error_square ε hε h hne hh m g k a t ha x)

theorem derivative_norm_bound (a t : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖derivative ε hε h hne hh m g k a t f‖ ≤ ‖f‖/2 := by
  have hs := KFCausalFormResolventEnergyBounds.gram_derivative_square
    (derivative ε hε h hne hh m g k a t) (T a t) a ha f (a/4*‖f‖^2)
    (by positivity) (derivative_pairing ε hε h hne hh m g k a t ha f)
    (growingLift_square_bound ε hε h hne hh m g k a t ha f)
    (growingLift_square_bound ε hε h hne hh m g k a t ha)
  have he : (a/4*‖f‖^2)/a = ‖f‖^2/4 := by field_simp
  rw [he] at hs
  nlinarith [norm_nonneg f,norm_nonneg (derivative ε hε h hne hh m g k a t f)]

theorem derivative_opNorm (a t : ℝ) (ha : 0 < a) :
    ‖derivative ε hε h hne hh m g k a t‖ ≤ 1/2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  exact (derivative_norm_bound ε hε h hne hh m g k a t ha f).trans_eq (by ring)

def rateCorrection (a t : ℝ) (D : Hilbert →L[ℂ] Hilbert) : Hilbert →L[ℂ] Hilbert :=
  KFCausalMovingSandwichCalculus.correction (R a t) (derivative ε hε h hne hh m g k a t) D

theorem observable_derivative (a t : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert) :
    HasDerivAt (fun u => observable ε hε h hne hh m g k a u D)
      (rateCorrection ε hε h hne hh m g k a t D) t :=
  KFCausalMovingSandwichCalculus.sandwich_derivative (R a)
    (derivative ε hε h hne hh m g k a t) D t (regularizer_derivative ε hε h hne hh m g k a t ha)

theorem correction_continuous (a : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert) :
    Continuous (fun t => rateCorrection ε hε h hne hh m g k a t D) := by
  have hR := (shiftedResolvent_continuous ε hε h hne hh m g k a ha).const_smul a
  have hS := derivative_continuous ε hε h hne hh m g k a ha
  exact (hS.clm_comp (continuous_const.clm_comp hR)).add
    (hR.clm_comp (continuous_const.clm_comp hS))

theorem correction_bound (a t : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert) (x : V₀) :
    ‖inner ℂ (J x) (rateCorrection ε hε h hne hh m g k a t D (J x))‖ ≤
      2*‖D‖*‖J x‖*Real.sqrt (E t x/a) := by
  have hb := KFCausalMovingSandwichCalculus.correction_bound (R a t)
    (derivative ε hε h hne hh m g k a t) D
    (regularizer_contraction ε hε h hne hh m g k a t ha)
    (regularizer_symmetric ε hε h hne hh m g k a t ha)
    (derivative_symmetric ε hε h hne hh m g k a t ha) (J x)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (derivative_error_norm ε hε h hne hh m g k a t ha x) (by positivity))

#print axioms regularizer_derivative
#print axioms derivative_continuous
#print axioms derivative_sandwich
#print axioms derivative_pairing
#print axioms derivative_symmetric
#print axioms derivative_error_square
#print axioms derivative_error_norm
#print axioms derivative_norm_bound
#print axioms derivative_opNorm
#print axioms observable_derivative
#print axioms correction_continuous
#print axioms correction_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorMovingResolvent
