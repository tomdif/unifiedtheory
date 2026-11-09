/- C1 time dependence of the full fixed-domain resolvent on its derived
admissible region. The inverse exists locally around every admissible time. -/
import UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
import UnifiedTheory.Audit.KFCausalPerturbedResolventCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorFixedResolventCurve
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorLiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "D" => referenceFormDerivative ε hε h hne hh m g k
local notation "P" => referenceInverse ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "S'" => transportDerivative ε hε h hne hh m g k
local notation "C" => connection ε hε h hne hh m g k
local notation "C'" => connectionDerivative ε hε h hne hh m g k
local notation "R" => schrodingerResolvent ε hε h hne hh m g k
local notation "R'" => KFCausalComplexMassCurve.derivative M Q D h
local notation "B" => baseResolvent ε hε h hne hh m g k
local notation "F" => fullResolvent ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k

def baseDerivative (a b s t : ℝ) : V →L[ℂ] V :=
  (P a s*D t)*(R b t*S a s t)+S a t s*(R' b t*S a s t+R b t*S' a s t)

def fullDerivative (a b s t : ℝ) : V →L[ℂ] V :=
  KFCausalPerturbedResolventCurve.derivative (B a b s t) (C a s t)
    (baseDerivative ε hε h hne hh m g k a b s t) (C' a s t)

theorem base_derivative (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (B a b s) (baseDerivative ε hε h hne hh m g k a b s t) t :=
  (transport_reverse_derivative ε hε h hne hh m g k a s t).mul
    ((KFCausalComplexMassCurve.resolvent_derivative M Q D h b t
      (referenceForm_derivative ε hε h hne hh m g k t)
      (complex_pencil_isUnit ε hε h hne hh m g k b t hb)).mul
      (transport_derivative ε hε h hne hh m g k a s t ha))

theorem base_continuous (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) : Continuous (B a b s) :=
  continuous_iff_continuousAt.mpr (fun t => (base_derivative ε hε h hne hh m g k a b s t ha hb).continuousAt)

theorem base_derivative_continuous (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (baseDerivative ε hε h hne hh m g k a b s) := by
  have hd := referenceForm_derivative_continuous ε hε h hne hh m g k
  have hs : Continuous (S a s) := continuous_iff_continuousAt.mpr
    (fun t => (transport_derivative ε hε h hne hh m g k a s t ha).continuousAt)
  have hu : Continuous (fun t => S a t s) := continuous_iff_continuousAt.mpr
    (fun t => (transport_reverse_derivative ε hε h hne hh m g k a s t).continuousAt)
  have hr : Continuous (R b) := continuous_iff_continuousAt.mpr
    (fun t => (KFCausalComplexMassCurve.resolvent_derivative M Q D h b t
      (referenceForm_derivative ε hε h hne hh m g k t)
      (complex_pencil_isUnit ε hε h hne hh m g k b t hb)).continuousAt)
  have hr' := KFCausalComplexMassCurve.derivative_continuous M Q D h b
    (continuous_iff_continuousAt.mpr
      (fun t => (referenceForm_derivative ε hε h hne hh m g k t).continuousAt)) hd
    (fun t => complex_pencil_isUnit ε hε h hne hh m g k b t hb)
  have hs' : Continuous (S' a s) :=
    (((referenceInverse_continuous ε hε h hne hh m g k a ha).mul hd).mul hs).neg
  exact ((continuous_const.mul hd).mul (hr.mul hs)).add
    (hu.mul ((hr'.mul hs).add (hr.mul hs')))

theorem connection_derivative_continuous (a s : ℝ) (ha : 0 < a) : Continuous (C' a s) := by
  have hd := referenceForm_derivative_continuous ε hε h hne hh m g k
  have hs : Continuous (S a s) := continuous_iff_continuousAt.mpr
    (fun t => (transport_derivative ε hε h hne hh m g k a s t ha).continuousAt)
  have hs' : Continuous (S' a s) :=
    (((referenceInverse_continuous ε hε h hne hh m g k a ha).mul hd).mul hs).neg
  exact ((continuous_const.mul (hd.const_smul (2:ℝ))).mul hs).add
    ((continuous_const.mul hd).mul hs')

theorem full_resolvent_derivative (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbq : q a s t < b) : HasDerivAt (F a b s) (fullDerivative ε hε h hne hh m g k a b s t) t :=
  KFCausalPerturbedResolventCurve.resolvent_derivative (B a b s) (C a s)
    (baseDerivative ε hε h hne hh m g k a b s t) (C' a s t) t
    (base_derivative ε hε h hne hh m g k a b s t ha hb)
    (connection_derivative ε hε h hne hh m g k a s t ha)
    (connection_factor_isUnit ε hε h hne hh m g k a b s t ha hb hbq)

theorem full_derivative_continuousOn (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (fullDerivative ε hε h hne hh m g k a b s) {t | q a s t < b} :=
  KFCausalPerturbedResolventCurve.derivative_continuousOn (B a b s) (C a s)
    (baseDerivative ε hε h hne hh m g k a b s) (C' a s) _
    (base_continuous ε hε h hne hh m g k a b s ha hb)
    (continuous_iff_continuousAt.mpr
      (fun t => (connection_derivative ε hε h hne hh m g k a s t ha).continuousAt))
    (base_derivative_continuous ε hε h hne hh m g k a b s ha hb)
    (connection_derivative_continuous ε hε h hne hh m g k a s ha)
    (fun t ht => connection_factor_isUnit ε hε h hne hh m g k a b s t ha hb ht)

theorem full_approximation_derivative (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbq : q a s t < b) :
    HasDerivAt (fun r => fullApproximation ε hε h hne hh m g k a b s r)
      (b • (b • fullDerivative ε hε h hne hh m g k a b s t)) t :=
  (((full_resolvent_derivative ε hε h hne hh m g k a b s t ha hb hbq).const_smul b).sub_const 1).const_smul b

#print axioms base_derivative
#print axioms base_continuous
#print axioms base_derivative_continuous
#print axioms connection_derivative_continuous
#print axioms full_resolvent_derivative
#print axioms full_derivative_continuousOn
#print axioms full_approximation_derivative
end
end UnifiedTheory.Audit.KFCausalClockFloorFixedResolventCurve
