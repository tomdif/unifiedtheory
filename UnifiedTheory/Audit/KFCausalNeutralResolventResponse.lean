/- Uniform energy bounds and explicit linear response for the actual
neutral resolvent commutator. The error is O(|hbar| E), independently of
the positive resolvent scale. No classical limit of the leading term is assumed. -/
import UnifiedTheory.Audit.KFCausalFormResolventTestPairing
import UnifiedTheory.Audit.KFCausalNeutralOutputLinearResponse
import UnifiedTheory.Audit.KFCausalClockFloorMovingResolventEhrenfest
import UnifiedTheory.Audit.KFCausalNeutralWeightTime

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 120000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalNeutralResolventResponse
noncomputable section
open scoped ComplexConjugate
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity (referenceFormOperator)
open UnifiedTheory.Audit.KFCausalClockFloorResolventTests
open UnifiedTheory.Audit.KFCausalClockFloorResolventEnergyControl
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient action_dual)
open UnifiedTheory.Audit.KFCausalNeutralReferenceForm (formAction formAction_embedding)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates (action)
open UnifiedTheory.Audit.KFCausalNeutralTranslationPhysicalCommutator (speedBound)
open UnifiedTheory.Audit.KFCausalNeutralTranslationBounds (weightedLinear weightedQuadratic)
open UnifiedTheory.Audit.KFCausalNeutralWeightTime
open UnifiedTheory.Audit.KFCausalNeutralTranslationJointGraph (energyWeight_ne_zero)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "A" => regularizerLift ε hε h hne hh m g k
local notation "R" => regularizer ε hε h hne hh m g k
local notation "E" => timeEnergy ε hε h hne hh m g k
local notation "L" => referenceEnergyMap ε hε h hne hh m g k

def rate (a t v : ℝ) (f : Hilbert) : ℂ :=
  coefficient h*(a:ℂ)*inner ℂ f (action (h*v) (R a t f)-R a t (action (h*v) f))

def responseOutput (a t : ℝ) (f : Hilbert) : EnergyOutputSpace := L t (A a t f)

def linearRate (a t v : ℝ) (f : Hilbert) : ℂ :=
  KFCausalNeutralOutputLinearResponse.linearRate angleMeasure (energyWeight m g k 0) h v
    (responseOutput ε hε h hne hh m g k a t f)

def quadraticRate (a t v : ℝ) (f : Hilbert) : ℂ :=
  KFCausalNeutralOutputLinearResponse.quadraticRate angleMeasure (energyWeight m g k 0) h v
    (responseOutput ε hε h hne hh m g k a t f)

variable (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
include hm hg hk
local notation "F" => formAction ε hε h hne hh m g k hm hg hk 0

theorem rate_eq_form (a t v : ℝ) (ha : 0 < a) (f : Hilbert) :
    rate ε hε h hne hh m g k a t v f =
      KFCausalNeutralReferencePairing.rate ε hε h hne hh m g k hm hg hk t (h*v) (A a t f) := by
  have hp := KFCausalFormResolventTestPairing.pairing J (Q t) (A a t) (R a t)
    (action (h*v) : Hilbert →L[ℂ] Hilbert) (action (-(h*v)) : Hilbert →L[ℂ] Hilbert)
    (F (h*v)) (F (-(h*v))) a
    (regularizer_symmetric ε hε h hne hh m g k a t ha)
    (by intro x y; simpa only [neg_neg] using action_dual (-(h*v)) x y)
    (formAction_embedding ε hε h hne hh m g k hm hg hk 0 (h*v))
    (formAction_embedding ε hε h hne hh m g k hm hg hk 0 (-(h*v)))
    (regularizerLift_embedding ε hε h hne hh m g k a t)
    (regularizer_variational ε hε h hne hh m g k a t ha) f
  simpa only [rate,KFCausalNeutralReferencePairing.rate,mul_assoc] using
    (congrArg (fun z : ℂ => coefficient h*z) hp).symm

theorem rate_energy_bound (a t v H : ℝ) (ha : 0 < a) (hH : |h| ≤ H) (x : V₀) :
    ‖rate ε hε h hne hh m g k a t v (J x)‖ ≤ speedBound (energyWeight m g k 0) H v*E t x := by
  have hb := KFCausalNeutralReferencePairing.canonical_rate_bound
    ε hε h hne hh m g k hm hg hk t v H hH (A a t (J x))
  have hc := mul_le_mul_of_nonneg_left
    (regularizer_energy_contraction ε hε h hne hh m g k a t ha x)
    (speedBound_nonneg (energyWeight m g k 0) H v ((abs_nonneg h).trans hH))
  simp only [speedBound_time m g k 0 t] at hb
  exact (congrArg norm (rate_eq_form ε hε h hne hh m g k hm hg hk a t v ha (J x))).le.trans
    (hb.trans hc)

theorem rate_smoothing_bound (a t v H : ℝ) (ha : 0 < a) (hH : |h| ≤ H) (f : Hilbert) :
    ‖rate ε hε h hne hh m g k a t v f‖ ≤ speedBound (energyWeight m g k 0) H v*(a/4*‖f‖^2) := by
  have hb := KFCausalNeutralReferencePairing.canonical_rate_bound
    ε hε h hne hh m g k hm hg hk t v H hH (A a t f)
  have hc := mul_le_mul_of_nonneg_left
    (regularizer_energy_square ε hε h hne hh m g k a t ha f)
    (speedBound_nonneg (energyWeight m g k 0) H v ((abs_nonneg h).trans hH))
  simp only [speedBound_time m g k 0 t] at hb
  exact (congrArg norm (rate_eq_form ε hε h hne hh m g k hm hg hk a t v ha f)).le.trans
    (hb.trans hc)

theorem form_polynomial (t v : ℝ) (x : V₀) :
    KFCausalNeutralReferencePairing.rate ε hε h hne hh m g k hm hg hk t (h*v) x =
      KFCausalNeutralOutputLinearResponse.linearRate angleMeasure (energyWeight m g k t) h v (L t x)+
      KFCausalNeutralOutputLinearResponse.quadraticRate angleMeasure (energyWeight m g k t) h v (L t x) := by
  have he := KFCausalNeutralReferencePairing.rate_output ε hε h hne hh m g k hm hg hk t (h*v) x
  have hp := KFCausalNeutralOutputLinearResponse.normalized_energy_polynomial m g k t h v hne
    (energyWeight_ne_zero m g k t hm hg hk)
    (energyOutput ε hε h hne hh m g k t (formTransfer ε hε h hne hh m g k 0 t x))
  have hy := congrArg (fun y =>
    KFCausalNeutralOutputLinearResponse.linearRate angleMeasure (energyWeight m g k t) h v y+
    KFCausalNeutralOutputLinearResponse.quadraticRate angleMeasure (energyWeight m g k t) h v y)
      (referenceEnergyMap_apply ε hε h hne hh m g k t x)
  exact he.trans (hp.trans hy.symm)

theorem rate_polynomial (a t v : ℝ) (ha : 0 < a) (f : Hilbert) :
    rate ε hε h hne hh m g k a t v f =
      linearRate ε hε h hne hh m g k a t v f+quadraticRate ε hε h hne hh m g k a t v f := by
  have hp := form_polynomial ε hε h hne hh m g k hm hg hk t v (A a t f)
  exact (rate_eq_form ε hε h hne hh m g k hm hg hk a t v ha f).trans (hp.trans
    (congrArg₂ (fun x y : ℂ => x+y)
      (KFCausalNeutralOutputLinearResponse.linearRate_time angleMeasure m g k 0 t h v
        (responseOutput ε hε h hne hh m g k a t f))
      (KFCausalNeutralOutputLinearResponse.quadraticRate_time angleMeasure m g k 0 t h v
        (responseOutput ε hε h hne hh m g k a t f))))

omit hm hg hk in
theorem responseOutput_energy (a t : ℝ) (ha : 0 < a) (x : V₀) :
    ‖responseOutput ε hε h hne hh m g k a t (J x)‖^2 ≤ E t x :=
  (referenceEnergyMap_square ε hε h hne hh m g k t (A a t (J x))).le.trans
    (regularizer_energy_contraction ε hε h hne hh m g k a t ha x)

omit hm hg hk in
theorem linearRate_energy_bound (a t v : ℝ) (ha : 0 < a) (x : V₀) :
    ‖linearRate ε hε h hne hh m g k a t v (J x)‖ ≤
      2*|v| *‖weightedLinear (energyWeight m g k 0)‖*E t x := by
  exact (KFCausalNeutralOutputLinearResponse.linearRate_bound angleMeasure (energyWeight m g k 0)
    h v (responseOutput ε hε h hne hh m g k a t (J x))).trans
      (mul_le_mul_of_nonneg_left (responseOutput_energy ε hε h hne hh m g k a t ha x) (by positivity))

omit hm hg hk in
theorem quadraticRate_energy_bound (a t v : ℝ) (ha : 0 < a) (x : V₀) :
    ‖quadraticRate ε hε h hne hh m g k a t v (J x)‖ ≤
      2*|h| *|v|^2*‖weightedQuadratic (energyWeight m g k 0)‖*E t x := by
  exact (KFCausalNeutralOutputLinearResponse.quadraticRate_bound angleMeasure (energyWeight m g k 0)
    h v (responseOutput ε hε h hne hh m g k a t (J x))).trans
      (mul_le_mul_of_nonneg_left (responseOutput_energy ε hε h hne hh m g k a t ha x) (by positivity))

#print axioms rate_eq_form
#print axioms rate_energy_bound
#print axioms rate_smoothing_bound
#print axioms form_polynomial
#print axioms rate_polynomial
#print axioms responseOutput_energy
#print axioms linearRate_energy_bound
#print axioms quadraticRate_energy_bound
end
end UnifiedTheory.Audit.KFCausalNeutralResolventResponse
