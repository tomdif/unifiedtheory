/- Regularization at the current time gives an exact moving-observable
identity. The quantum part is a bounded physical resolvent commutator;
the explicitly derived time correction is small on energy-bounded states. -/
import UnifiedTheory.Audit.KFCausalClockFloorMovingResolvent
import UnifiedTheory.Audit.KFCausalFormResolventCommutator
import UnifiedTheory.Audit.KFCausalClockFloorResolventEhrenfest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorMovingResolventEhrenfest
noncomputable section
open scoped ComplexConjugate
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorResolventTests
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolvent (rateCorrection)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "R" => regularizer ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k

def characteristic (a : ℝ) (D : Hilbert →L[ℂ] Hilbert) (s t : ℝ) (w : V₀) : ℂ :=
  KFCausalClockFloorResolventEhrenfest.characteristic ε hε h hne hh m g k a t D s t w

def boundedRate (a : ℝ) (D : Hilbert →L[ℂ] Hilbert) (s t : ℝ) (w : V₀) : ℂ :=
  coefficient h*(a:ℂ)*inner ℂ (U s t (J w))
    (D (R a t (U s t (J w)))-R a t (D (U s t (J w))))

def correctionRate (a : ℝ) (D : Hilbert →L[ℂ] Hilbert) (s t : ℝ) (w : V₀) : ℂ :=
  inner ℂ (U s t (J w)) (rateCorrection ε hε h hne hh m g k a t D (U s t (J w)))

theorem reference_form_hermitian (t : ℝ) (x y : V₀) :
    inner ℂ x (Q t y) = conj (inner ℂ y (Q t x)) := by
  let L := referenceEnergyMap ε hε h hne hh m g k t
  have hi : inner ℂ (L x) (L y) = conj (inner ℂ (L y) (L x)) :=
    (inner_conj_symm (𝕜 := ℂ) (L x) (L y)).symm
  exact (referenceEnergyMap_pairing ε hε h hne hh m g k t x y).symm.trans
    (hi.trans (congrArg conj (referenceEnergyMap_pairing ε hε h hne hh m g k t y x)))

theorem formRate_eq_boundedRate (a : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert)
    (s t : ℝ) (w : V₀) :
    KFCausalClockFloorResolventEhrenfest.exactRate ε hε h hne hh m g k a t D s t w =
      boundedRate ε hε h hne hh m g k a D s t w := by
  have hp := KFCausalFormResolventCommutator.pairing J (Q t)
    (regularizerLift ε hε h hne hh m g k a t) (R a t) D a
    (reference_form_hermitian ε hε h hne hh m g k t)
    (regularizer_symmetric ε hε h hne hh m g k a t ha)
    (regularizer_variational ε hε h hne hh m g k a t ha) (F s t w)
  simpa only [KFCausalClockFloorResolventEhrenfest.exactRate,formLift,
    ContinuousLinearMap.comp_apply,boundedRate,evolution_embedding,mul_assoc] using
      congrArg (fun z : ℂ => coefficient h*z) hp

theorem expectation_derivative (a : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert)
    (s t : ℝ) (w : V₀) :
    HasDerivAt (fun u => characteristic ε hε h hne hh m g k a D s u w)
      (boundedRate ε hε h hne hh m g k a D s t w+
        correctionRate ε hε h hne hh m g k a D s t w) t := by
  have hf := KFCausalClockFloorResolventEhrenfest.expectation_derivative
    ε hε h hne hh m g k a t D ha s t w
  have hd := KFCausalMovingObservableDerivative.expectation_derivative
    (fun u => U s u (J w)) (fun u => observable ε hε h hne hh m g k a u D)
    (rateCorrection ε hε h hne hh m g k a t D) t
    (KFCausalClockFloorResolventEhrenfest.exactRate ε hε h hne hh m g k a t D s t w)
    (evolution_strong_continuous ε hε h hne hh m g k s (J w)).continuousAt
    (KFCausalClockFloorMovingResolvent.observable_derivative ε hε h hne hh m g k a t ha D) hf
  exact hd.congr_deriv (congrArg (fun z : ℂ => z+correctionRate ε hε h hne hh m g k a D s t w)
    (formRate_eq_boundedRate ε hε h hne hh m g k a ha D s t w))

theorem boundedRate_continuous (a : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert)
    (s : ℝ) (w : V₀) : Continuous (fun t => boundedRate ε hε h hne hh m g k a D s t w) := by
  have hu := evolution_strong_continuous ε hε h hne hh m g k s (J w)
  have hr := (shiftedResolvent_continuous ε hε h hne hh m g k a ha).const_smul a
  exact (continuous_const (y := coefficient h*(a:ℂ))).mul
    (hu.inner (𝕜 := ℂ) ((D.continuous.comp (hr.clm_apply hu)).sub
      (hr.clm_apply (D.continuous.comp hu))))

theorem correctionRate_continuous (a : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert)
    (s : ℝ) (w : V₀) : Continuous (fun t => correctionRate ε hε h hne hh m g k a D s t w) :=
  (evolution_strong_continuous ε hε h hne hh m g k s (J w)).inner (𝕜 := ℂ)
    ((KFCausalClockFloorMovingResolvent.correction_continuous ε hε h hne hh m g k a ha D).clm_apply
      (evolution_strong_continuous ε hε h hne hh m g k s (J w)))

theorem expectation_integral (a : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert)
    (s b c : ℝ) (w : V₀) :
    (∫ t in b..c, boundedRate ε hε h hne hh m g k a D s t w+
      correctionRate ε hε h hne hh m g k a D s t w) =
        characteristic ε hε h hne hh m g k a D s c w-
          characteristic ε hε h hne hh m g k a D s b w :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => expectation_derivative ε hε h hne hh m g k a ha D s t w)
    (((boundedRate_continuous ε hε h hne hh m g k a ha D s w).add
      (correctionRate_continuous ε hε h hne hh m g k a ha D s w)).intervalIntegrable _ _)

theorem boundedRate_integral (a : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert)
    (s b c : ℝ) (w : V₀) :
    (∫ t in b..c, boundedRate ε hε h hne hh m g k a D s t w) =
      characteristic ε hε h hne hh m g k a D s c w-
        characteristic ε hε h hne hh m g k a D s b w-
          ∫ t in b..c, correctionRate ε hε h hne hh m g k a D s t w := by
  have hi := expectation_integral ε hε h hne hh m g k a ha D s b c w
  rw [intervalIntegral.integral_add
    ((boundedRate_continuous ε hε h hne hh m g k a ha D s w).intervalIntegrable b c)
    ((correctionRate_continuous ε hε h hne hh m g k a ha D s w).intervalIntegrable b c)] at hi
  exact eq_sub_of_add_eq hi

theorem correctionRate_bound (a : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert)
    (s t : ℝ) (w : V₀) :
    ‖correctionRate ε hε h hne hh m g k a D s t w‖ ≤
      2*‖D‖*‖J w‖*Real.sqrt (timeEnergy ε hε h hne hh m g k t (F s t w)/a) := by
  simpa only [correctionRate,evolution_embedding,formFlow_physical_norm] using
    KFCausalClockFloorMovingResolvent.correction_bound ε hε h hne hh m g k a t ha D (F s t w)

#print axioms reference_form_hermitian
#print axioms formRate_eq_boundedRate
#print axioms expectation_derivative
#print axioms boundedRate_continuous
#print axioms correctionRate_continuous
#print axioms expectation_integral
#print axioms boundedRate_integral
#print axioms correctionRate_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorMovingResolventEhrenfest
