/- The actual finite-energy evolution in simultaneous chart and squeeze
coordinates. Both first-generator terms are derived on the constructed
dense common test class; no generator moment of the state is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorCombinedReference
import UnifiedTheory.Audit.KFCausalClockFloorCombinedTestDensity
import UnifiedTheory.Audit.KFCausalClockFloorGaugeWeakDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorCombinedDynamics
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCombinedUnitary
open UnifiedTheory.Audit.KFCausalClockFloorCombinedReference
open UnifiedTheory.Audit.KFCausalClockFloorCombinedOutput (weightedPairing balancedPairing balanced_output_pairing)
open UnifiedTheory.Audit.KFCausalClockFloorGaugeDerivative (chartOperator)
open UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator (squeezeMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow formFlow_initial)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity (referenceFormOperator)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)

private theorem expand_pairing {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a : ℝ) (P : ℂ) (f zQ zA : H) :
    P+inner ℂ f ((a:ℂ) • zA-(2:ℂ) • zQ) = P+(a:ℂ)*inner ℂ f zA-2*inner ℂ f zQ := by
  rw [inner_sub_right,inner_smul_right,inner_smul_right]
  ring

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m q k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m q k 0
local notation "J" => embedding ε hε h hne hh m q k 0
local notation "A" => energyOutput ε hε h hne hh m q k 0
local notation "R" => formAction ε hε h hne hh m q k
local notation "Q" => referenceFormOperator ε hε h hne hh m q k
local notation "F" => formFlow ε hε h hne hh m q k
local notation "U" => evolution ε hε h hne hh m q k

def transformedState (a s t : ℝ) (f : Hilbert) : Hilbert := combined ε h a (-t) (U s t f)
def transformedFormState (a s t : ℝ) (w : V) : V := R a (-t) (F s t w)
def transformedPairing (a t : ℝ) (u v : V) (zQ zA : Hilbert) : ℂ :=
  weightedPairing (a*t) t (A u) (A v)+inner ℂ (J u) ((a:ℂ) • zA-(2:ℂ) • zQ)

theorem transformed_embedding (a s t : ℝ) (w : V) :
    J (transformedFormState ε hε h hne hh m q k a s t w) =
      transformedState ε hε h hne hh m q k a s t (J w) := by
  unfold transformedFormState transformedState
  rw [formAction_embedding,evolution_embedding]

theorem transformed_initial (a s : ℝ) (w : V) :
    transformedState ε hε h hne hh m q k a s s (J w) = combined ε h a (-s) (J w) := by
  simp only [transformedState,evolution_embedding,formFlow_initial]

theorem transformed_norm (a s t : ℝ) (f : Hilbert) :
    ‖transformedState ε hε h hne hh m q k a s t f‖ = ‖f‖ := by
  unfold transformedState
  rw [LinearIsometryEquiv.norm_map,evolution_norm]

theorem transformed_defect_norm (a s t : ℝ) (f : Hilbert) :
    ‖KFCausalClockFloorDefectOperator.defectOperator ε hε
      (transformedState ε hε h hne hh m q k a s t f)‖ =
    ‖KFCausalClockFloorDefectOperator.defectOperator ε hε (U s t f)‖ :=
  combined_defect_norm ε hε h a (-t) (U s t f)

theorem transformedPairing_explicit (a t : ℝ) (u v : V) (zQ zA : Hilbert) :
    transformedPairing ε hε h hne hh m q k a t u v zQ zA =
      weightedPairing (a*t) t (A u) (A v)+(a:ℂ)*inner ℂ (J u) zA-2*inner ℂ (J u) zQ :=
  expand_pairing a (weightedPairing (a*t) t (A u) (A v)) (J u) zQ zA

theorem transformed_weak_derivative (a s t : ℝ) (w v : V) (zQ zA : Hilbert)
    (hQ : (J v,zQ) ∈ (chartOperator ε).graph) (hA : (J v,zA) ∈ (squeezeMomentum h).graph) :
    HasDerivAt (fun b => inner ℂ (transformedState ε hε h hne hh m q k a s b (J w)) (J v))
      (coefficient h*transformedPairing ε hε h hne hh m q k a t
        (transformedFormState ε hε h hne hh m q k a s t w) v zQ zA) t := by
  have hf := KFCausalClockFloorGaugeWeakDynamics.physical_pairing_derivative
    ε hε h hne hh m q k s t w (R a t v)
  simp only [formAction_embedding] at hf
  let z : Hilbert := (a:ℂ) • zA-(2:ℂ) • zQ
  have hd := KFCausalMovingTestDerivative.pairing_derivative
    (fun b => U s b (J w)) (fun b => combined ε h a b (J v)) t
    (coefficient h • combined ε h a t z)
    (coefficient h*inner ℂ (F s t w) (Q t (R a t v)))
    (evolution_strong_continuous ε hε h hne hh m q k s (J w)).continuousAt
    (combined_derivative ε h hne a t (J v) zQ zA hQ hA) hf
  have he : coefficient h*inner ℂ (F s t w) (Q t (R a t v))+
      inner ℂ (U s t (J w)) (coefficient h • combined ε h a t z) =
      coefficient h*transformedPairing ε hε h hne hh m q k a t
        (transformedFormState ε hε h hne hh m q k a s t w) v zQ zA := by
    let P : ℂ := weightedPairing (a*t) t (A (R a (-t) (F s t w))) (A v)
    let Z : ℂ := inner ℂ (transformedState ε hε h hne hh m q k a s t (J w)) z
    have hP : inner ℂ (F s t w) (Q t (R a t v)) = P :=
      reference_mixed_pairing ε hε h hne hh m q k a t (F s t w) v
    have hZ : inner ℂ (U s t (J w)) (combined ε h a t z) = Z :=
      (combined_dual ε h hne a t (U s t (J w)) z).symm
    have hpair : transformedPairing ε hε h hne hh m q k a t
        (transformedFormState ε hε h hne hh m q k a s t w) v zQ zA = P+Z :=
      congrArg (fun x : Hilbert => P+inner ℂ x z)
        (transformed_embedding ε hε h hne hh m q k a s t w)
    have hb : inner ℂ (U s t (J w)) (coefficient h • combined ε h a t z) = coefficient h*Z :=
      (inner_smul_right (𝕜 := ℂ) (E := Hilbert) (U s t (J w)) (combined ε h a t z) (coefficient h)).trans
        (congrArg (fun y : ℂ => coefficient h*y) hZ)
    exact (congrArg₂ (fun x y : ℂ => x+y) (congrArg (fun y : ℂ => coefficient h*y) hP) hb).trans
      ((mul_add (coefficient h) P Z).symm.trans (congrArg (fun y : ℂ => coefficient h*y) hpair.symm))
  have hfun : (fun b => inner ℂ (transformedState ε hε h hne hh m q k a s b (J w)) (J v)) =
      (fun b => inner ℂ (U s b (J w)) (combined ε h a b (J v))) :=
    funext (fun b => combined_dual ε h hne a b (U s b (J w)) (J v))
  exact (hd.congr_deriv he).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)

theorem balanced_form_pairing (t : ℝ) (u v : V) (zQ zA : Hilbert) :
    transformedPairing ε hε h hne hh m q k (-1/2) t u v zQ zA =
      balancedPairing t (A u) (A v)-(1/2:ℂ)*inner ℂ (J u) zA-2*inner ℂ (J u) zQ := by
  have he := transformedPairing_explicit ε hε h hne hh m q k (-1/2) t u v zQ zA
  have hb := congrArg (fun P : ℂ => P+(((-1/2:ℝ):ℂ))*inner ℂ (J u) zA-2*inner ℂ (J u) zQ)
    (balanced_output_pairing t (A u) (A v))
  have ha (P ZA ZQ : ℂ) : P+(((-1/2:ℝ):ℂ))*ZA-2*ZQ = P-(1/2:ℂ)*ZA-2*ZQ := by
    push_cast
    ring
  exact he.trans (hb.trans (ha _ _ _))

theorem balanced_weak_derivative (s t : ℝ) (w v : V) (zQ zA : Hilbert)
    (hQ : (J v,zQ) ∈ (chartOperator ε).graph) (hA : (J v,zA) ∈ (squeezeMomentum h).graph) :
    HasDerivAt (fun b => inner ℂ (transformedState ε hε h hne hh m q k (-1/2) s b (J w)) (J v))
      (coefficient h*(balancedPairing t
        (A (transformedFormState ε hε h hne hh m q k (-1/2) s t w)) (A v)-
          (1/2:ℂ)*inner ℂ (J (transformedFormState ε hε h hne hh m q k (-1/2) s t w)) zA-
          2*inner ℂ (J (transformedFormState ε hε h hne hh m q k (-1/2) s t w)) zQ)) t := by
  simpa only [balanced_form_pairing] using
    transformed_weak_derivative ε hε h hne hh m q k (-1/2) s t w v zQ zA hQ hA

#print axioms transformed_embedding
#print axioms transformed_initial
#print axioms transformed_norm
#print axioms transformed_defect_norm
#print axioms transformedPairing_explicit
#print axioms transformed_weak_derivative
#print axioms balanced_form_pairing
#print axioms balanced_weak_derivative
end
end UnifiedTheory.Audit.KFCausalClockFloorCombinedDynamics
