/- The actual weak quantum equation in an affine-time squeeze frame.
The additional squeeze-generator term is derived on a dense test class;
no generator domain of the evolving state is required. -/
import UnifiedTheory.Audit.KFCausalClockFloorSqueezeMovingPairing
import UnifiedTheory.Audit.KFCausalClockFloorSqueezeTestDensity
import UnifiedTheory.Audit.KFCausalPairedSqueezeTimeDerivative
import UnifiedTheory.Audit.KFCausalClockFloorGaugeWeakDynamics
import UnifiedTheory.Audit.KFCausalPairedSqueezeClockCommutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSqueezeMovingDynamics
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport (transport)
open UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator (squeezeMomentum)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTimeDerivative (affine_time_derivative)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow formFlow_initial)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity (referenceFormOperator)
open UnifiedTheory.Audit.KFCausalClockFloorReferenceSqueeze
open UnifiedTheory.Audit.KFCausalClockFloorSqueezePairing (timeOutput)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeMovingPairing
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m q k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m q k 0
local notation "J" => embedding ε hε h hne hh m q k 0
local notation "R" => (fun r : ℝ => formAction ε hε h hne hh m q k r 0)
local notation "Q" => referenceFormOperator ε hε h hne hh m q k
local notation "F" => formFlow ε hε h hne hh m q k
local notation "U" => evolution ε hε h hne hh m q k
local notation "T" => timeOutput ε hε h hne hh m q k

def transformedState (a s t : ℝ) (f : Hilbert) : Hilbert := transport (-(a*t)) (U s t f)
def transformedFormState (a s t : ℝ) (w : V) : V := R (-(a*t)) (F s t w)
def transformedPairing (a t : ℝ) (u v : V) (z : Hilbert) : ℂ :=
  weightedPairing (a*t) (T t u) (T t v)+(a:ℂ)*inner ℂ (J u) z

theorem transformed_embedding (a s t : ℝ) (w : V) :
    J (transformedFormState ε hε h hne hh m q k a s t w) =
      transformedState ε hε h hne hh m q k a s t (J w) := by
  unfold transformedFormState transformedState
  rw [formAction_embedding,evolution_embedding]

theorem transformed_initial (a s : ℝ) (w : V) :
    transformedState ε hε h hne hh m q k a s s (J w) = transport (-(a*s)) (J w) := by
  simp only [transformedState,evolution_embedding,formFlow_initial]

theorem transformed_norm (a s t : ℝ) (f : Hilbert) :
    ‖transformedState ε hε h hne hh m q k a s t f‖ = ‖f‖ := by
  unfold transformedState
  rw [LinearIsometryEquiv.norm_map,evolution_norm]

theorem transformed_defect_norm (a s t : ℝ) (f : Hilbert) :
    ‖KFCausalClockFloorDefectOperator.defectOperator ε hε
      (transformedState ε hε h hne hh m q k a s t f)‖ =
    ‖KFCausalClockFloorDefectOperator.defectOperator ε hε (U s t f)‖ := by
  unfold transformedState
  rw [← KFCausalPairedSqueezeClockCommutation.defect_commutes,LinearIsometryEquiv.norm_map]

theorem transformed_weak_derivative (a s t : ℝ) (w v : V) (z : Hilbert)
    (hvz : (J v,z) ∈ (squeezeMomentum h).graph) :
    HasDerivAt (fun b => inner ℂ (transformedState ε hε h hne hh m q k a s b (J w)) (J v))
      (coefficient h*transformedPairing ε hε h hne hh m q k a t
        (transformedFormState ε hε h hne hh m q k a s t w) v z) t := by
  have hf := KFCausalClockFloorGaugeWeakDynamics.physical_pairing_derivative
    ε hε h hne hh m q k s t w (R (a*t) v)
  simp only [formAction_embedding] at hf
  have hd := KFCausalMovingTestDerivative.pairing_derivative
    (fun b => U s b (J w)) (fun b => transport (a*b) (J v)) t
    ((coefficient h*(a:ℂ)) • transport (a*t) z)
    (coefficient h*inner ℂ (F s t w) (Q t (R (a*t) v)))
    (evolution_strong_continuous ε hε h hne hh m q k s (J w)).continuousAt
    (affine_time_derivative h hne a t (J v) z hvz) hf
  have he : coefficient h*inner ℂ (F s t w) (Q t (R (a*t) v))+
      inner ℂ (U s t (J w)) ((coefficient h*(a:ℂ)) • transport (a*t) z) =
      coefficient h*transformedPairing ε hε h hne hh m q k a t
        (transformedFormState ε hε h hne hh m q k a s t w) v z := by
    let P : ℂ := weightedPairing (a*t) (T t (R (-(a*t)) (F s t w))) (T t v)
    let Z : ℂ := inner ℂ (transformedState ε hε h hne hh m q k a s t (J w)) z
    have hP : inner ℂ (F s t w) (Q t (R (a*t) v)) = P :=
      reference_mixed_pairing ε hε h hne hh m q k (a*t) t (F s t w) v
    have hZ : inner ℂ (U s t (J w)) (transport (a*t) z) = Z := by
      simpa only [neg_neg] using (transport_dual (-(a*t)) (U s t (J w)) z).symm
    have hpair : transformedPairing ε hε h hne hh m q k a t
        (transformedFormState ε hε h hne hh m q k a s t w) v z = P+(a:ℂ)*Z :=
      congrArg (fun x : Hilbert => P+(a:ℂ)*inner ℂ x z)
        (transformed_embedding ε hε h hne hh m q k a s t w)
    have hb : inner ℂ (U s t (J w)) ((coefficient h*(a:ℂ)) • transport (a*t) z) =
        (coefficient h*(a:ℂ))*Z :=
      (inner_smul_right (𝕜 := ℂ) (E := Hilbert) (U s t (J w)) (transport (a*t) z)
        (coefficient h*(a:ℂ))).trans
        (congrArg (fun y : ℂ => (coefficient h*(a:ℂ))*y) hZ)
    have ha : coefficient h*P+(coefficient h*(a:ℂ))*Z = coefficient h*(P+(a:ℂ)*Z) := by ring
    exact (congrArg₂ (fun x y : ℂ => x+y) (congrArg (fun y : ℂ => coefficient h*y) hP) hb).trans
      (ha.trans (congrArg (fun y : ℂ => coefficient h*y) hpair.symm))
  have hfun : (fun b => inner ℂ (transformedState ε hε h hne hh m q k a s b (J w)) (J v)) =
      (fun b => inner ℂ (U s b (J w)) (transport (a*b) (J v))) := by
    funext b
    simpa only [transformedState,neg_neg] using transport_dual (-(a*b)) (U s b (J w)) (J v)
  exact (hd.congr_deriv he).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)

#print axioms transformed_embedding
#print axioms transformed_initial
#print axioms transformed_norm
#print axioms transformed_defect_norm
#print axioms transformed_weak_derivative
end
end UnifiedTheory.Audit.KFCausalClockFloorSqueezeMovingDynamics
