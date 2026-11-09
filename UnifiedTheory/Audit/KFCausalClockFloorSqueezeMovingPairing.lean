/- The exact full form pairing in a squeeze frame. Every angle-dependent
factor retains its actual weight; this is used by the moving weak equation. -/
import UnifiedTheory.Audit.KFCausalClockFloorSqueezePairing
import UnifiedTheory.Audit.KFCausalSqueezeEnergyContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSqueezeMovingPairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEnergy (degree factorScale outputAction outputAction_apply)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy (OutputSpace coordinate coordinateLp outputLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorReferenceSqueeze
open UnifiedTheory.Audit.KFCausalClockFloorSqueezePairing (timeOutput reference_output_pairing)

def weightedPairing (a : ℝ) (x y : OutputSpace) : ℂ :=
  ∑ i : Fin 8, (Real.exp (2*degree i*a):ℂ)*inner ℂ (coordinateLp i x) (coordinateLp i y)

theorem point_pairing (a : ℝ) (x y : Output (Fin 8) Hilbert) :
    inner ℂ (outputAction a x) (outputAction a y) =
      ∑ i : Fin 8, (Real.exp (2*degree i*a):ℂ)*inner ℂ (x i) (y i) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [outputAction_apply,outputAction_apply,inner_smul_left,inner_smul_right,
    LinearIsometryEquiv.inner_map_map]
  have he : factorScale a i * factorScale a i = (Real.exp (2*degree i*a):ℂ) := by
    unfold factorScale
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  simp only [factorScale,Complex.conj_ofReal] at he ⊢
  rw [← mul_assoc,he]

theorem outputLp_pairing (a : ℝ) (x y : OutputSpace) :
    inner ℂ (outputLp a x) (outputLp a y) = weightedPairing a x y := by
  have he : (fun θ => inner ℂ (outputLp a x θ) (outputLp a y θ)) =ᵐ[angleMeasure]
      fun θ => ∑ i : Fin 8, (Real.exp (2*degree i*a):ℂ)*
        inner ℂ (coordinateLp i x θ) (coordinateLp i y θ) := by
    filter_upwards [(outputAction a).coeFn_compLp x,(outputAction a).coeFn_compLp y,
      ae_all_iff.mpr (fun i : Fin 8 => (coordinate i).coeFn_compLp x),
      ae_all_iff.mpr (fun i : Fin 8 => (coordinate i).coeFn_compLp y)] with θ hx hy hcx hcy
    change inner ℂ ((outputAction a).compLp x θ) ((outputAction a).compLp y θ) = _
    rw [hx,hy,point_pairing]
    apply Finset.sum_congr rfl
    intro i _
    have h1 : coordinateLp i x θ = x θ i := hcx i
    have h2 : coordinateLp i y θ = y θ i := hcy i
    rw [h1,h2]
  rw [L2.inner_def,integral_congr_ae he,integral_finset_sum Finset.univ]
  · unfold weightedPairing
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul,← L2.inner_def]
  · intro i _
    exact (L2.integrable_inner (𝕜 := ℂ) (coordinateLp i x) (coordinateLp i y)).const_mul _

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m q k : ℝ)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity (referenceFormOperator)
local notation "V" => FormSpace ε hε h hne hh m q k 0
local notation "R" => (fun a : ℝ => formAction ε hε h hne hh m q k a 0)
local notation "T" => timeOutput ε hε h hne hh m q k
local notation "Q" => referenceFormOperator ε hε h hne hh m q k

theorem timeOutput_action (a t : ℝ) (u : V) : T t (R a u) = outputLp a (T t u) := by
  unfold timeOutput
  exact (congrArg (energyOutput ε hε h hne hh m q k t)
    (formAction_transfer ε hε h hne hh m q k a 0 t u)).trans
      (formAction_output ε hε h hne hh m q k a t (formTransfer ε hε h hne hh m q k 0 t u))

theorem reference_squeezed_pairing (a t : ℝ) (u v : V) :
    inner ℂ (R a u) (Q t (R a v)) = weightedPairing a (T t u) (T t v) := by
  have hp := reference_output_pairing ε hε h hne hh m q k a t (R a u) v
  exact hp.trans ((congrArg (fun x : OutputSpace => inner ℂ x (outputLp a (T t v)))
    (timeOutput_action ε hε h hne hh m q k a t u)).trans (outputLp_pairing a (T t u) (T t v)))

theorem reference_mixed_pairing (a t : ℝ) (u v : V) :
    inner ℂ u (Q t (R a v)) = weightedPairing a (T t (R (-a) u)) (T t v) := by
  have hp := reference_squeezed_pairing ε hε h hne hh m q k a t (R (-a) u) v
  have hi : R a (R (-a) u) = u := by
    simpa only [neg_neg] using formAction_inverse ε hε h hne hh m q k (-a) 0 u
  exact (congrArg (fun x : V => inner ℂ x (Q t (R a v))) hi.symm).trans hp

#print axioms point_pairing
#print axioms outputLp_pairing
#print axioms timeOutput_action
#print axioms reference_squeezed_pairing
#print axioms reference_mixed_pairing
end
end UnifiedTheory.Audit.KFCausalClockFloorSqueezeMovingPairing
