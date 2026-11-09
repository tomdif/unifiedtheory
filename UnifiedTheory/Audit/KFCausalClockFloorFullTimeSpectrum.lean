/- Every fixed localized upper coupled spectral observation tends to
zero along the full actual trajectory. The proof uses an actual
dissipation budget and a derived squared variation estimate. -/
import UnifiedTheory.Audit.KFCausalClockFloorPhysicalVariation
import UnifiedTheory.Audit.KFCausalExponentialSquareNoSpikes
import UnifiedTheory.Audit.KFCausalDenseObservationDecay
import UnifiedTheory.Audit.KFCausalClockFloorLocalizedSpectrum
import UnifiedTheory.Audit.KFCausalClockFloorDissipationTail

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFullTimeSpectrum
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding energyOutput transfer_energyOutput)
open KFCausalClockFloorAveragedFormFlow (formFlow)
open KFCausalClockFloorAveragedEvolution (evolution evolution_embedding)
open KFCausalClockFloorDefectDissipationBudget (dissipation dissipation_continuous)
open KFCausalClockFloorLocalizedSpectrum (orbitObservation)
open KFCausalClockFloorMovingDissipation (detector)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "F" => formFlow ε hε h hne hb m g k
local notation "E" => evolution ε hε h hne hb m g k
local notation "B" => orbitObservation ε hε h hne
local notation "d" => dissipation ε hε h hne hb m g k
local notation "det" => detector ε hε h hne hb m g k

theorem actual_rescaling (s t : ℝ) (v : V) :
    d s t v=2*Real.exp (2*t)*det (F s t v) := by
  unfold dissipation KFCausalClockFloorExactEhrenfest.classicalRate
    KFCausalClockFloorExactEhrenfest.evolvingOutput
  rw [transfer_energyOutput,KFCausalClockFloorDissipationRescaling.averaged_real_pairing]
  simp only [sub_zero,detector]
  ring

theorem detection_bound (hk : 0 < k) (s t R : ℝ) (v : V) :
    Real.exp (2*t)*‖B R (E s t (J v))‖^2 ≤
      (64*ε*Real.exp (-R)/k)*d s t v := by
  rw [evolution_embedding,actual_rescaling]
  have he := mul_le_mul_of_nonneg_left
    (KFCausalClockFloorLocalizedSpectrum.form_bound ε hε h hne hb m g k R hk (F s t v))
    (Real.exp_pos (2*t)).le
  exact he.trans_eq (by ring)

theorem upper_decay_form (hk : 0 < k) (s R : ℝ) (v : V) :
    Tendsto (fun t => B R (E s t (J v))) atTop (𝓝 0) := by
  let C := KFCausalClockFloorPhysicalVariation.bound ε hε h hne hb m g k s v
  have hC : 0 ≤ C := KFCausalClockFloorPhysicalVariation.bound_nonnegative ε hε h hne hb m g k s v
  apply KFCausalExponentialSquareNoSpikes.tendsto_zero
    (fun t => B R (E s t (J v))) (fun t => d s t v)
    (dissipation_continuous ε hε h hne hb m g k s v) s (‖B R‖^2*C) (by positivity)
  · intro a b hsa hab
    rw [← map_sub]
    have hn := pow_le_pow_left₀ (norm_nonneg _)
      ((B R).le_opNorm (E s b (J v)-E s a (J v))) 2
    rw [mul_pow] at hn
    exact hn.trans ((mul_le_mul_of_nonneg_left
      (KFCausalClockFloorPhysicalVariation.increment_square_bound ε hε h hne hb m g k
        s a b hsa hab v) (sq_nonneg ‖B R‖)).trans_eq (by ring))
  · intro η hη
    let K := 64*ε*Real.exp (-R)/k
    have hK : 0 < K := by dsimp [K]; positivity
    refine ⟨η^2/K,by positivity,fun t _ ht => ?_⟩
    have he := detection_bound ε hε h hne hb m g k hk s t R v
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη.le ht 2) (Real.exp_pos (2*t)).le
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hK).mpr
    exact hs.trans (he.trans_eq (mul_comm _ _))
  · exact KFCausalClockFloorDissipationTail.tail_budget ε hε h hne hb m g k s v

theorem upper_decay (hk : 0 < k) (s R : ℝ) (f : Hilbert) :
    Tendsto (fun t => B R (E s t f)) atTop (𝓝 0) :=
  KFCausalDenseObservationDecay.decay J
    (KFCausalClockFloorAveragedFormGeometry.embedding_dense ε hε h hne hb m g k 0)
    (fun t => E s t) (B R) atTop
    (fun v => upper_decay_form ε hε h hne hb m g k hk s R v) f

#print axioms actual_rescaling
#print axioms detection_bound
#print axioms upper_decay_form
#print axioms upper_decay
end
end UnifiedTheory.Audit.KFCausalClockFloorFullTimeSpectrum
