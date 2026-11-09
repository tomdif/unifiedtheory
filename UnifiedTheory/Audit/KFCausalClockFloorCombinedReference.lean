/- The combined unitary on the actual reference energy-form space, with
its exact full polarized energy pairing and inverse. -/
import UnifiedTheory.Audit.KFCausalClockFloorCombinedUnitary
import UnifiedTheory.Audit.KFCausalClockFloorCombinedOutput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorCombinedReference
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity (referenceFormOperator referenceForm_represents_closed_form)
open UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy (rate gaugeOutputLp)
open UnifiedTheory.Audit.KFCausalClockFloorCombinedUnitary (combined combined_inverse)
open UnifiedTheory.Audit.KFCausalClockFloorCombinedOutput
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy (OutputSpace outputLp)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m q k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m q k 0
local notation "J" => embedding ε hε h hne hh m q k 0
local notation "A" => energyOutput ε hε h hne hh m q k 0
local notation "G" => (fun r : ℝ => KFCausalClockFloorReferenceChartModulation.formAction ε hε h hne hh m q k r 0)
local notation "S" => (fun r : ℝ => KFCausalClockFloorReferenceSqueeze.formAction ε hε h hne hh m q k r 0)
local notation "Q" => referenceFormOperator ε hε h hne hh m q k

def formAction (a t : ℝ) : V →L[ℂ] V := (G (rate h t)).comp (S (a*t))
local notation "R" => formAction ε hε h hne hh m q k

theorem formAction_embedding (a t : ℝ) (u : V) : J (R a t u) = combined ε h a t (J u) := rfl

theorem formAction_inverse (a t : ℝ) (u : V) : R a (-t) (R a t u) = u := by
  apply embedding_injective ε hε h hne hh m q k 0
  simp only [formAction_embedding,combined_inverse ε h hne]

theorem formAction_time_output (a t : ℝ) (u : V) :
    energyOutput ε hε h hne hh m q k t
      (formTransfer ε hε h hne hh m q k 0 t (R a t u)) = combinedOutputLp ε h (a*t) t (A u) := by
  have hg := KFCausalClockFloorGaugePairing.formAction_time_output ε hε h hne hh m q k t (S (a*t) u)
  have hs : A (S (a*t) u) = outputLp (a*t) (A u) :=
    KFCausalClockFloorReferenceSqueeze.formAction_output ε hε h hne hh m q k (a*t) 0 u
  exact hg.trans ((congrArg (gaugeOutputLp ε h t) hs).trans
    (combinedOutputLp_comp ε h (a*t) t (A u)).symm)

theorem reference_combined_pairing (a t : ℝ) (u v : V) :
    inner ℂ (R a t u) (Q t (R a t v)) = weightedPairing (a*t) t (A u) (A v) := by
  have hp := referenceForm_represents_closed_form ε hε h hne hh m q k t (R a t u) (R a t v)
  have he := congrArg₂ (fun x y : OutputSpace => inner ℂ x y)
    (formAction_time_output ε hε h hne hh m q k a t u)
    (formAction_time_output ε hε h hne hh m q k a t v)
  exact hp.trans (he.trans (outputLp_pairing ε h hne (a*t) t (A u) (A v)))

theorem reference_mixed_pairing (a t : ℝ) (u v : V) :
    inner ℂ u (Q t (R a t v)) = weightedPairing (a*t) t (A (R a (-t) u)) (A v) := by
  have hp := reference_combined_pairing ε hε h hne hh m q k a t (R a (-t) u) v
  have hi : R a t (R a (-t) u) = u := by
    simpa only [neg_neg] using formAction_inverse ε hε h hne hh m q k a (-t) u
  exact (congrArg (fun x : V => inner ℂ x (Q t (R a t v))) hi.symm).trans hp

#print axioms formAction_embedding
#print axioms formAction_inverse
#print axioms formAction_time_output
#print axioms reference_combined_pairing
#print axioms reference_mixed_pairing
end
end UnifiedTheory.Audit.KFCausalClockFloorCombinedReference
