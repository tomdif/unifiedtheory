/- Continuity of the concrete energy outputs and the two response terms
along continuous physical curves, with a fixed positive resolvent scale. -/
import UnifiedTheory.Audit.KFCausalNeutralResolventResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 120000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalNeutralResolventContinuity
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalNeutralTranslationOutput (Outputs)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorResolventTests
open UnifiedTheory.Audit.KFCausalNeutralResolventResponse
open UnifiedTheory.Audit.KFCausalNeutralOutputLinearResponse (translated)
open UnifiedTheory.Audit.KFCausalNeutralTranslationBounds (weightedLinear weightedQuadratic)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

theorem timeOutput_split (t : ℝ) :
    timeOutput 0 t = staticOutput+(Real.exp t:ℂ) • growingOutput := by
  apply ContinuousLinearMap.ext
  intro y
  apply PiLp.ext
  intro i
  by_cases hi : i.val < 3
  all_goals simp [timeOutput_apply,staticOutput,growingOutput,
    KFCausalFiniteOutputRescaling.selected_apply,hi]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "L" => referenceEnergyMap ε hε h hne hh m g k
local notation "A" => regularizerLift ε hε h hne hh m g k

theorem referenceEnergyMap_split (t : ℝ) :
    L t = staticMap ε hε h hne hh m g k+(Real.exp t:ℂ) • growingMap ε hε h hne hh m g k := by
  have he := congrArg (fun B : Outputs →L[ℂ] Outputs => B.compLpL 2 angleMeasure) (timeOutput_split t)
  simp only [ContinuousLinearMap.add_compLpL,ContinuousLinearMap.smul_compLpL] at he
  apply ContinuousLinearMap.ext
  intro x
  exact (referenceEnergyMap_apply ε hε h hne hh m g k t x).trans
    ((transfer_energyOutput ε hε h hne hh m g k 0 t x).trans
      (congrArg (fun B : EnergyOutputSpace →L[ℂ] EnergyOutputSpace => B (energyOutput ε hε h hne hh m g k 0 x)) he))

theorem referenceEnergyMap_continuous : Continuous L := by
  have he : Continuous (fun t : ℝ => staticMap ε hε h hne hh m g k+
      (Real.exp t:ℂ) • growingMap ε hε h hne hh m g k) :=
    continuous_const.add ((Complex.continuous_ofReal.comp Real.continuous_exp).smul continuous_const)
  exact he.congr (fun t => (referenceEnergyMap_split ε hε h hne hh m g k t).symm)

theorem regularizerLift_continuous (a : ℝ) (ha : 0 < a) : Continuous (A a) :=
  ((referenceInverse_continuous ε hε h hne hh m g k a ha).clm_comp continuous_const).const_smul a

theorem responseOutput_continuous (a : ℝ) (ha : 0 < a) (f : ℝ → Hilbert) (hf : Continuous f) :
    Continuous (fun t => responseOutput ε hε h hne hh m g k a t (f t)) :=
  (referenceEnergyMap_continuous ε hε h hne hh m g k).clm_apply
    ((regularizerLift_continuous ε hε h hne hh m g k a ha).clm_apply hf)

theorem linearRate_continuous (a v : ℝ) (ha : 0 < a) (f : ℝ → Hilbert) (hf : Continuous f) :
    Continuous (fun t => linearRate ε hε h hne hh m g k a t v (f t)) :=
  (KFCausalNeutralOutputLinearResponse.linearRate_continuous angleMeasure (energyWeight m g k 0) h v).comp
    (responseOutput_continuous ε hε h hne hh m g k a ha f hf)

theorem quadraticRate_continuous (a v : ℝ) (ha : 0 < a) (f : ℝ → Hilbert) (hf : Continuous f) :
    Continuous (fun t => quadraticRate ε hε h hne hh m g k a t v (f t)) :=
  (KFCausalNeutralOutputLinearResponse.quadraticRate_continuous angleMeasure (energyWeight m g k 0) h v).comp
    (responseOutput_continuous ε hε h hne hh m g k a ha f hf)

#print axioms timeOutput_split
#print axioms referenceEnergyMap_split
#print axioms referenceEnergyMap_continuous
#print axioms regularizerLift_continuous
#print axioms responseOutput_continuous
#print axioms linearRate_continuous
#print axioms quadraticRate_continuous
end
end UnifiedTheory.Audit.KFCausalNeutralResolventContinuity
