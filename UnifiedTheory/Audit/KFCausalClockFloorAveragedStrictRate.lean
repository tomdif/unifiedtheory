/- Strict negativity on every nonzero actual completed charge-averaged
form vector. The vacuum factor survives joint closure and orbit averaging. -/
import UnifiedTheory.Audit.KFCausalClockFloorStrictOutputRate
import UnifiedTheory.Audit.KFCausalAveragedStrictRate
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedStrictRate
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction (outputAction)
open UnifiedTheory.Audit.KFCausalClockFloorStrictOutputRate (form_rate_negative)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
  (mass2 quartic vacuum t : ℝ) (hv : 0 < vacuum)
local notation "BaseData" => KFCausalClockFloorFormHamiltonian.formData ε hε hbar
  (hamiltonian_bound ε hbar hb) mass2 quartic vacuum t
local notation "R" => outputAction ε hε hbar hb
local notation "AvgSpace" => KFCausalClockFloorAveragedEnergy.AveragedSpace ε hε hbar
  (hamiltonian_bound ε hbar hb) hh mass2 quartic vacuum t
local notation "AvgJ" => KFCausalClockFloorAveragedEnergy.embedding ε hε hbar
  (hamiltonian_bound ε hbar hb) hh mass2 quartic vacuum t
local notation "AvgA" => KFCausalClockFloorAveragedEnergy.energyOutput ε hε hbar
  (hamiltonian_bound ε hbar hb) hh mass2 quartic vacuum t

include hv

theorem averaged_rate_negative (u : AvgSpace) (hu : AvgJ u ≠ 0) :
    (-2/hbar)*(inner ℂ (AvgA u) ((R).compLp (AvgA u))).im < 0 :=
  @KFCausalAveragedStrictRate.averaged_rate_negative
    Hilbert (KFCausalClosedGraphForm.FormSpace BaseData) (Output (Fin 8) Hilbert)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (KFCausalPhysicalCircleAction.group hbar hh) (2*Real.pi)
    (KFCausalClosedGraphForm.embedding BaseData) (KFCausalClosedGraphForm.energyOutput BaseData)
    R (-2/hbar) (form_rate_negative ε hε hbar hh hb mass2 quartic vacuum t hv) u hu

theorem completed_rate_negative (w : FormSpace ε hε hbar hh hb mass2 quartic vacuum t)
    (hw : embedding ε hε hbar hh hb mass2 quartic vacuum t w ≠ 0) :
    (-2/hbar)*(inner ℂ (energyOutput ε hε hbar hh hb mass2 quartic vacuum t w)
      ((R).compLp (energyOutput ε hε hbar hh hb mass2 quartic vacuum t w))).im < 0 := by
  have hs := KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective
    ε hε hbar hh hb mass2 quartic vacuum t w
  let u := Classical.choose hs
  have hu := Classical.choose_spec hs
  have hj : AvgJ u = embedding ε hε hbar hh hb mass2 quartic vacuum t w :=
    congrArg (embedding ε hε hbar hh hb mass2 quartic vacuum t) hu
  have ha : AvgA u = energyOutput ε hε hbar hh hb mass2 quartic vacuum t w :=
    congrArg (energyOutput ε hε hbar hh hb mass2 quartic vacuum t) hu
  have hn : AvgJ u ≠ 0 := fun hz => hw (hj.symm.trans hz)
  have h := averaged_rate_negative ε hε hbar hh hb mass2 quartic vacuum t hv u hn
  have he := congrArg (fun g : KFCausalAveragedOutputRescaling.EnergyOutputSpace => (-2/hbar)*(inner ℂ g ((R).compLp g)).im) ha
  exact lt_of_eq_of_lt he.symm h

theorem averaged_square_rate_negative (u : AvgSpace) (hu : AvgJ u ≠ 0) :
    (-2/hbar)*(inner ℂ (AvgA u) (((R).comp R).compLp (AvgA u))).im < 0 :=
  @KFCausalAveragedStrictRate.averaged_rate_negative
    Hilbert (KFCausalClosedGraphForm.FormSpace BaseData) (Output (Fin 8) Hilbert)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (KFCausalPhysicalCircleAction.group hbar hh) (2*Real.pi)
    (KFCausalClosedGraphForm.embedding BaseData) (KFCausalClosedGraphForm.energyOutput BaseData)
    ((R).comp R) (-2/hbar) (fun v hv' =>
      KFCausalClockFloorStrictOutputRate.output_square_rate_negative ε hε hbar hh hb _
        (KFCausalClockFloorVacuumOutputFaithful.form_vacuum_ne_zero ε hε hbar _
          mass2 quartic vacuum t hv v hv')) u hu

theorem completed_square_rate_negative (w : FormSpace ε hε hbar hh hb mass2 quartic vacuum t)
    (hw : embedding ε hε hbar hh hb mass2 quartic vacuum t w ≠ 0) :
    (-2/hbar)*(inner ℂ (energyOutput ε hε hbar hh hb mass2 quartic vacuum t w)
      (((R).comp R).compLp (energyOutput ε hε hbar hh hb mass2 quartic vacuum t w))).im < 0 := by
  have hs := KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective
    ε hε hbar hh hb mass2 quartic vacuum t w
  let u := Classical.choose hs
  have hu := Classical.choose_spec hs
  have hj : AvgJ u = embedding ε hε hbar hh hb mass2 quartic vacuum t w :=
    congrArg (embedding ε hε hbar hh hb mass2 quartic vacuum t) hu
  have ha : AvgA u = energyOutput ε hε hbar hh hb mass2 quartic vacuum t w :=
    congrArg (energyOutput ε hε hbar hh hb mass2 quartic vacuum t) hu
  have hn : AvgJ u ≠ 0 := fun hz => hw (hj.symm.trans hz)
  have h := averaged_square_rate_negative ε hε hbar hh hb mass2 quartic vacuum t hv u hn
  have he := congrArg (fun g : KFCausalAveragedOutputRescaling.EnergyOutputSpace =>
    (-2/hbar)*(inner ℂ g (((R).comp R).compLp g)).im) ha
  exact lt_of_eq_of_lt he.symm h

#print axioms averaged_square_rate_negative
#print axioms completed_square_rate_negative

#print axioms averaged_rate_negative
#print axioms completed_rate_negative

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedStrictRate
