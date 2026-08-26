/-
  Audit/KFTOESharedHarmonicMicroscopicModel.lean

  ONE MICROSCOPIC HARMONIC LAW -> JOINT GATE 4/5/6 OBSERVABLE LAW

  A list of separately constructed Gate 4, Gate 5, and Gate 6 objects does
  not by itself show that they arise from one microscopic theory.  This file
  supplies the missing provenance layer.  Three measurable coarse-grainings
  are applied to the *same* action-selected harmonic Born trajectory, and a
  single joint pushforward probability measure is constructed.  Its three
  marginals are proved to be exactly the separately displayed Gate 4, Gate 5,
  and Gate 6 pushforwards.

  This is the strongest conclusion obtainable from readout data alone.  The
  record intentionally requires the three readouts and their measurability;
  it does not assert that an arbitrary readout has the intended physical
  interpretation.  That identification and comparison with experiment remain
  separate obligations.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFTOESharedHarmonicMicroscopicModel

noncomputable section

open MeasureTheory
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure

universe u v w

/-- The common microscopic sample space used by all three readouts. -/
abbrev HarmonicCausalHistory : Type :=
  ∀ n : ℕ, CausalSetGrowthBranch n

/-- Three typed observable maps out of one harmonic causal history.  The
`chirality` parameter pins the record to the exact harmonic trajectory law
whose pushforwards are formed below. -/
structure HarmonicGate456Readout
    (chirality : Fin 2)
    (Gate4State : Type u) (Gate5State : Type v) (Gate6State : Type w)
    [MeasurableSpace Gate4State] [MeasurableSpace Gate5State]
    [MeasurableSpace Gate6State] where
  gate4Readout : HarmonicCausalHistory → Gate4State
  gate5Readout : HarmonicCausalHistory → Gate5State
  gate6Readout : HarmonicCausalHistory → Gate6State
  gate4Measurable : Measurable gate4Readout
  gate5Measurable : Measurable gate5Readout
  gate6Measurable : Measurable gate6Readout

namespace HarmonicGate456Readout

variable {chirality : Fin 2}
variable {Gate4State : Type u} {Gate5State : Type v} {Gate6State : Type w}
variable [MeasurableSpace Gate4State] [MeasurableSpace Gate5State]
variable [MeasurableSpace Gate6State]

variable
  (R : HarmonicGate456Readout chirality Gate4State Gate5State Gate6State)

/-- The three coarse-grainings evaluated together, before any marginal is
forgotten. -/
def jointReadout :
    HarmonicCausalHistory → Gate4State × (Gate5State × Gate6State) :=
  fun history =>
    (R.gate4Readout history,
      (R.gate5Readout history, R.gate6Readout history))

theorem jointReadout_measurable : Measurable R.jointReadout := by
  exact R.gate4Measurable.prodMk
    (R.gate5Measurable.prodMk R.gate6Measurable)

/-- The single joint Gate 4/5/6 observable law induced by the canonical
harmonic Born trajectory measure. -/
def jointMeasure : Measure (Gate4State × (Gate5State × Gate6State)) :=
  (harmonicBornTrajectoryMeasure chirality).map R.jointReadout

/-- The joint observable law is a probability measure because it is a
measurable pushforward of the already normalized microscopic law. -/
theorem jointMeasure_isProbabilityMeasure :
    IsProbabilityMeasure R.jointMeasure := by
  unfold jointMeasure
  exact Measure.isProbabilityMeasure_map
    R.jointReadout_measurable.aemeasurable

/-- Forgetting Gate 5 and Gate 6 recovers exactly the Gate 4 pushforward. -/
theorem gate4_marginal :
    R.jointMeasure.map Prod.fst =
      (harmonicBornTrajectoryMeasure chirality).map R.gate4Readout := by
  rw [jointMeasure,
    Measure.map_map measurable_fst R.jointReadout_measurable]
  rfl

/-- Forgetting Gate 4 and Gate 6 recovers exactly the Gate 5 pushforward. -/
theorem gate5_marginal :
    R.jointMeasure.map (fun output => output.2.1) =
      (harmonicBornTrajectoryMeasure chirality).map R.gate5Readout := by
  have hProjection :
      Measurable
        (fun output : Gate4State × (Gate5State × Gate6State) =>
          output.2.1) :=
    measurable_fst.comp measurable_snd
  rw [jointMeasure,
    Measure.map_map hProjection R.jointReadout_measurable]
  rfl

/-- Forgetting Gate 4 and Gate 5 recovers exactly the Gate 6 pushforward. -/
theorem gate6_marginal :
    R.jointMeasure.map (fun output => output.2.2) =
      (harmonicBornTrajectoryMeasure chirality).map R.gate6Readout := by
  have hProjection :
      Measurable
        (fun output : Gate4State × (Gate5State × Gate6State) =>
          output.2.2) :=
    measurable_snd.comp measurable_snd
  rw [jointMeasure,
    Measure.map_map hProjection R.jointReadout_measurable]
  rfl

/-- Auditable meaning of "Gates 4--6 arise from one microscopic law": there
is one normalized joint pushforward and every named single-gate law is its
corresponding marginal. -/
structure Closed : Prop where
  jointProbability : IsProbabilityMeasure R.jointMeasure
  gate4Marginal :
    R.jointMeasure.map Prod.fst =
      (harmonicBornTrajectoryMeasure chirality).map R.gate4Readout
  gate5Marginal :
    R.jointMeasure.map (fun output => output.2.1) =
      (harmonicBornTrajectoryMeasure chirality).map R.gate5Readout
  gate6Marginal :
    R.jointMeasure.map (fun output => output.2.2) =
      (harmonicBornTrajectoryMeasure chirality).map R.gate6Readout

theorem closed : R.Closed where
  jointProbability := R.jointMeasure_isProbabilityMeasure
  gate4Marginal := R.gate4_marginal
  gate5Marginal := R.gate5_marginal
  gate6Marginal := R.gate6_marginal

#print axioms jointMeasure_isProbabilityMeasure
#print axioms gate4_marginal
#print axioms gate5_marginal
#print axioms gate6_marginal
#print axioms closed

end HarmonicGate456Readout

end

end UnifiedTheory.Audit.KFTOESharedHarmonicMicroscopicModel
