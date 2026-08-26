/-
  Audit/KFGate6ActionSelectedHarmonicBornInitialMeasureAdapter.lean

  A NARROW GATE-6 ADAPTER FOR THE HARMONIC BORN TRAJECTORY LAW

  The Gate-6 ledger stores its initial-condition/cosmological-measure slot as
  an unconstrained `Prop`.  This file gives that slot one precise, proved
  interpretation: the canonical Born probability law on complete
  causal-growth trajectories built from the action-selected raw harmonic
  schedule, with its exact finite marginals and almost-sure physical support.

  This is only a causal-growth measure certificate.  It is not renamed into a
  physical cosmological measure.  The final section records the genuinely
  missing typed bridge: a measurable readout into a chosen cosmological
  initial-state space whose pushforward is almost surely physically
  admissible.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure
import UnifiedTheory.Audit.KFTOESevenGateAttack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFGate6ActionSelectedHarmonicBornInitialMeasureAdapter

noncomputable section

open scoped ENNReal
open Set MeasureTheory Preorder
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalSetMicroscopicSpectatorAction
open UnifiedTheory.Audit.KFCausalSetIntrinsicPairCouplingSelection
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornTrajectoryMeasure
open UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure
open UnifiedTheory.Audit.KFTOESevenGateAttack
open UnifiedTheory.Cosmology.QQG

/-! ## 1. The exact measure-theoretic certificate that is now redundant -/

/-- The proved content of the action-selected harmonic causal-growth measure,
without claiming that its sample space already is a space of cosmological
initial data.  The certificate covers both chiral labels, so it introduces no
extra chirality-choice premise. -/
structure Gate6ActionSelectedHarmonicBornCausalGrowthMeasureCertificate : Prop where
  actionSelectsHarmonicCoupling :
    microscopicSpectatorPairCoupling canonicalVacuumSpectatorCausalAction =
      harmonicCriticalPairCoupling
  probabilityMeasure :
    ∀ chirality : Fin 2,
      IsProbabilityMeasure (harmonicBornTrajectoryMeasure chirality)
  totalMass :
    ∀ chirality : Fin 2,
      harmonicBornTrajectoryMeasure chirality Set.univ = 1
  exactFiniteCylinderMarginals :
    ∀ (chirality : Fin 2) (n : ℕ)
      (history : ∀ i : Finset.Iic n, CausalSetGrowthBranch i),
      (harmonicBornTrajectoryMeasure chirality).map
          (frestrictLe n) {history} =
        ENNReal.ofReal
          (finiteBornPathWeight
            (canonicalHarmonicBornNormalizedGrowthLaw chirality) (n + 1)
            (rankedGrowthPathOfIic n history))
  almostSurePhysicalSupport :
    ∀ chirality : Fin 2,
      ∀ᵐ trajectory ∂harmonicBornTrajectoryMeasure chirality,
        IsPhysicalInfiniteCausalGrowthTrajectory trajectory

/-- The canonical harmonic trajectory measure built on the action-selected raw
schedule supplies the certificate with no external existence or normalization
premise. -/
theorem gate6_actionSelectedHarmonicBornCausalGrowthMeasureCertificate_closed :
    Gate6ActionSelectedHarmonicBornCausalGrowthMeasureCertificate := by
  exact
    ⟨microscopicSpectatorPairCoupling_eq_harmonic
        canonicalVacuumSpectatorCausalAction,
      harmonicBornTrajectoryMeasure_isProbabilityMeasure,
      harmonicBornTrajectoryMeasure_univ,
      harmonicBornTrajectoryMeasure_finiteCylinder_singleton,
      harmonicBornTrajectory_physical_ae⟩

/-! ## 2. A Gate-6 specialization that removes only this certificate -/

/-- The strongest named Gate-6 target specialized so that its initial-measure
slot means exactly the causal-growth certificate above.  The physical
Hayden--Preskill and late-cosmology obligations remain unchanged, and evidence
for a fixed QQG claims ledger remains an explicit closure hypothesis. -/
def gate6NamedTargetsOfActionSelectedHarmonicBornCausalGrowthMeasure
    (lateStructureFormation gravitationalWaveCompatibility : Prop) :
    Gate6NamedCosmologyBlackHoleBridgeTargets :=
  gate6NamedCosmologyBlackHoleBridgeTargetsOfHaydenPreskillMicroscopicEvaporation
    Gate6ActionSelectedHarmonicBornCausalGrowthMeasureCertificate
    lateStructureFormation gravitationalWaveCompatibility

/-- In the narrowly specialized target, callers no longer need to supply a
bare measure-existence premise.  They must still supply evidence for the fixed
QQG claims ledger. -/
theorem gate6_namedBridge_closed_of_actionSelectedHarmonicBornCausalGrowthMeasure
    (claims : QQGEmergenceClaims)
    (S : UnifiedTheory.Cosmology.QQG.QQGScenario)
    {lateStructureFormation gravitationalWaveCompatibility : Prop}
    (hQQGEmergence : QQGEmergenceHypotheses claims)
    (hHP : Gate6HaydenPreskillMicroscopicEvaporationBridgeClosed)
    (hlate : lateStructureFormation)
    (hgw : gravitationalWaveCompatibility) :
    Gate6NamedCosmologyBlackHoleBridgeClosed claims S
      (gate6NamedTargetsOfActionSelectedHarmonicBornCausalGrowthMeasure
        lateStructureFormation gravitationalWaveCompatibility) := by
  exact
    gate6_namedCosmologyBlackHoleBridge_closed_of_haydenPreskillMicroscopicEvaporation
      claims S
      gate6_actionSelectedHarmonicBornCausalGrowthMeasureCertificate_closed
      hQQGEmergence hHP hlate hgw

/-- The corresponding strict Gate-6 closure theorem.  Only the now-proved
causal-growth measure certificate has disappeared from the hypotheses; QQG
emergence evidence remains explicit. -/
theorem gate6_cosmologyBlackHole_closed_of_actionSelectedHarmonicBornCausalGrowthMeasure
    (claims : QQGEmergenceClaims)
    (S : UnifiedTheory.Cosmology.QQG.QQGScenario)
    {lateStructureFormation gravitationalWaveCompatibility : Prop}
    (hQQGEmergence : QQGEmergenceHypotheses claims)
    (hHP : Gate6HaydenPreskillMicroscopicEvaporationBridgeClosed)
    (hlate : lateStructureFormation)
    (hgw : gravitationalWaveCompatibility) :
    Gate6CosmologyBlackHoleClosed
      (gate6CosmologyBlackHoleTargetsOfNamedCosmologyBlackHoleBridge claims S
        (gate6NamedTargetsOfActionSelectedHarmonicBornCausalGrowthMeasure
          lateStructureFormation gravitationalWaveCompatibility)) := by
  exact
    gate6_cosmologyBlackHole_closed_of_namedCosmologyBlackHoleBridge claims S
      (gate6NamedTargetsOfActionSelectedHarmonicBornCausalGrowthMeasure
        lateStructureFormation gravitationalWaveCompatibility)
      (gate6_namedBridge_closed_of_actionSelectedHarmonicBornCausalGrowthMeasure
        claims S hQQGEmergence hHP hlate hgw)

/-! ## 3. The remaining physical type bridge -/

/-- An honest cosmological initial measure needs a specified state space and
an admissible physical sector, not merely an abstract proposition. -/
structure Gate6AdmissibleCosmologicalInitialMeasure
    (CosmologicalInitialState : Type*)
    [MeasurableSpace CosmologicalInitialState]
    (physicallyAdmissible : Set CosmologicalInitialState) where
  measure : Measure CosmologicalInitialState
  probabilityMeasure : IsProbabilityMeasure measure
  admissibleMeasurable : MeasurableSet physicallyAdmissible
  almostSurelyAdmissible : measure physicallyAdmissible = 1

/-- The exact extra data required to turn the causal-growth trajectory law
into a physical cosmological initial measure: a measurable readout and an
almost-sure admissibility theorem for its output.  Neither datum follows from
normalization or finite causal-growth marginals alone. -/
structure Gate6ActionSelectedHarmonicBornCosmologicalReadoutBridge
    (chirality : Fin 2)
    (CosmologicalInitialState : Type*)
    [MeasurableSpace CosmologicalInitialState]
    (physicallyAdmissible : Set CosmologicalInitialState) where
  readout :
    (∀ n : ℕ, CausalSetGrowthBranch n) → CosmologicalInitialState
  readoutMeasurable : Measurable readout
  admissibleMeasurable : MeasurableSet physicallyAdmissible
  almostEveryTrajectoryAdmissible :
    ∀ᵐ trajectory ∂harmonicBornTrajectoryMeasure chirality,
      readout trajectory ∈ physicallyAdmissible

namespace Gate6ActionSelectedHarmonicBornCosmologicalReadoutBridge

variable {chirality : Fin 2}
variable {CosmologicalInitialState : Type*}
variable [MeasurableSpace CosmologicalInitialState]
variable {physicallyAdmissible : Set CosmologicalInitialState}

/-- Push the action-selected harmonic trajectory law through the supplied
cosmological readout. -/
def inducedCosmologicalInitialMeasure
    (B : Gate6ActionSelectedHarmonicBornCosmologicalReadoutBridge chirality
      CosmologicalInitialState physicallyAdmissible) :
    Measure CosmologicalInitialState :=
  (harmonicBornTrajectoryMeasure chirality).map B.readout

theorem inducedCosmologicalInitialMeasure_isProbabilityMeasure
    (B : Gate6ActionSelectedHarmonicBornCosmologicalReadoutBridge chirality
      CosmologicalInitialState physicallyAdmissible) :
    IsProbabilityMeasure B.inducedCosmologicalInitialMeasure := by
  unfold inducedCosmologicalInitialMeasure
  exact Measure.isProbabilityMeasure_map B.readoutMeasurable.aemeasurable

theorem inducedCosmologicalInitialMeasure_admissible
    (B : Gate6ActionSelectedHarmonicBornCosmologicalReadoutBridge chirality
      CosmologicalInitialState physicallyAdmissible) :
    B.inducedCosmologicalInitialMeasure physicallyAdmissible = 1 := by
  rw [inducedCosmologicalInitialMeasure,
    Measure.map_apply B.readoutMeasurable B.admissibleMeasurable]
  calc
    harmonicBornTrajectoryMeasure chirality
        (B.readout ⁻¹' physicallyAdmissible) =
        harmonicBornTrajectoryMeasure chirality Set.univ := by
      apply measure_congr
      filter_upwards [B.almostEveryTrajectoryAdmissible] with trajectory h
      apply propext
      constructor
      · intro _
        trivial
      · intro _
        exact h
    _ = 1 := harmonicBornTrajectoryMeasure_univ chirality

/-- Once the missing readout bridge is supplied, its pushforward is an honest
probability measure supported on the chosen physical cosmological sector. -/
def toAdmissibleCosmologicalInitialMeasure
    (B : Gate6ActionSelectedHarmonicBornCosmologicalReadoutBridge chirality
      CosmologicalInitialState physicallyAdmissible) :
    Gate6AdmissibleCosmologicalInitialMeasure
      CosmologicalInitialState physicallyAdmissible where
  measure := B.inducedCosmologicalInitialMeasure
  probabilityMeasure :=
    B.inducedCosmologicalInitialMeasure_isProbabilityMeasure
  admissibleMeasurable := B.admissibleMeasurable
  almostSurelyAdmissible :=
    B.inducedCosmologicalInitialMeasure_admissible

end Gate6ActionSelectedHarmonicBornCosmologicalReadoutBridge

#print axioms gate6_actionSelectedHarmonicBornCausalGrowthMeasureCertificate_closed
#print axioms gate6_cosmologyBlackHole_closed_of_actionSelectedHarmonicBornCausalGrowthMeasure
#print axioms Gate6ActionSelectedHarmonicBornCosmologicalReadoutBridge.inducedCosmologicalInitialMeasure_admissible

end

end UnifiedTheory.Audit.KFGate6ActionSelectedHarmonicBornInitialMeasureAdapter
