/-
  Audit/KFTOEStoppableFullClosureTarget.lean

  Conditional seven-gate closure-record target based on the
  normalized-compatible stoppable Gate 3 recurrence and its direct Gate 3 to
  Gate 4 handoff.

  The theorem in this file is deliberately conditional.  It does not derive
  the remaining Gate 1 physical law selection, the Gate 4 horizon-estimator or
  null-balance inputs, the constructive-QFT inputs of Gate 5, or the physical
  cosmology/black-hole inputs of Gate 6.  It proves that, once those named
  inputs are supplied, the stoppable microscopic data close Gate 2, Gate 3,
  and the density/operator/recovery portion of Gate 4, while the existing
  preregistration ledger closes Gate 7.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFTOEFullClosureTarget
import UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3DirectRateGate4Handoff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFTOEStoppableFullClosureTarget

noncomputable section

open Filter Topology
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3Supplier
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3StoppableDirectRate
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3DirectRateGate4Handoff
open UnifiedTheory.Audit.KFTOESevenGateAttack
open UnifiedTheory.Audit.KFTOEFullClosureTarget

variable {ι X Y chart : Type*} [Fintype ι]
variable [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
variable {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
variable {scale c step descentRate remainder total : ℕ → ℝ}
variable {edge : ℕ → ι → E4}
variable {candidate : ℕ → ι → Equiv.Perm Direction}
variable {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
variable {rateBase stepFloor countGap curvatureGap spectralGap : ℝ}

/-! ## 1. Honest stoppable Gate 3 closure -/

/-- The quantized residual component of stoppable Gate 3 data, separated from
the dynamical recurrence.  This is exactly the finite-spectrum information
needed by the existing Gate 2 semantic theorem. -/
def stoppableGate3QuantizedResiduals
    (D : MicroscopicGate3StoppableDirectRateQuantizedData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      rateBase stepFloor countGap curvatureGap spectralGap) :
    QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap where
  countGap_pos := D.countGap_pos
  curvatureGap_pos := D.curvatureGap_pos
  spectralGap_pos := D.spectralGap_pos
  count_eq := D.count_eq
  curvature_eq := D.curvature_eq
  spectral_eq := D.spectral_eq

/-- Gate 3 closure stated directly for the stoppable recurrence.  In
particular, this package records the absorbing-zero theorem that makes finite
exact recovery compatible with a nonnegative normalized dynamics. -/
structure Gate3StoppableExactRecoveryClosed
    (D : MicroscopicGate3StoppableDirectRateQuantizedData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      rateBase stepFloor countGap curvatureGap spectralGap) : Prop where
  horizonProtection :
    ∀ n,
      linearResponse (w n) (source n) (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse (w n) (source n)
          (finiteAreaChange (c n) (J n)) = 0
  totalTendsToZero : Tendsto total atTop (nhds 0)
  descentStopsAtZero :
    ∀ {n : ℕ}, total n = 0 → descentRate n = 0
  zeroIsAbsorbing :
    ∀ {n : ℕ}, total n = 0 → total (n + 1) = 0
  eventualExactZero :
    ∀ᶠ n in atTop,
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n)
  eventualRecoveredStage :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)
  recoveredAfter :
    ∃ N, ∀ n, N ≤ n →
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)

/-- The stoppable data prove their Gate 3 package without importing a stronger
convergence certificate as an assumption. -/
theorem gate3_stoppableExactRecovery_closed
    (D : MicroscopicGate3StoppableDirectRateQuantizedData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      rateBase stepFloor countGap curvatureGap spectralGap) :
    Gate3StoppableExactRecoveryClosed D where
  horizonProtection := D.horizonProtection_and_total_tendsto_zero.1
  totalTendsToZero := D.horizonProtection_and_total_tendsto_zero.2
  descentStopsAtZero := D.descentRate_eq_zero_of_total_eq_zero
  zeroIsAbsorbing := D.total_next_eq_zero_of_total_eq_zero
  eventualExactZero := D.eventually_exact_zero
  eventualRecoveredStage := D.eventually_recoveredStage
  recoveredAfter := D.exists_recovered_after

/-! ## 2. Gate 4 target induced by the stoppable handoff -/

variable
  (G : MicroscopicGate3DirectRateGate4ScheduledKernelData
    (ι := ι) (X := X) (Y := Y) (chart := chart)
    w J source countWindow curvatureBias spectralLocality
    scale c step descentRate remainder total edge candidate
    countQuantum curvatureQuantum spectralQuantum
    rateBase stepFloor countGap curvatureGap spectralGap)

/-- Gate 4 with the scheduled-density, operator-profile, and recovered-stage
slots instantiated by the stoppable handoff.  Relative to the supplied `G`,
the only additional Gate 4 arguments are the explicitly named
horizon-estimator convergence and dynamical null-balance propositions.  The
chart certificates, residual matching, affine density law, and kernel/profile
package are substantial premises already stored inside `G`. -/
noncomputable def stoppableGate4HorizonEinsteinAnalyticTargets
    (errorScale : ℝ)
    (horizonEstimatorConvergence nullBalanceFromDynamics : Prop) :
    Gate4HorizonEinsteinAnalyticTargets where
  horizonEstimatorConvergence := horizonEstimatorConvergence
  physicalScheduledDensity :=
    Tendsto (fun n => (G.chartCertificate n).density) atTop atTop
  bdgKernelProfileCertificate :=
    Tendsto
      (fun n =>
        BDG4DOperatorProfileData.mean
          G.operatorKernelData.toProfileData
          ((G.chartCertificate n).density))
      atTop
      (nhds
        (BDG4DOperatorProfileData.target
          G.operatorKernelData.toProfileData))
  nullBalanceFromDynamics := nullBalanceFromDynamics
  recoveredBDGInterfaceSupplied := G.Closed errorScale

/-- The handoff closes the three supplied Gate 4 fields; the theorem remains
conditional precisely on the named horizon-estimator and null-balance inputs. -/
theorem stoppableGate4HorizonEinsteinAnalytic_closed
    {errorScale : ℝ}
    {horizonEstimatorConvergence nullBalanceFromDynamics : Prop}
    (hhorizon : horizonEstimatorConvergence)
    (hnull : nullBalanceFromDynamics) :
    Gate4HorizonEinsteinAnalyticClosed
      (stoppableGate4HorizonEinsteinAnalyticTargets G errorScale
        horizonEstimatorConvergence nullBalanceFromDynamics) := by
  have H := G.closed errorScale
  exact
    ⟨hhorizon, H.scheduledDensityTendsToInfinity,
      H.chartOperatorLimit, hnull, H⟩

/-! ## 3. Seven-gate target and conditional closure -/

/-- Conditional seven-gate ledger target specialized to stoppable Gate 3 data.

Gate 2 is the finite-spectrum semantic target read from the quantized residual
fields.  Gate 3 is the stoppable exact-recovery package above.  Gate 4 receives
the proved density/operator/recovery handoff and keeps only two named physical
propositions.  Gates 1, 5, and 6 remain explicit targets rather than claimed
derivations, and Gate 7 is only the repository's preregistration-protocol
target, not a claim that the registered experiments have run or passed. -/
noncomputable def stoppableTOEClosureTargets
    (gate1Targets : Gate1MicroscopicLawTargets)
    (gate5Targets : Gate5QFTStandardModelIRTargets)
    (gate6Targets : Gate6CosmologyBlackHoleTargets)
    (errorScale : ℝ)
    (horizonEstimatorConvergence nullBalanceFromDynamics : Prop) :
    TOEClosureTargets where
  gate1Targets := gate1Targets
  gate2Targets :=
    gate2QuantizedResidualSemanticTargets
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
  gate3ExactRecovery := Gate3StoppableExactRecoveryClosed G.gate3
  gate4Targets :=
    stoppableGate4HorizonEinsteinAnalyticTargets G errorScale
      horizonEstimatorConvergence nullBalanceFromDynamics
  gate5Targets := gate5Targets
  gate6Targets := gate6Targets
  gate7Targets := gate7PreRegistrationLedgerTargets

/-- Conditional full closure for the stoppable path.

This theorem does not manufacture the remaining physics: Gate 1 law
selection, Gate 4 horizon estimation and null balance, Gate 5 constructive QFT,
and Gate 6 cosmology/black-hole dynamics are hypotheses.  Its content derived
relative to the supplied `G` is the quantized-counter Gate 2 equivalence,
stoppable Gate 3 exact recovery, the Gate 4 density/operator/recovery handoff,
and Gate 7 preregistration-protocol checks.  It does not establish the full
physical Hauptvermutung semantics or empirical validation. -/
theorem stoppableTOEClosureTargets_closed
    {gate1Targets : Gate1MicroscopicLawTargets}
    {gate5Targets : Gate5QFTStandardModelIRTargets}
    {gate6Targets : Gate6CosmologyBlackHoleTargets}
    {errorScale : ℝ}
    {horizonEstimatorConvergence nullBalanceFromDynamics : Prop}
    (hgate1 : Gate1MicroscopicLawClosed gate1Targets)
    (hhorizon : horizonEstimatorConvergence)
    (hnull : nullBalanceFromDynamics)
    (hgate5 : Gate5QFTStandardModelIRClosed gate5Targets)
    (hgate6 : Gate6CosmologyBlackHoleClosed gate6Targets) :
    TOEClosureClosed
      (stoppableTOEClosureTargets G gate1Targets gate5Targets gate6Targets
        errorScale horizonEstimatorConvergence nullBalanceFromDynamics) := by
  exact
    ⟨hgate1,
      quantizedGate3Residuals_gate2HauptvermutungSemantic_closed
        (stoppableGate3QuantizedResiduals G.gate3),
      gate3_stoppableExactRecovery_closed G.gate3,
      stoppableGate4HorizonEinsteinAnalytic_closed G hhorizon hnull,
      hgate5, hgate6,
      gate7_externalTests_closed_from_preRegistrationLedger⟩

#print axioms stoppableGate3QuantizedResiduals
#print axioms gate3_stoppableExactRecovery_closed
#print axioms stoppableGate4HorizonEinsteinAnalytic_closed
#print axioms stoppableTOEClosureTargets_closed

end

end UnifiedTheory.Audit.KFTOEStoppableFullClosureTarget
