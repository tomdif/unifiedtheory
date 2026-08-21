/-
  Audit/KFCausalCSpecRecoveredStageGRLimit.lean

  First finite bridge from exact recovered CSpec stages to the existing
  horizon-flux error-control interface.

  Scope: finite recovery-to-error plumbing only.  This file does not prove a
  continuum GR limit; it proves that the recovered-stage zero residuals feed the
  RSS/Poisson error budget used by the entropy-flux limit module.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
import UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

open Filter
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecGlobalization

theorem PhysicalHauptvermutungRecoveredStage.rssPoissonError_zero
    {ι : Type*} [Fintype ι]
    {countWindow curvatureBias spectralLocality : ι → ℝ}
    {scale total S : ℝ}
    {edge : ι → E4}
    {candidate : ι → Equiv.Perm Direction}
    (Rstage : PhysicalHauptvermutungRecoveredStage
      countWindow curvatureBias spectralLocality scale total edge candidate)
    (hcount : ∀ i, 0 ≤ countWindow i)
    (hcurvature : ∀ i, 0 ≤ curvatureBias i)
    (hspectral : ∀ i, 0 ≤ spectralLocality i)
    (i : ι) :
    rssPoissonError (countWindow i) (curvatureBias i) S = 0 := by
  rcases Rstage.residuals_zero hcount hcurvature hspectral with
    ⟨hcount_zero, hcurvature_zero, _hspectral_zero⟩
  unfold rssPoissonError
  rw [hcount_zero i, hcurvature_zero i]
  ring

theorem physicalHauptvermutungExactRecoveryCertificate_eventually_rssPoissonError_zero
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase residualGap S : ℝ}
    (C : PhysicalHauptvermutungExactRecoveryCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase residualGap) :
    ∀ᶠ n in atTop,
      ∀ i, rssPoissonError (countWindow n i) (curvatureBias n i) S = 0 := by
  have hrecovered :
      ∀ᶠ n in atTop,
        PhysicalHauptvermutungRecoveredStage
          (countWindow n) (curvatureBias n) (spectralLocality n)
          (scale n) (total n) (edge n) (candidate n) :=
    physicalHauptvermutungExactRecoveryCertificate_eventually_recoveredStage C
  filter_upwards [hrecovered] with n Rstage
  intro i
  exact Rstage.rssPoissonError_zero
    (C.convergence.count_nonneg n)
    (C.convergence.curvature_nonneg n)
    (C.convergence.spectral_nonneg n)
    i

theorem physicalHauptvermutungExactRecoveryCertificate_exists_rssPoissonError_zero_after
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase residualGap S : ℝ}
    (C : PhysicalHauptvermutungExactRecoveryCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase residualGap) :
    ∃ N, ∀ n, N ≤ n →
      ∀ i, rssPoissonError (countWindow n i) (curvatureBias n i) S = 0 := by
  have hz :
      ∀ᶠ n in atTop,
        ∀ i, rssPoissonError (countWindow n i) (curvatureBias n i) S = 0 :=
    physicalHauptvermutungExactRecoveryCertificate_eventually_rssPoissonError_zero C
  rw [eventually_atTop] at hz
  exact hz

#print axioms PhysicalHauptvermutungRecoveredStage.rssPoissonError_zero
#print axioms physicalHauptvermutungExactRecoveryCertificate_eventually_rssPoissonError_zero
#print axioms physicalHauptvermutungExactRecoveryCertificate_exists_rssPoissonError_zero_after

end UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
