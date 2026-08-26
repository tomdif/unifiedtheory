/-
  Audit/KFCausalCSpecHarmonicBornNonzeroBDGFrontier.lean

  NONZERO AND PHYSICAL-TARGET FRONTIER FOR THE HARMONIC GATE-4 HANDOFF

  The finite Gate-4 handoff already proves recovery, RSS/Poisson cancellation,
  chart-distortion convergence, density growth, and convergence of the selected
  reduced BDG profile.  Those facts do not imply that the selected profile has
  a nonzero target or that its target is the d'Alembertian of a physical field
  in a Lorentzian chart.

  This file keeps those two obligations visible.  The first theorem accepts
  the kernel-level `HasNonzeroBDG4DTarget` diagnostic directly and pairs it with
  the existing finite closure.  The physical frontier then records, without
  supplying an inhabitant, the missing typed chart/field realization and the
  identification of its target with the very same certificate sequence and
  kernel data used by the handoff.

  Curvature-sign audit: `bdg_dalembertian_continuum_limit` concludes at
  `boxPhi + (1/2) * curvaturePhi`, whereas
  `RecoveredStageBDGAsymptoticInterface.standard_bdg_dalembertian_tendsto`
  concludes at `boxPhi - (1/2) * curvaturePhi`.  The algebraic theorems at the
  end of this file show that these displayed targets differ by exactly
  `curvaturePhi`, and agree exactly in the curvature-zero case.  This does not
  choose a Riemann-tensor or d'Alembertian sign convention; that physical
  dictionary remains an explicit upstream obligation.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornWellFoundedGate4Handoff
import UnifiedTheory.Audit.KFCausalCSpecBDG4DCanonicalZeroKernel
import UnifiedTheory.Audit.KFCausalCSpecBDGContinuumLimit
import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDGInterface

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHarmonicBornNonzeroBDGFrontier

noncomputable section

open Filter Topology
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornProtectedWellFoundedGate3
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornWellFoundedGate4Handoff

variable {ι X Y chart : Type*} [Fintype ι]
variable [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
variable {chirality : Fin 2}
variable
  {parentSchedule :
    (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n}
variable {observe : (n : ℕ) → CausalSetGrowthBranch n → ι}
variable
  {J countWindow curvatureBias spectralLocality corrector : ℕ → ι → ℝ}
variable {scale c total correctorCoeff : ℕ → ℝ}
variable {edge : ℕ → ι → E4}
variable {candidate : ℕ → ι → Equiv.Perm Direction}
variable {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
variable {countGap curvatureGap spectralGap : ℝ}

variable
  (H : HarmonicBornProtectedWellFoundedGate4ScheduledKernelData
    (ι := ι) (X := X) (Y := Y) (chart := chart)
    chirality parentSchedule observe J
    countWindow curvatureBias spectralLocality corrector
    scale c total correctorCoeff edge candidate
    countQuantum curvatureQuantum spectralQuantum
    countGap curvatureGap spectralGap)

/-! ## Direct nonzero-target wrapper -/

/-- The strongest nonredundant finite Gate-4 wrapper: the pre-existing closure
is returned unchanged, paired with the diagnostic on its actual kernel data.
No auxiliary scalar target or equality can be chosen independently of `H`. -/
theorem closed_and_hasNonzeroBDG4DTarget
    (errorScale : ℝ)
    (hTarget : HasNonzeroBDG4DTarget H.operatorKernelData) :
    H.Closed errorScale ∧
      HasNonzeroBDG4DTarget H.operatorKernelData := by
  exact ⟨H.closed errorScale, hTarget⟩

/-! ## Typed physical chart/field target frontier -/

/-- The physical identification still absent from the finite Gate-4 handoff.

`PhysicalChart` and `PhysicalField` are deliberately abstract types.  The
three predicates make the missing physics explicit: the selected chart must
be Lorentzian, the actual Hauptvermutung certificate sequence in `H` must
generate that chart, and the chart must generate/realize the selected field.
Finally, the physical chart/field target is identified with the target of the
actual operator kernel in `H` and is required to be nonzero.

No constructor is provided: none of these physical-generation facts follows
from the finite causal-order data presently carried by `H`. -/
structure PhysicalBDGTargetIdentification
    (PhysicalChart PhysicalField : Type*)
    (IsLorentzianChart : PhysicalChart → Prop)
    (CertificateSequenceGeneratesChart :
      (ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart) →
        PhysicalChart → Prop)
    (ChartGeneratesField : PhysicalChart → PhysicalField → Prop)
    (physicalBDGTarget : PhysicalChart → PhysicalField → ℝ) where
  physicalChart : PhysicalChart
  physicalField : PhysicalField
  chart_isLorentzian : IsLorentzianChart physicalChart
  chart_generated_from_certificates :
    CertificateSequenceGeneratesChart H.chartCertificate physicalChart
  field_generated_from_chart :
    ChartGeneratesField physicalChart physicalField
  target_identification :
    BDG4DOperatorProfileData.target H.operatorKernelData.toProfileData =
      physicalBDGTarget physicalChart physicalField
  physical_target_ne_zero :
    physicalBDGTarget physicalChart physicalField ≠ 0

namespace PhysicalBDGTargetIdentification

variable {PhysicalChart PhysicalField : Type*}
variable {IsLorentzianChart : PhysicalChart → Prop}
variable
  {CertificateSequenceGeneratesChart :
    (ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart) →
      PhysicalChart → Prop}
variable {ChartGeneratesField : PhysicalChart → PhysicalField → Prop}
variable {physicalBDGTarget : PhysicalChart → PhysicalField → ℝ}

/-- A typed physical identification discharges the diagnostic on the same
kernel data used by the harmonic Gate-4 handoff. -/
theorem hasNonzeroBDG4DTarget
    (P : PhysicalBDGTargetIdentification H
      PhysicalChart PhysicalField IsLorentzianChart
      CertificateSequenceGeneratesChart ChartGeneratesField
      physicalBDGTarget) :
    HasNonzeroBDG4DTarget H.operatorKernelData := by
  unfold HasNonzeroBDG4DTarget
  rw [P.target_identification]
  exact P.physical_target_ne_zero

/-- Rewrite the already-proved sampled operator convergence to the typed,
identified, nonzero physical chart/field target.  The sampled mean, certificate
density, and kernel are definitionally the ones in `H`; only the codomain
target is rewritten by the frontier's physical identification. -/
theorem chart_operator_tendsto_identifiedPhysicalTarget
    (P : PhysicalBDGTargetIdentification H
      PhysicalChart PhysicalField IsLorentzianChart
      CertificateSequenceGeneratesChart ChartGeneratesField
      physicalBDGTarget) :
    Tendsto
      (fun n =>
        BDG4DOperatorProfileData.mean
          H.operatorKernelData.toProfileData
          ((H.chartCertificate n).density))
      atTop
      (𝓝 (physicalBDGTarget P.physicalChart P.physicalField)) := by
  have h := H.chart_operator_tendsto
  rw [P.target_identification] at h
  exact h

end PhysicalBDGTargetIdentification

/-! ## Curvature-coefficient convention mismatch -/

/-- The `+1/2` target displayed by `bdg_dalembertian_continuum_limit` minus the
`-1/2` target displayed by the recovered-stage standard theorem is exactly the
curvature contribution. -/
theorem plusHalfTarget_sub_minusHalfTarget
    (boxPhi curvaturePhi : ℝ) :
    (boxPhi + (1 / 2 : ℝ) * curvaturePhi) -
        (boxPhi - (1 / 2 : ℝ) * curvaturePhi) =
      curvaturePhi := by
  ring

/-- Consequently the two displayed curvature-coefficient conventions agree
if and only if the sampled curvature contribution vanishes. -/
theorem plusHalfTarget_eq_minusHalfTarget_iff
    (boxPhi curvaturePhi : ℝ) :
    boxPhi + (1 / 2 : ℝ) * curvaturePhi =
        boxPhi - (1 / 2 : ℝ) * curvaturePhi ↔
      curvaturePhi = 0 := by
  constructor
  · intro h
    linarith
  · rintro rfl
    ring

/-- A single real-valued sampled mean cannot converge to both convention
targets unless the curvature contribution vanishes. -/
theorem plusHalf_and_minusHalf_limits_force_curvature_zero
    (M : ℕ → ℝ) (boxPhi curvaturePhi : ℝ)
    (hplus : Tendsto M atTop
      (𝓝 (boxPhi + (1 / 2 : ℝ) * curvaturePhi)))
    (hminus : Tendsto M atTop
      (𝓝 (boxPhi - (1 / 2 : ℝ) * curvaturePhi))) :
    curvaturePhi = 0 := by
  apply
    (plusHalfTarget_eq_minusHalfTarget_iff boxPhi curvaturePhi).mp
  exact tendsto_nhds_unique hplus hminus

#print axioms closed_and_hasNonzeroBDG4DTarget
#print axioms PhysicalBDGTargetIdentification.hasNonzeroBDG4DTarget
#print axioms PhysicalBDGTargetIdentification.chart_operator_tendsto_identifiedPhysicalTarget
#print axioms plusHalfTarget_sub_minusHalfTarget
#print axioms plusHalfTarget_eq_minusHalfTarget_iff
#print axioms plusHalf_and_minusHalf_limits_force_curvature_zero

end

end UnifiedTheory.Audit.KFCausalCSpecHarmonicBornNonzeroBDGFrontier
