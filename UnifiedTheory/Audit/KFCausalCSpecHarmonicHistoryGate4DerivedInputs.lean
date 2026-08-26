/-
  Audit/KFCausalCSpecHarmonicHistoryGate4DerivedInputs.lean

  HARMONIC MICROSCOPIC HISTORY -> MAXIMAL HONEST GATE-4 INPUTS

  The explicit source-driven harmonic trajectory already determines the three
  scalar Hauptvermutung error channels and proves that they vanish after a
  finite natural-rank budget.  Its post-root branch at repair time `n` has the
  cardinality index `n+2`; after one positive density calibration this gives a
  concrete affine density schedule tending to infinity.

  What the microscopic record does not contain is a continuum realization:
  there are no coordinates, bilinear interval form, interval volumes, or
  chart-overlap estimates in an unlabeled causal-order history.  The structure
  `SourceDrivenHarmonicHistoryChartFrontier` below is exactly that remaining
  geometric supplier.  Unlike the previous Gate-4 record, it does not ask for
  arbitrary scalar windows, an arbitrary density sequence, an arbitrary full
  certificate sequence, or arbitrary BDG kernel data; all of those components
  are constructed here.

  Finally, a fully explicit `Fin 2`/one-chart benchmark discharges even this
  geometric frontier.  It proves consistency and end-to-end inhabitation of the
  repaired interface, but it is deliberately labelled a benchmark: its fixed
  two-event chart and zero continuum profile are not an identification of the
  growing microscopic causet with physical four-dimensional spacetime.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornSourceDrivenRank
import UnifiedTheory.Audit.KFCausalCSpecHauptvermutungDiagonalNoGo
import UnifiedTheory.Audit.KFCausalCSpecBDG4DCanonicalZeroKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHarmonicHistoryGate4DerivedInputs

noncomputable section

open Filter Topology
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecBridgePoset
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornProtectedWellFoundedGate3
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornWellFoundedGate4Handoff
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornSourceDrivenRank
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornSourceDrivenRank.QuantizedGate3State
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungDiagonalNoGo

/-! ## 1. Density scaling forced by the post-root rank -/

/-- A Gate-3 repair step `n` observes branches of
`CausalSetGrowthBranch (n+1)`, whose type index carries `n+2` events. -/
def harmonicPostRootEventCount (n : ℕ) : ℕ := n + 2

/-- Convert the exact event-count index into a real density parameter using one
positive physical calibration, `densityUnit`. -/
def harmonicHistoryDensity (densityUnit : ℝ) (n : ℕ) : ℝ :=
  densityUnit * (harmonicPostRootEventCount n : ℝ)

theorem harmonicHistoryDensity_eq_affine (densityUnit : ℝ) (n : ℕ) :
    harmonicHistoryDensity densityUnit n =
      2 * densityUnit + densityUnit * (n : ℝ) := by
  simp [harmonicHistoryDensity, harmonicPostRootEventCount]
  ring

theorem harmonicHistoryDensity_pos
    {densityUnit : ℝ} (hunit : 0 < densityUnit) (n : ℕ) :
    0 < harmonicHistoryDensity densityUnit n := by
  rw [harmonicHistoryDensity_eq_affine]
  positivity

theorem harmonicHistoryDensity_tendsto_atTop
    {densityUnit : ℝ} (hunit : 0 < densityUnit) :
    Tendsto (harmonicHistoryDensity densityUnit) atTop atTop := by
  have h := affineDensity_tendsto_atTop
    (2 * densityUnit) densityUnit hunit
  convert h using 1
  funext n
  exact harmonicHistoryDensity_eq_affine densityUnit n

/-! ## 2. Derived nonnegativity of the source-driven residual channels -/

theorem sourceDrivenCountWindow_nonneg
    {ι : Type*} [Fintype ι]
    {countGap curvatureGap spectralGap : ℝ}
    (hcountGap : 0 < countGap)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) (n : ℕ) (i : ι) :
    0 ≤ sourceDrivenCountWindow countGap curvatureGap spectralGap
      scale edge initial n i := by
  change 0 ≤ countGap *
    ((sourceDrivenTrajectory countGap curvatureGap spectralGap
      scale edge initial n).countQuantum i : ℝ)
  exact mul_nonneg hcountGap.le (Nat.cast_nonneg _)

theorem sourceDrivenCurvatureBias_nonneg
    {ι : Type*} [Fintype ι]
    {countGap curvatureGap spectralGap : ℝ}
    (hcurvatureGap : 0 < curvatureGap)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) (n : ℕ) (i : ι) :
    0 ≤ sourceDrivenCurvatureBias countGap curvatureGap spectralGap
      scale edge initial n i := by
  change 0 ≤ curvatureGap *
    ((sourceDrivenTrajectory countGap curvatureGap spectralGap
      scale edge initial n).curvatureQuantum i : ℝ)
  exact mul_nonneg hcurvatureGap.le (Nat.cast_nonneg _)

theorem sourceDrivenSpectralLocality_nonneg
    {ι : Type*} [Fintype ι]
    {countGap curvatureGap spectralGap : ℝ}
    (hspectralGap : 0 < spectralGap)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) (n : ℕ) (i : ι) :
    0 ≤ sourceDrivenSpectralLocality countGap curvatureGap spectralGap
      scale edge initial n i := by
  change 0 ≤ spectralGap *
    ((sourceDrivenTrajectory countGap curvatureGap spectralGap
      scale edge initial n).spectralQuantum i : ℝ)
  exact mul_nonneg hspectralGap.le (Nat.cast_nonneg _)

/-! ## 3. Nonzero physical BDG frontier -/

/-- The operator information still required when Gate 4 is meant to identify
a specified *nonzero* continuum target.  The microscopic harmonic history does
not choose this kernel or prove the displayed physical identification.

This frontier is intentionally stronger than mere Gate-4 interface
inhabitation.  It separates a genuine nonzero-target obligation from the
canonical zero-profile regression below. -/
structure SourceDrivenHarmonicHistoryPhysicalBDGFrontier
    (physicalTarget : ℝ) where
  kernelData : BDG4DOperatorProfileKernelSplitData
  physicalTarget_ne_zero : physicalTarget ≠ 0
  target_identification :
    BDG4DOperatorProfileData.target kernelData.toProfileData = physicalTarget

namespace SourceDrivenHarmonicHistoryPhysicalBDGFrontier

/-- A physically identified nonzero target satisfies the kernel-level
anti-vacuity diagnostic. -/
theorem hasNonzeroTarget
    {physicalTarget : ℝ}
    (P : SourceDrivenHarmonicHistoryPhysicalBDGFrontier physicalTarget) :
    HasNonzeroBDG4DTarget P.kernelData := by
  unfold HasNonzeroBDG4DTarget
  rw [P.target_identification]
  exact P.physicalTarget_ne_zero

end SourceDrivenHarmonicHistoryPhysicalBDGFrontier

/-! ## 4. Exact remaining physical chart frontier -/

/-- The continuum-geometric information absent from the harmonic microscopic
history.  Every scalar error bound and the density appearing here is already a
fixed function of the source-driven trajectory; only the actual realization
maps, interval counts, volumes, and their laws remain supplied. -/
structure SourceDrivenHarmonicHistoryChartFrontier
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) where
  densityUnit : ℝ
  densityUnit_pos : 0 < densityUnit
  B : ℕ → Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ
  B_symm : ∀ n x y, B n x y = B n y x
  G : ℕ → X → X → ℝ
  localChart : ℕ → chart → X → Y
  count : ℕ → chart → X → X → ℝ
  volume : ℕ → chart → X → X → ℝ
  scale_nonneg : ∀ n, 0 ≤ scale n
  G_self : ∀ n x, G n x x = 0
  G_pos : ∀ n x x', x ≠ x' → 0 < G n x x'
  G_le_scale : ∀ n x x', G n x x' ≤ scale n
  chart_count_eq : ∀ n i x x', x ≠ x' →
    B n (localChart n i x - localChart n i x')
        (localChart n i x - localChart n i x') =
      Real.sqrt
        (24 * count n i x x' /
          (Real.pi * harmonicHistoryDensity densityUnit n))
  count_nonneg : ∀ n i x x', 0 ≤ count n i x x'
  volume_pos : ∀ n i x x', x ≠ x' → 0 < volume n i x x'
  count_concentration : ∀ n i x x', x ≠ x' →
    |count n i x x' /
        (harmonicHistoryDensity densityUnit n * volume n i x x') - 1| ≤
      ∑ site, sourceDrivenCountWindow countGap curvatureGap spectralGap
        scale edge initial n site
  curvature_bias_bound : ∀ n i x x', x ≠ x' →
    |volume n i x x' / ((Real.pi / 24) * (G n x x') ^ 2) - 1| ≤
      ∑ site, sourceDrivenCurvatureBias countGap curvatureGap spectralGap
        scale edge initial n site
  chart_pair_consistency : ∀ n i j x x', x ≠ x' →
    |B n
        ((localChart n i x - localChart n i x') -
          (localChart n j x - localChart n j x'))
        ((localChart n i x - localChart n i x') -
          (localChart n j x - localChart n j x'))| ≤
      ∑ site, sourceDrivenSpectralLocality countGap curvatureGap spectralGap
        scale edge initial n site

namespace SourceDrivenHarmonicHistoryChartFrontier

variable {ι X Y chart : Type*} [Fintype ι]
variable [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
variable {countGap curvatureGap spectralGap : ℝ}
variable {scale : ℕ → ℝ} {edge : ι → E4}
variable {initial : QuantizedGate3State ι}

/-- Assemble the full repaired Hauptvermutung certificate at stage `n`.  Its
three windows and its density are definitions, not supplier fields. -/
noncomputable def chartCertificate
    (F : SourceDrivenHarmonicHistoryChartFrontier
      (ι := ι) (X := X) (Y := Y) (chart := chart)
      countGap curvatureGap spectralGap scale edge initial)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (n : ℕ) : PhysicalGrowthHauptvermutungCertificate X Y chart where
  B := F.B n
  B_symm := F.B_symm n
  G := F.G n
  pairConsistency :=
    ∑ site, sourceDrivenSpectralLocality countGap curvatureGap spectralGap
      scale edge initial n site
  countWindow :=
    ∑ site, sourceDrivenCountWindow countGap curvatureGap spectralGap
      scale edge initial n site
  curvatureBias :=
    ∑ site, sourceDrivenCurvatureBias countGap curvatureGap spectralGap
      scale edge initial n site
  scale := scale n
  density := harmonicHistoryDensity F.densityUnit n
  density_pos := harmonicHistoryDensity_pos F.densityUnit_pos n
  countWindow_nonneg := Finset.sum_nonneg fun i _ =>
    sourceDrivenCountWindow_nonneg hcountGap scale edge initial n i
  curvatureBias_nonneg := Finset.sum_nonneg fun i _ =>
    sourceDrivenCurvatureBias_nonneg hcurvatureGap scale edge initial n i
  scale_nonneg := F.scale_nonneg n
  pairConsistency_nonneg := Finset.sum_nonneg fun i _ =>
    sourceDrivenSpectralLocality_nonneg hspectralGap scale edge initial n i
  chart := F.localChart n
  count := F.count n
  volume := F.volume n
  G_self := F.G_self n
  G_pos := F.G_pos n
  G_le_scale := F.G_le_scale n
  chart_count_eq := F.chart_count_eq n
  count_nonneg := F.count_nonneg n
  volume_pos := F.volume_pos n
  count_concentration := F.count_concentration n
  curvature_bias_bound := F.curvature_bias_bound n
  chart_pair_consistency := F.chart_pair_consistency n

/-- The microscopic rank fixes the entire density sequence of the assembled
certificates up to the one positive conversion factor. -/
theorem chartCertificate_density
    (F : SourceDrivenHarmonicHistoryChartFrontier
      (ι := ι) (X := X) (Y := Y) (chart := chart)
      countGap curvatureGap spectralGap scale edge initial)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap) (n : ℕ) :
    (F.chartCertificate hcountGap hcurvatureGap hspectralGap n).density =
      harmonicHistoryDensity F.densityUnit n := rfl

/-- Assemble the existing harmonic Gate-4 handoff with no arbitrary
certificate sequence, density schedule, or operator-kernel argument. -/
noncomputable def toGate4Data
    (F : SourceDrivenHarmonicHistoryChartFrontier
      (ι := ι) (X := X) (Y := Y) (chart := chart)
      countGap curvatureGap spectralGap scale edge initial)
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (c : ℕ → ℝ) :
    HarmonicBornProtectedWellFoundedGate4ScheduledKernelData
      (ι := ι) (X := X) (Y := Y) (chart := chart)
      chirality parentSchedule observe
      (fun _ _ => 0)
      (sourceDrivenCountWindow countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenCurvatureBias countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenSpectralLocality countGap curvatureGap spectralGap
        scale edge initial)
      (fun _ _ => 0) scale c
      (sourceDrivenTotal countGap curvatureGap spectralGap scale edge initial)
      (fun _ => 0) (fun _ => edge)
      (sourceDrivenCandidate countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenCountQuantum countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenCurvatureQuantum countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenSpectralQuantum countGap curvatureGap spectralGap
        scale edge initial)
      countGap curvatureGap spectralGap :=
  sourceDrivenHarmonicBornProtectedWellFoundedGate4Data
    chirality parentSchedule observe
    countGap curvatureGap spectralGap
    hcountGap hcurvatureGap hspectralGap scale c edge initial
    (F.chartCertificate hcountGap hcurvatureGap hspectralGap)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (2 * F.densityUnit) F.densityUnit F.densityUnit_pos
    (fun n => by
      exact harmonicHistoryDensity_eq_affine F.densityUnit n)
    canonicalZeroBDG4DKernelData

/-- Assemble Gate-4 data for a specified nonzero continuum target.  Unlike
`toGate4Data`, this constructor cannot use the canonical zero-profile package:
the physical frontier carries both a nonzero target and its identification
with the supplied BDG profile target. -/
noncomputable def toPhysicalGate4Data
    (F : SourceDrivenHarmonicHistoryChartFrontier
      (ι := ι) (X := X) (Y := Y) (chart := chart)
      countGap curvatureGap spectralGap scale edge initial)
    (physicalTarget : ℝ)
    (P : SourceDrivenHarmonicHistoryPhysicalBDGFrontier physicalTarget)
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (c : ℕ → ℝ) :
    HarmonicBornProtectedWellFoundedGate4ScheduledKernelData
      (ι := ι) (X := X) (Y := Y) (chart := chart)
      chirality parentSchedule observe
      (fun _ _ => 0)
      (sourceDrivenCountWindow countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenCurvatureBias countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenSpectralLocality countGap curvatureGap spectralGap
        scale edge initial)
      (fun _ _ => 0) scale c
      (sourceDrivenTotal countGap curvatureGap spectralGap scale edge initial)
      (fun _ => 0) (fun _ => edge)
      (sourceDrivenCandidate countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenCountQuantum countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenCurvatureQuantum countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenSpectralQuantum countGap curvatureGap spectralGap
        scale edge initial)
      countGap curvatureGap spectralGap :=
  sourceDrivenHarmonicBornProtectedWellFoundedGate4Data
    chirality parentSchedule observe
    countGap curvatureGap spectralGap
    hcountGap hcurvatureGap hspectralGap scale c edge initial
    (F.chartCertificate hcountGap hcurvatureGap hspectralGap)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (2 * F.densityUnit) F.densityUnit F.densityUnit_pos
    (fun n => by
      exact harmonicHistoryDensity_eq_affine F.densityUnit n)
    P.kernelData

/-- The nonzero physical target obligation is retained by the assembled
Gate-4 record; it is not erased by the constructor. -/
theorem toPhysicalGate4Data_hasNonzeroTarget
    (F : SourceDrivenHarmonicHistoryChartFrontier
      (ι := ι) (X := X) (Y := Y) (chart := chart)
      countGap curvatureGap spectralGap scale edge initial)
    (physicalTarget : ℝ)
    (P : SourceDrivenHarmonicHistoryPhysicalBDGFrontier physicalTarget)
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (c : ℕ → ℝ) :
    HasNonzeroBDG4DTarget
      (F.toPhysicalGate4Data physicalTarget P chirality parentSchedule observe
        hcountGap hcurvatureGap hspectralGap c).operatorKernelData := by
  exact P.hasNonzeroTarget

/-- Every Gate-4 conclusion of the existing handoff follows from the explicit
history plus only the named continuum chart frontier. -/
theorem toGate4Data_closed
    (F : SourceDrivenHarmonicHistoryChartFrontier
      (ι := ι) (X := X) (Y := Y) (chart := chart)
      countGap curvatureGap spectralGap scale edge initial)
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (c : ℕ → ℝ) (errorScale : ℝ) :
    (F.toGate4Data chirality parentSchedule observe
      hcountGap hcurvatureGap hspectralGap c).Closed errorScale := by
  exact
    (F.toGate4Data chirality parentSchedule observe
      hcountGap hcurvatureGap hspectralGap c).closed errorScale

end SourceDrivenHarmonicHistoryChartFrontier

/-! ## 5. Fully concrete two-event benchmark -/

def harmonicHistoryFinTwoCount (densityUnit : ℝ) (n : ℕ)
    (x x' : Fin 2) : ℝ :=
  if x = x' then 0 else
    harmonicHistoryDensity densityUnit n * (Real.pi / 24)

def harmonicHistoryFinTwoVolume (x x' : Fin 2) : ℝ :=
  if x = x' then 0 else Real.pi / 24

private theorem pi_div_twentyFour_pos : 0 < Real.pi / 24 := by positivity

private theorem harmonicHistory_chart_ratio
    {densityUnit : ℝ} (hunit : 0 < densityUnit) (n : ℕ) :
    (24 : ℝ) *
        (harmonicHistoryDensity densityUnit n * (Real.pi / 24)) /
      (Real.pi * harmonicHistoryDensity densityUnit n) = 1 := by
  have hd := harmonicHistoryDensity_pos hunit n
  field_simp [ne_of_gt Real.pi_pos, ne_of_gt hd]

private theorem harmonicHistory_count_ratio
    {densityUnit : ℝ} (hunit : 0 < densityUnit) (n : ℕ) :
    (harmonicHistoryDensity densityUnit n * (Real.pi / 24)) /
      (harmonicHistoryDensity densityUnit n * (Real.pi / 24)) = 1 := by
  have hd := harmonicHistoryDensity_pos hunit n
  exact div_self (mul_ne_zero (ne_of_gt hd) (ne_of_gt pi_div_twentyFour_pos))

private theorem finTwoCoordinate_bilinear_eq_one_of_ne
    (x x' : Fin 2) (h : x ≠ x') :
    realMulBilinear (finTwoCoordinate x - finTwoCoordinate x')
      (finTwoCoordinate x - finTwoCoordinate x') = 1 := by
  fin_cases x <;> fin_cases x' <;>
    simp_all [realMulBilinear, finTwoCoordinate]

/-- A concrete benchmark chart frontier.  It uses exact two-point interval
geometry at every rank; the only rank dependence is the history-derived density
and the three source-driven error allowances. -/
noncomputable def sourceDrivenHarmonicHistoryFinTwoFrontier
    {ι : Type*} [Fintype ι]
    (countGap curvatureGap spectralGap : ℝ)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (edge : ι → E4) (initial : QuantizedGate3State ι)
    (densityUnit : ℝ) (hunit : 0 < densityUnit) :
    SourceDrivenHarmonicHistoryChartFrontier
      (X := Fin 2) (Y := ℝ) (chart := Fin 1)
      countGap curvatureGap spectralGap (fun _ => 1) edge initial where
  densityUnit := densityUnit
  densityUnit_pos := hunit
  B := fun _ => realMulBilinear
  B_symm := by
    intro n x y
    simp [realMulBilinear]
    ring
  G := fun _ => finTwoInterval
  localChart := fun _ _ x => finTwoCoordinate x
  count := fun n _ x x' => harmonicHistoryFinTwoCount densityUnit n x x'
  volume := fun _ _ x x' => harmonicHistoryFinTwoVolume x x'
  scale_nonneg := by norm_num
  G_self := by simp [finTwoInterval]
  G_pos := by
    intro n x x' h
    simp [finTwoInterval, h]
  G_le_scale := by
    intro n x x'
    by_cases h : x = x' <;> simp [finTwoInterval, h]
  chart_count_eq := by
    intro n i x x' h
    rw [finTwoCoordinate_bilinear_eq_one_of_ne x x' h]
    simp only [harmonicHistoryFinTwoCount, if_neg h]
    rw [harmonicHistory_chart_ratio hunit n, Real.sqrt_one]
  count_nonneg := by
    intro n i x x'
    by_cases h : x = x'
    · simp [harmonicHistoryFinTwoCount, h]
    · simp only [harmonicHistoryFinTwoCount, if_neg h]
      exact mul_nonneg (harmonicHistoryDensity_pos hunit n).le
        pi_div_twentyFour_pos.le
  volume_pos := by
    intro n i x x' h
    simpa [harmonicHistoryFinTwoVolume, h] using pi_div_twentyFour_pos
  count_concentration := by
    intro n i x x' h
    simp only [harmonicHistoryFinTwoCount, harmonicHistoryFinTwoVolume,
      if_neg h]
    rw [harmonicHistory_count_ratio hunit n, sub_self, abs_zero]
    exact Finset.sum_nonneg fun site _ =>
      sourceDrivenCountWindow_nonneg hcountGap (fun _ => 1) edge initial n site
  curvature_bias_bound := by
    intro n i x x' h
    simp only [harmonicHistoryFinTwoVolume, finTwoInterval, if_neg h,
      one_pow]
    have hratio :
        (Real.pi / 24) / (Real.pi / 24 * 1) = (1 : ℝ) := by
      field_simp [ne_of_gt Real.pi_pos]
    rw [hratio, sub_self, abs_zero]
    exact Finset.sum_nonneg fun site _ =>
      sourceDrivenCurvatureBias_nonneg hcurvatureGap
        (fun _ => 1) edge initial n site
  chart_pair_consistency := by
    intro n i j x x' h
    have hij : i = j := Subsingleton.elim i j
    subst j
    simp only [sub_self, map_zero, abs_zero]
    exact Finset.sum_nonneg fun site _ =>
      sourceDrivenSpectralLocality_nonneg hspectralGap
        (fun _ => 1) edge initial n site

/-- End-to-end Gate-4 data for the explicit two-event benchmark.  There is no
chart-certificate, density-schedule, rank-step, or operator-kernel argument. -/
noncomputable def sourceDrivenHarmonicHistoryFinTwoGate4Data
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (countGap curvatureGap spectralGap : ℝ)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (c : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι)
    (densityUnit : ℝ) (hunit : 0 < densityUnit) :=
  (sourceDrivenHarmonicHistoryFinTwoFrontier
    countGap curvatureGap spectralGap
    hcountGap hcurvatureGap hspectralGap edge initial densityUnit hunit).toGate4Data
      chirality parentSchedule observe
      hcountGap hcurvatureGap hspectralGap c

/-- The concrete benchmark inherits finite exact recovery, zero asymptotic
chart distortion, divergent history density, and the exact zero-profile BDG
operator limit. -/
theorem sourceDrivenHarmonicHistoryFinTwoGate4_closed
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (countGap curvatureGap spectralGap : ℝ)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (c : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι)
    (densityUnit : ℝ) (hunit : 0 < densityUnit)
    (errorScale : ℝ) :
    (sourceDrivenHarmonicHistoryFinTwoGate4Data
      chirality parentSchedule observe
      countGap curvatureGap spectralGap
      hcountGap hcurvatureGap hspectralGap c edge initial
      densityUnit hunit).Closed errorScale := by
  exact
    (sourceDrivenHarmonicHistoryFinTwoGate4Data
      chirality parentSchedule observe
      countGap curvatureGap spectralGap
      hcountGap hcurvatureGap hspectralGap c edge initial
      densityUnit hunit).closed errorScale

#print axioms harmonicHistoryDensity_tendsto_atTop
#print axioms SourceDrivenHarmonicHistoryChartFrontier.chartCertificate
#print axioms SourceDrivenHarmonicHistoryChartFrontier.toGate4Data
#print axioms SourceDrivenHarmonicHistoryPhysicalBDGFrontier.hasNonzeroTarget
#print axioms SourceDrivenHarmonicHistoryChartFrontier.toPhysicalGate4Data
#print axioms SourceDrivenHarmonicHistoryChartFrontier.toPhysicalGate4Data_hasNonzeroTarget
#print axioms SourceDrivenHarmonicHistoryChartFrontier.toGate4Data_closed
#print axioms sourceDrivenHarmonicHistoryFinTwoFrontier
#print axioms sourceDrivenHarmonicHistoryFinTwoGate4Data
#print axioms sourceDrivenHarmonicHistoryFinTwoGate4_closed

end

end UnifiedTheory.Audit.KFCausalCSpecHarmonicHistoryGate4DerivedInputs
