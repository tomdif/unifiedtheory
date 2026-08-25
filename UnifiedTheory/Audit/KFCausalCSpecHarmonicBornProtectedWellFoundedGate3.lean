/-
  Audit/KFCausalCSpecHarmonicBornProtectedWellFoundedGate3.lean

  HARMONIC BORN LAW ON AN ACTION-SELECTED RAW SCHEDULE -> GATE 3

  This is the leanest current microscopic Gate 3 route.  The probability
  weights come from the canonical Born-shell completion of the harmonic raw
  coupling schedule selected by the vacuum spectator action.  The completion
  itself is a separate construction.  The repair source is a totalized
  horizon-orthogonal two-channel source that remains defined at zero variance.

  Once physical evolution supplies strict descent of the natural-valued defect
  rank, real contraction rates, Taylor remainders, step floors, asymptotic
  convergence, and positive residual gaps are unnecessary for termination.
  Nat well-foundedness gives exact recovery by the initial rank and forever
  after it.  The remaining dynamical premise is explicit and local:
  `rank_step`.  This file proves horizon protection of the displayed source
  and finite termination from that rank law; deriving the rank law from an
  actual source-driven causal update remains a physical bridge.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalBornObservedWeight
import UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedRank
import UnifiedTheory.Audit.KFCausalCSpecVarianceSafeHorizonProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHarmonicBornProtectedWellFoundedGate3

noncomputable section

open Filter
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalBornObservedWeight
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecVarianceSafeHorizonProjection
open UnifiedTheory.Audit.KFCausalCSpecBridgePoset
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedRank

/-- Gate 3 repair time starts after the deterministic causal root.  Time `n`
therefore observes causal-growth stage `n + 1`.  The variance-safe projection
would also be defined at the root; this indexing convention simply does not
count the forced first birth as a repair update. -/
noncomputable def harmonicPostRootGate3Weight
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι) :
    ℕ → ι → ℝ :=
  fun n =>
    harmonicObservedBornWeight
      chirality parentSchedule observe (n + 1)

/-- The full physical distortion observable used by the harmonic repair law. -/
noncomputable def harmonicBornPhysicalDistortion
    {ι : Type*} [Fintype ι]
    (countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (scale : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction) :
    ℕ → ι → ℝ :=
  fun n =>
    physicalHauptvermutungDistortion
      (countWindow n) (curvatureBias n) (spectralLocality n)
      (scale n) (edge n) (candidate n)

/-- The protected repair source belonging to the harmonic Born weights. -/
noncomputable def harmonicBornProtectedRepairSource
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (J countWindow curvatureBias spectralLocality corrector : ℕ → ι → ℝ)
    (scale correctorCoeff : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction) :
    ℕ → ι → ℝ :=
  fun n i =>
    -varianceSafeHorizonOrthogonalResidual
        (harmonicPostRootGate3Weight chirality parentSchedule observe n)
        (J n)
        (harmonicBornPhysicalDistortion
          countWindow curvatureBias spectralLocality scale edge candidate n) i +
      correctorCoeff n *
        varianceSafeHorizonOrthogonalResidual
          (harmonicPostRootGate3Weight chirality parentSchedule observe n)
          (J n) (corrector n) i

/-- Slim Gate 3 data.  All analytic repair-rate machinery has been replaced by
one natural-rank transition law.  The two horizon fields are finite geometric
certificates for the source and are not termination assumptions.  In
particular, this record does not assert an update equation deriving
`rank_step` from `harmonicBornProtectedRepairSource`. -/
structure HarmonicBornProtectedWellFoundedGate3Data
    {ι : Type*} [Fintype ι]
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (J countWindow curvatureBias spectralLocality corrector : ℕ → ι → ℝ)
    (scale c total correctorCoeff : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction)
    (countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ)
    (countGap curvatureGap spectralGap : ℝ) : Prop where
  leakage_null_cone_of_variance_ne_zero :
    ∀ n,
      variance
          (harmonicPostRootGate3Weight chirality parentSchedule observe n)
          (J n) ≠ 0 →
      horizonSecondOrderLeakageQuadratic
        (harmonicPostRootGate3Weight chirality parentSchedule observe n)
        (J n)
        (varianceSafeHorizonOrthogonalResidual
          (harmonicPostRootGate3Weight chirality parentSchedule observe n)
          (J n)
          (harmonicBornPhysicalDistortion
            countWindow curvatureBias spectralLocality
            scale edge candidate n))
        (varianceSafeHorizonOrthogonalResidual
          (harmonicPostRootGate3Weight chirality parentSchedule observe n)
          (J n) (corrector n))
        (-1) (correctorCoeff n) = 0
  countGap_pos : 0 < countGap
  curvatureGap_pos : 0 < curvatureGap
  spectralGap_pos : 0 < spectralGap
  count_eq :
    ∀ n i, countWindow n i = countGap * (countQuantum n i : ℝ)
  curvature_eq :
    ∀ n i,
      curvatureBias n i = curvatureGap * (curvatureQuantum n i : ℝ)
  spectral_eq :
    ∀ n i,
      spectralLocality n i = spectralGap * (spectralQuantum n i : ℝ)
  total_eq :
    ∀ n,
      total n =
        physicalHauptvermutungTotalDistortion
          (countWindow n) (curvatureBias n) (spectralLocality n)
          (scale n) (edge n) (candidate n)
  rank_step :
    StoppableNatRankStep (fun n =>
      gate3DefectRank
        (countQuantum n) (curvatureQuantum n) (spectralQuantum n)
        (edge n) (candidate n))

namespace HarmonicBornProtectedWellFoundedGate3Data

variable {ι : Type*} [Fintype ι]
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
  (D : HarmonicBornProtectedWellFoundedGate3Data
    chirality parentSchedule observe J
    countWindow curvatureBias spectralLocality corrector
    scale c total correctorCoeff edge candidate
    countQuantum curvatureQuantum spectralQuantum
    countGap curvatureGap spectralGap)

include D

/-- The harmonic Gate 3 weights are derived, nonnegative probabilities. -/
theorem weight_nonneg :
    ∀ n i,
      0 ≤ harmonicPostRootGate3Weight
        chirality parentSchedule observe n i :=
  fun n i =>
    harmonicObservedBornWeight_nonneg
      chirality parentSchedule observe (n + 1) i

/-- The same derived weights have unit total mass at every stage. -/
theorem weight_sum_one (n : ℕ) :
    (∑ i,
      harmonicPostRootGate3Weight
        chirality parentSchedule observe n i) = 1 :=
  harmonicObservedBornWeight_sum_one
    chirality parentSchedule observe (n + 1)

/-- The canonical two-channel source preserves the horizon area through both
the first and finite second central response.  No descent-rate hypothesis is
used. -/
theorem horizonProtection :
    ∀ n,
      linearResponse
          (harmonicPostRootGate3Weight chirality parentSchedule observe n)
          (harmonicBornProtectedRepairSource
            chirality parentSchedule observe J
            countWindow curvatureBias spectralLocality corrector
            scale correctorCoeff edge candidate n)
          (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse
          (harmonicPostRootGate3Weight chirality parentSchedule observe n)
          (harmonicBornProtectedRepairSource
            chirality parentSchedule observe J
            countWindow curvatureBias spectralLocality corrector
            scale correctorCoeff edge candidate n)
          (finiteAreaChange (c n) (J n)) = 0 := by
  intro n
  let w := harmonicPostRootGate3Weight chirality parentSchedule observe n
  let G := harmonicBornPhysicalDistortion
    countWindow curvatureBias spectralLocality scale edge candidate n
  let A := varianceSafeHorizonOrthogonalResidual w (J n) G
  let B := varianceSafeHorizonOrthogonalResidual w (J n) (corrector n)
  have hsource :
      harmonicBornProtectedRepairSource
          chirality parentSchedule observe J
          countWindow curvatureBias spectralLocality corrector
          scale correctorCoeff edge candidate n =
        fun i => (-1 : ℝ) * A i + correctorCoeff n * B i := by
    funext i
    simp only [harmonicBornProtectedRepairSource]
    change -A i + correctorCoeff n * B i = _
    ring
  rw [hsource]
  have hA : covariance w A (J n) = 0 :=
    covariance_varianceSafeHorizonOrthogonalResidual_self
      w (J n) G (D.weight_nonneg n) (D.weight_sum_one n)
  have hB : covariance w B (J n) = 0 :=
    covariance_varianceSafeHorizonOrthogonalResidual_self
      w (J n) (corrector n) (D.weight_nonneg n) (D.weight_sum_one n)
  have hcone :
      horizonSecondOrderLeakageQuadratic
        w (J n) A B (-1) (correctorCoeff n) = 0 := by
    by_cases hvar : variance w (J n) = 0
    · unfold horizonSecondOrderLeakageQuadratic
      rw [horizonSecondOrderCrossLeakage_eq_zero_of_variance_eq_zero
          w (J n) A A (D.weight_nonneg n) (D.weight_sum_one n) hvar,
        horizonSecondOrderCrossLeakage_eq_zero_of_variance_eq_zero
          w (J n) A B (D.weight_nonneg n) (D.weight_sum_one n) hvar,
        horizonSecondOrderCrossLeakage_eq_zero_of_variance_eq_zero
          w (J n) B B (D.weight_nonneg n) (D.weight_sum_one n) hvar]
      ring
    · exact D.leakage_null_cone_of_variance_ne_zero n hvar
  constructor
  · rw [linearResponse_eq_covariance]
    rw [covariance_finiteAreaChange_eq_neg_covariance
      w (J n) (fun i => (-1 : ℝ) * A i + correctorCoeff n * B i)
      (c n) (D.weight_sum_one n)]
    rw [covariance_add_right]
    rw [covariance_const_mul_right, covariance_const_mul_right]
    rw [covariance_comm w (J n) A, covariance_comm w (J n) B]
    rw [hA, hB]
    ring
  · rw [quadraticResponse_finiteAreaChange_eq_neg_leakageQuadratic
      w (J n) A B (c n) (-1) (correctorCoeff n)
      (D.weight_sum_one n)]
    rw [hcone]
    ring

/-- Stagewise finite defect rank. -/
noncomputable def defectRank
    (_D : HarmonicBornProtectedWellFoundedGate3Data
      chirality parentSchedule observe J
      countWindow curvatureBias spectralLocality corrector
      scale c total correctorCoeff edge candidate
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap)
    (n : ℕ) : ℕ :=
  gate3DefectRank
    (countQuantum n) (curvatureQuantum n) (spectralQuantum n)
    (edge n) (candidate n)

theorem defectRank_step : StoppableNatRankStep D.defectRank :=
  D.rank_step

theorem defectRank_eq_zero_iff (n : ℕ) :
    D.defectRank n = 0 ↔
      (∀ i, countQuantum n i = 0) ∧
        (∀ i, curvatureQuantum n i = 0) ∧
          (∀ i, spectralQuantum n i = 0) ∧
            candidate n = canonicalCSpecBridgeCandidate (edge n) :=
  gate3DefectRank_eq_zero_iff
    (countQuantum n) (curvatureQuantum n) (spectralQuantum n)
    (edge n) (candidate n)

theorem count_nonneg (n : ℕ) (i : ι) : 0 ≤ countWindow n i := by
  rw [D.count_eq n i]
  exact mul_nonneg (le_of_lt D.countGap_pos) (Nat.cast_nonneg _)

theorem curvature_nonneg (n : ℕ) (i : ι) : 0 ≤ curvatureBias n i := by
  rw [D.curvature_eq n i]
  exact mul_nonneg (le_of_lt D.curvatureGap_pos) (Nat.cast_nonneg _)

theorem spectral_nonneg (n : ℕ) (i : ι) : 0 ≤ spectralLocality n i := by
  rw [D.spectral_eq n i]
  exact mul_nonneg (le_of_lt D.spectralGap_pos) (Nat.cast_nonneg _)

/-- Rank zero is simultaneous exact real defect zero and canonical bridge
transport. -/
theorem exact_zero_of_defectRank_eq_zero
    {n : ℕ} (hrank : D.defectRank n = 0) :
    total n = 0 ∧
      (∀ i, countWindow n i = 0) ∧
        (∀ i, curvatureBias n i = 0) ∧
          (∀ i, spectralLocality n i = 0) ∧
            candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  rcases (D.defectRank_eq_zero_iff n).1 hrank with
    ⟨hcountQuantum, hcurvatureQuantum, hspectralQuantum, hcandidate⟩
  have hcount : ∀ i, countWindow n i = 0 := by
    intro i
    rw [D.count_eq n i, hcountQuantum i]
    norm_num
  have hcurvature : ∀ i, curvatureBias n i = 0 := by
    intro i
    rw [D.curvature_eq n i, hcurvatureQuantum i]
    norm_num
  have hspectral : ∀ i, spectralLocality n i = 0 := by
    intro i
    rw [D.spectral_eq n i, hspectralQuantum i]
    norm_num
  have htotal : total n = 0 := by
    rw [D.total_eq n]
    exact
      (physicalHauptvermutungTotalDistortion_eq_zero_iff
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (edge n) (candidate n)
        (D.count_nonneg n) (D.curvature_nonneg n)
        (D.spectral_nonneg n)).2
        ⟨hcount, hcurvature, hspectral, hcandidate⟩
  exact ⟨htotal, hcount, hcurvature, hspectral, hcandidate⟩

/-- Rank zero supplies the exact operational predicate consumed by Gate 4. -/
theorem recoveredStage_of_defectRank_eq_zero
    {n : ℕ} (hrank : D.defectRank n = 0) :
    PhysicalHauptvermutungRecoveredStage
      (countWindow n) (curvatureBias n) (spectralLocality n)
      (scale n) (total n) (edge n) (candidate n) := by
  rcases D.exact_zero_of_defectRank_eq_zero hrank with
    ⟨htotal, hcount, hcurvature, hspectral, hcandidate⟩
  have hcandidate_at :
      ∀ i, candidate n i = fourState.perm (edge n i) := by
    intro i
    simpa [canonicalCSpecBridgeCandidate] using congrFun hcandidate i
  exact
    { total_zero := htotal
      local_distortion_zero := fun i =>
        (physicalHauptvermutungDistortion_zero_iff
          (countWindow n) (curvatureBias n) (spectralLocality n)
          (scale n) (edge n) (candidate n) i
          (D.count_nonneg n i) (D.curvature_nonneg n i)
          (D.spectral_nonneg n i)).2
          ⟨hcount i, hcurvature i, hspectral i, hcandidate_at i⟩
      bridge_total_zero :=
        (cSpecBridgeTotalDistortion_eq_zero_iff_candidate_eq_canonical
          (scale n) (edge n) (candidate n)).2 hcandidate
      order_recovered := fun i a b hcov => by
        rw [hcandidate_at i]
        exact bridge_incidence_recovers_transport
          fourState (edge n i) a b hcov (fourState_src_ne_dst (edge n i)) }

/-- Exact recovery occurs no later than the initial natural defect rank. -/
theorem recoveredStage_at_initial_defectRank :
    PhysicalHauptvermutungRecoveredStage
      (countWindow (D.defectRank 0))
      (curvatureBias (D.defectRank 0))
      (spectralLocality (D.defectRank 0))
      (scale (D.defectRank 0)) (total (D.defectRank 0))
      (edge (D.defectRank 0)) (candidate (D.defectRank 0)) := by
  exact D.recoveredStage_of_defectRank_eq_zero
    D.defectRank_step.zero_at_initial_rank

theorem exact_zero_after_initial_defectRank :
    ∀ n, D.defectRank 0 ≤ n →
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  intro n hn
  exact D.exact_zero_of_defectRank_eq_zero
    (D.defectRank_step.zero_after_initial_rank n hn)

theorem recoveredStage_after_initial_defectRank :
    ∀ n, D.defectRank 0 ≤ n →
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  intro n hn
  exact D.recoveredStage_of_defectRank_eq_zero
    (D.defectRank_step.zero_after_initial_rank n hn)

theorem eventually_exact_zero :
    ∀ᶠ n in Filter.atTop,
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  filter_upwards [eventually_ge_atTop (D.defectRank 0)] with n hn
  exact D.exact_zero_after_initial_defectRank n hn

theorem eventually_recoveredStage :
    ∀ᶠ n in Filter.atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  filter_upwards [eventually_ge_atTop (D.defectRank 0)] with n hn
  exact D.recoveredStage_after_initial_defectRank n hn

/-- Complete mathematical output of the slim harmonic Gate 3. -/
structure Closed : Prop where
  normalizedWeights : ∀ n,
    (∑ i,
      harmonicPostRootGate3Weight
        chirality parentSchedule observe n i) = 1
  nonnegativeWeights : ∀ n i,
    0 ≤ harmonicPostRootGate3Weight
      chirality parentSchedule observe n i
  horizonProtected :
    ∀ n,
      linearResponse
          (harmonicPostRootGate3Weight chirality parentSchedule observe n)
          (harmonicBornProtectedRepairSource
            chirality parentSchedule observe J
            countWindow curvatureBias spectralLocality corrector
            scale correctorCoeff edge candidate n)
          (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse
          (harmonicPostRootGate3Weight chirality parentSchedule observe n)
          (harmonicBornProtectedRepairSource
            chirality parentSchedule observe J
            countWindow curvatureBias spectralLocality corrector
            scale correctorCoeff edge candidate n)
          (finiteAreaChange (c n) (J n)) = 0
  explicitRecoveryBound : ∀ n, D.defectRank 0 ≤ n →
    PhysicalHauptvermutungRecoveredStage
      (countWindow n) (curvatureBias n) (spectralLocality n)
      (scale n) (total n) (edge n) (candidate n)

theorem closed : D.Closed where
  normalizedWeights := D.weight_sum_one
  nonnegativeWeights := D.weight_nonneg
  horizonProtected := D.horizonProtection
  explicitRecoveryBound := D.recoveredStage_after_initial_defectRank

#print axioms horizonProtection
#print axioms exact_zero_of_defectRank_eq_zero
#print axioms recoveredStage_at_initial_defectRank
#print axioms recoveredStage_after_initial_defectRank
#print axioms eventually_recoveredStage
#print axioms closed

end HarmonicBornProtectedWellFoundedGate3Data

end


end UnifiedTheory.Audit.KFCausalCSpecHarmonicBornProtectedWellFoundedGate3
