/-
  Audit/KFCausalCSpecHarmonicBornSourceDrivenRank.lean

  AN EXPLICIT SOURCE-DRIVEN, WELL-FOUNDED GATE 3 SECTOR

  The general protected harmonic source cannot by itself force rank descent:
  the horizon projection may erase a distortion parallel to the horizon
  observable.  This file records that obstruction and then gives a concrete
  sector in which the missing update is constructed rather than assumed.

  In the constructive sector the horizon observable and quadratic corrector
  are zero.  The variance-safe projection is therefore the identity, so the
  displayed harmonic protected source is exactly minus the full physical
  distortion.  A negative-source site is selected and all four quantized
  defect channels at that site are repaired.  If the rank is nonzero such a
  site exists; its local rank is positive; hence the global natural rank
  strictly decreases.  At rank zero the source vanishes and the state is
  absorbing.  Thus `StoppableNatRankStep` is proved from an explicit update.

  This is an existence construction for a source-driven discrete repair
  dynamics.  It does not claim that the constant-horizon sector is selected
  by the microscopic causal-growth action, nor that it is the unique physical
  update.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornWellFoundedGate4Handoff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHarmonicBornSourceDrivenRank

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecVarianceSafeHorizonProjection
open UnifiedTheory.Audit.KFCausalCSpecBridgePoset
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedRank
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornProtectedWellFoundedGate3
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornWellFoundedGate4Handoff

/-! ## 1. Why a source-to-rank theorem cannot be unconditional -/

/-- A distortion parallel to a nonzero-variance horizon observable is erased
by the variance-safe projection.  Consequently, a nonzero protected source
cannot be deduced from nonzero distortion without an extra transversality
condition or a restricted horizon sector. -/
theorem varianceSafeHorizonOrthogonalResidual_self_eq_zero
    {ι : Type*} [Fintype ι]
    (w J : ι → ℝ) (hvar : variance w J ≠ 0) :
    varianceSafeHorizonOrthogonalResidual w J J = 0 := by
  have hcoeff : horizonProjectionCoeff w J J = 1 := by
    unfold horizonProjectionCoeff variance
    exact div_self hvar
  funext i
  simp [varianceSafeHorizonOrthogonalResidual, hvar,
    horizonOrthogonalResidual, hcoeff]

/-! ## 2. Quantized state and local repair -/

/-- The four discrete pieces counted by the Gate 3 natural defect rank. -/
structure QuantizedGate3State (ι : Type*) where
  countQuantum : ι → ℕ
  curvatureQuantum : ι → ℕ
  spectralQuantum : ι → ℕ
  candidate : ι → Equiv.Perm Direction

namespace QuantizedGate3State

variable {ι : Type*} [Fintype ι]

/-- The rank contribution of one observed site. -/
noncomputable def localDefectRank
    (edge : ι → E4) (s : QuantizedGate3State ι) (i : ι) : ℕ :=
  s.countQuantum i + s.curvatureQuantum i + s.spectralQuantum i +
    bridgeMismatchRank edge s.candidate i

/-- The global Gate 3 defect rank of a quantized state. -/
noncomputable def defectRank
    (edge : ι → E4) (s : QuantizedGate3State ι) : ℕ :=
  gate3DefectRank s.countQuantum s.curvatureQuantum s.spectralQuantum
    edge s.candidate

theorem defectRank_eq_sum_local
    (edge : ι → E4) (s : QuantizedGate3State ι) :
    s.defectRank edge = ∑ i, s.localDefectRank edge i := by
  simp [defectRank, gate3DefectRank, localDefectRank]

/-- An atomic site repair clears all three counters and replaces the bridge
candidate by the canonical transport at that site. -/
noncomputable def repairAt
    (edge : ι → E4) (s : QuantizedGate3State ι) (i : ι) :
    QuantizedGate3State ι := by
  classical
  exact
    { countQuantum := Function.update s.countQuantum i 0
      curvatureQuantum := Function.update s.curvatureQuantum i 0
      spectralQuantum := Function.update s.spectralQuantum i 0
      candidate := Function.update s.candidate i (fourState.perm (edge i)) }

@[simp] theorem localDefectRank_repairAt_self
    (edge : ι → E4) (s : QuantizedGate3State ι) (i : ι) :
    (s.repairAt edge i).localDefectRank edge i = 0 := by
  classical
  simp [localDefectRank, repairAt, bridgeMismatchRank]

theorem localDefectRank_repairAt_of_ne
    (edge : ι → E4) (s : QuantizedGate3State ι) {i j : ι}
    (hji : j ≠ i) :
    (s.repairAt edge i).localDefectRank edge j =
      s.localDefectRank edge j := by
  classical
  simp [localDefectRank, repairAt, bridgeMismatchRank, hji]

/-- Repairing a site with positive local defect strictly lowers the global
natural rank. -/
theorem defectRank_repairAt_lt
    (edge : ι → E4) (s : QuantizedGate3State ι) (i : ι)
    (hi : s.localDefectRank edge i ≠ 0) :
    (s.repairAt edge i).defectRank edge < s.defectRank edge := by
  classical
  rw [defectRank_eq_sum_local, defectRank_eq_sum_local]
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hji : j = i
    · subst j
      simp
    · rw [localDefectRank_repairAt_of_ne edge s hji]
  · exact ⟨i, Finset.mem_univ i, by
      rw [localDefectRank_repairAt_self]
      exact Nat.pos_of_ne_zero hi⟩

/-! ## 3. The negative-distortion source and its update -/

/-- Quantized count distortion at one state. -/
def countWindow (countGap : ℝ) (s : QuantizedGate3State ι) : ι → ℝ :=
  fun i => countGap * (s.countQuantum i : ℝ)

/-- Quantized curvature distortion at one state. -/
def curvatureBias
    (curvatureGap : ℝ) (s : QuantizedGate3State ι) : ι → ℝ :=
  fun i => curvatureGap * (s.curvatureQuantum i : ℝ)

/-- Quantized spectral distortion at one state. -/
def spectralLocality
    (spectralGap : ℝ) (s : QuantizedGate3State ι) : ι → ℝ :=
  fun i => spectralGap * (s.spectralQuantum i : ℝ)

/-- In the zero-horizon sector the protected repair source is exactly the
negative physical distortion. -/
noncomputable def negativeDistortionSource
    (countGap curvatureGap spectralGap scale : ℝ)
    (edge : ι → E4) (s : QuantizedGate3State ι) : ι → ℝ :=
  fun i =>
    -physicalHauptvermutungDistortion
      (countWindow countGap s)
      (curvatureBias curvatureGap s)
      (spectralLocality spectralGap s)
      scale edge s.candidate i

theorem negativeDistortionSource_neg_of_localDefectRank_ne_zero
    {countGap curvatureGap spectralGap scale : ℝ}
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (edge : ι → E4) (s : QuantizedGate3State ι) (i : ι)
    (hi : s.localDefectRank edge i ≠ 0) :
    negativeDistortionSource countGap curvatureGap spectralGap scale
      edge s i < 0 := by
  have hcount : 0 ≤ countWindow countGap s i :=
    mul_nonneg (le_of_lt hcountGap) (Nat.cast_nonneg _)
  have hcurvature : 0 ≤ curvatureBias curvatureGap s i :=
    mul_nonneg (le_of_lt hcurvatureGap) (Nat.cast_nonneg _)
  have hspectral : 0 ≤ spectralLocality spectralGap s i :=
    mul_nonneg (le_of_lt hspectralGap) (Nat.cast_nonneg _)
  have hnonneg :=
    physicalHauptvermutungDistortion_nonneg
      (countWindow countGap s)
      (curvatureBias curvatureGap s)
      (spectralLocality spectralGap s)
      scale edge s.candidate i hcount hcurvature hspectral
  have hne :
      physicalHauptvermutungDistortion
        (countWindow countGap s)
        (curvatureBias curvatureGap s)
        (spectralLocality spectralGap s)
        scale edge s.candidate i ≠ 0 := by
    intro hzero
    rcases
        (physicalHauptvermutungDistortion_zero_iff
          (countWindow countGap s)
          (curvatureBias curvatureGap s)
          (spectralLocality spectralGap s)
          scale edge s.candidate i hcount hcurvature hspectral).1 hzero with
      ⟨hc, hk, hs, hcandidate⟩
    have hcq : s.countQuantum i = 0 := by
      unfold countWindow at hc
      exact_mod_cast (mul_eq_zero.mp hc).resolve_left (ne_of_gt hcountGap)
    have hkq : s.curvatureQuantum i = 0 := by
      unfold curvatureBias at hk
      exact_mod_cast (mul_eq_zero.mp hk).resolve_left
        (ne_of_gt hcurvatureGap)
    have hsq : s.spectralQuantum i = 0 := by
      unfold spectralLocality at hs
      exact_mod_cast (mul_eq_zero.mp hs).resolve_left
        (ne_of_gt hspectralGap)
    apply hi
    simp [localDefectRank, bridgeMismatchRank, hcq, hkq, hsq, hcandidate]
  unfold negativeDistortionSource
  exact neg_neg_of_pos (lt_of_le_of_ne hnonneg (Ne.symm hne))

/-- A generic source-driven site update.  It repairs a site only when the
supplied source is negative there; otherwise it stops. -/
noncomputable def negativeSourceRepairStep
    (edge : ι → E4) (source : ι → ℝ) (s : QuantizedGate3State ι) :
    QuantizedGate3State ι :=
  if h : ∃ i, source i < 0 then
    s.repairAt edge (Classical.choose h)
  else
    s

/-- With the negative-distortion source, the explicit update strictly lowers
rank until zero and then remains at zero. -/
theorem negativeSourceRepairStep_rank
    {countGap curvatureGap spectralGap scale : ℝ}
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (edge : ι → E4) (s : QuantizedGate3State ι) :
    let source := negativeDistortionSource
      countGap curvatureGap spectralGap scale edge s
    (negativeSourceRepairStep edge source s).defectRank edge <
        s.defectRank edge ∨
      (s.defectRank edge = 0 ∧
        (negativeSourceRepairStep edge source s).defectRank edge = 0) := by
  dsimp only
  let source := negativeDistortionSource
    countGap curvatureGap spectralGap scale edge s
  by_cases h : ∃ i, source i < 0
  · rw [negativeSourceRepairStep, dif_pos h]
    apply Or.inl
    apply defectRank_repairAt_lt
    intro hlocal
    have hsourceNeg := Classical.choose_spec h
    have hsourceZero : source (Classical.choose h) = 0 := by
      unfold source negativeDistortionSource
      rw [(physicalHauptvermutungDistortion_zero_iff
        (countWindow countGap s)
        (curvatureBias curvatureGap s)
        (spectralLocality spectralGap s)
        scale edge s.candidate (Classical.choose h)
        (mul_nonneg (le_of_lt hcountGap) (Nat.cast_nonneg _))
        (mul_nonneg (le_of_lt hcurvatureGap) (Nat.cast_nonneg _))
        (mul_nonneg (le_of_lt hspectralGap) (Nat.cast_nonneg _))).2]
      · norm_num
      · have hsum := Nat.eq_zero_of_le_zero
          (show s.localDefectRank edge (Classical.choose h) ≤ 0 by
            rw [hlocal])
        have hcountZero : s.countQuantum (Classical.choose h) = 0 := by
          unfold localDefectRank at hsum
          omega
        have hcurvatureZero :
            s.curvatureQuantum (Classical.choose h) = 0 := by
          unfold localDefectRank at hsum
          omega
        have hspectralZero :
            s.spectralQuantum (Classical.choose h) = 0 := by
          unfold localDefectRank at hsum
          omega
        have hmismatch :
            bridgeMismatchRank edge s.candidate (Classical.choose h) = 0 := by
          unfold localDefectRank at hsum
          omega
        have hcandidate :
            s.candidate (Classical.choose h) =
              fourState.perm (edge (Classical.choose h)) := by
          by_contra hne
          simp [bridgeMismatchRank, hne] at hmismatch
        exact ⟨by simp [countWindow, hcountZero],
          by simp [curvatureBias, hcurvatureZero],
          by simp [spectralLocality, hspectralZero], hcandidate⟩
    linarith
  · rw [negativeSourceRepairStep, dif_neg h]
    apply Or.inr
    have hlocal : ∀ i, s.localDefectRank edge i = 0 := by
      intro i
      by_contra hi
      exact h ⟨i,
        negativeDistortionSource_neg_of_localDefectRank_ne_zero
          hcountGap hcurvatureGap hspectralGap edge s i hi⟩
    have hrank : s.defectRank edge = 0 := by
      rw [defectRank_eq_sum_local]
      exact Finset.sum_eq_zero fun i _ => hlocal i
    exact ⟨hrank, hrank⟩

/-! ## 4. Recursive source-driven trajectory -/

/-- The concrete quantized trajectory obtained by repeatedly applying the
negative protected source at the current state. -/
noncomputable def sourceDrivenTrajectory
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) : ℕ → QuantizedGate3State ι
  | 0 => initial
  | n + 1 =>
      let s := sourceDrivenTrajectory
        countGap curvatureGap spectralGap scale edge initial n
      negativeSourceRepairStep edge
        (negativeDistortionSource
          countGap curvatureGap spectralGap (scale n) edge s) s

@[simp] theorem sourceDrivenTrajectory_zero
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) :
    sourceDrivenTrajectory countGap curvatureGap spectralGap
      scale edge initial 0 = initial := by
  rfl

@[simp] theorem sourceDrivenTrajectory_succ
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) (n : ℕ) :
    sourceDrivenTrajectory countGap curvatureGap spectralGap
        scale edge initial (n + 1) =
      negativeSourceRepairStep edge
        (negativeDistortionSource countGap curvatureGap spectralGap (scale n)
          edge (sourceDrivenTrajectory countGap curvatureGap spectralGap
            scale edge initial n))
        (sourceDrivenTrajectory countGap curvatureGap spectralGap
          scale edge initial n) := by
  rfl

/-- The recursive trajectory satisfies the previously abstract stopping law. -/
theorem sourceDrivenTrajectory_rank_step
    {countGap curvatureGap spectralGap : ℝ}
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) :
    StoppableNatRankStep (fun n =>
      (sourceDrivenTrajectory countGap curvatureGap spectralGap
        scale edge initial n).defectRank edge) := by
  intro n
  change
    (sourceDrivenTrajectory countGap curvatureGap spectralGap
        scale edge initial (n + 1)).defectRank edge <
        (sourceDrivenTrajectory countGap curvatureGap spectralGap
          scale edge initial n).defectRank edge ∨
      ((sourceDrivenTrajectory countGap curvatureGap spectralGap
          scale edge initial n).defectRank edge = 0 ∧
        (sourceDrivenTrajectory countGap curvatureGap spectralGap
          scale edge initial (n + 1)).defectRank edge = 0)
  rw [sourceDrivenTrajectory_succ]
  exact negativeSourceRepairStep_rank
    hcountGap hcurvatureGap hspectralGap edge
      (sourceDrivenTrajectory countGap curvatureGap spectralGap
        scale edge initial n)

end QuantizedGate3State

/-! ## 5. Lift to the harmonic protected Gate 3 interface -/

variable {ι : Type*} [Fintype ι]

open QuantizedGate3State

/-- Counter sequence read from the explicit source-driven trajectory. -/
noncomputable def sourceDrivenCountQuantum
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) : ℕ → ι → ℕ :=
  fun n => (sourceDrivenTrajectory countGap curvatureGap spectralGap
    scale edge initial n).countQuantum

/-- Curvature-counter sequence read from the explicit trajectory. -/
noncomputable def sourceDrivenCurvatureQuantum
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) : ℕ → ι → ℕ :=
  fun n => (sourceDrivenTrajectory countGap curvatureGap spectralGap
    scale edge initial n).curvatureQuantum

/-- Spectral-counter sequence read from the explicit trajectory. -/
noncomputable def sourceDrivenSpectralQuantum
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) : ℕ → ι → ℕ :=
  fun n => (sourceDrivenTrajectory countGap curvatureGap spectralGap
    scale edge initial n).spectralQuantum

/-- Bridge-candidate sequence read from the explicit trajectory. -/
noncomputable def sourceDrivenCandidate
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) :
    ℕ → ι → Equiv.Perm Direction :=
  fun n => (sourceDrivenTrajectory countGap curvatureGap spectralGap
    scale edge initial n).candidate

/-- Real count defect obtained by multiplying the natural counter by its
positive quantum. -/
noncomputable def sourceDrivenCountWindow
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) : ℕ → ι → ℝ :=
  fun n => countWindow countGap
    (sourceDrivenTrajectory countGap curvatureGap spectralGap
      scale edge initial n)

/-- Real curvature defect obtained from its natural counter. -/
noncomputable def sourceDrivenCurvatureBias
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) : ℕ → ι → ℝ :=
  fun n => curvatureBias curvatureGap
    (sourceDrivenTrajectory countGap curvatureGap spectralGap
      scale edge initial n)

/-- Real spectral defect obtained from its natural counter. -/
noncomputable def sourceDrivenSpectralLocality
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) : ℕ → ι → ℝ :=
  fun n => spectralLocality spectralGap
    (sourceDrivenTrajectory countGap curvatureGap spectralGap
      scale edge initial n)

/-- The exact physical distortion total along the explicit trajectory. -/
noncomputable def sourceDrivenTotal
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) : ℕ → ℝ :=
  fun n => physicalHauptvermutungTotalDistortion
    (sourceDrivenCountWindow countGap curvatureGap spectralGap
      scale edge initial n)
    (sourceDrivenCurvatureBias countGap curvatureGap spectralGap
      scale edge initial n)
    (sourceDrivenSpectralLocality countGap curvatureGap spectralGap
      scale edge initial n)
    (scale n) edge
    (sourceDrivenCandidate countGap curvatureGap spectralGap
      scale edge initial n)

/-- On this trajectory the displayed harmonic protected source is literally
the negative physical distortion used by the update.  This is the explicit
source-to-state bridge absent from the general Gate 3 record. -/
theorem harmonicBornProtectedRepairSource_eq_negativeDistortionSource
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) (n : ℕ) :
    harmonicBornProtectedRepairSource chirality parentSchedule observe
        (fun _ _ => 0)
        (sourceDrivenCountWindow countGap curvatureGap spectralGap
          scale edge initial)
        (sourceDrivenCurvatureBias countGap curvatureGap spectralGap
          scale edge initial)
        (sourceDrivenSpectralLocality countGap curvatureGap spectralGap
          scale edge initial)
        (fun _ _ => 0) scale (fun _ => 0)
        (fun _ => edge)
        (sourceDrivenCandidate countGap curvatureGap spectralGap
          scale edge initial) n =
      negativeDistortionSource countGap curvatureGap spectralGap (scale n)
        edge (sourceDrivenTrajectory countGap curvatureGap spectralGap
          scale edge initial n) := by
  funext i
  simp [harmonicBornProtectedRepairSource,
    varianceSafeHorizonOrthogonalResidual, variance, covariance, expectation,
    harmonicBornPhysicalDistortion, negativeDistortionSource,
    sourceDrivenCountWindow, sourceDrivenCurvatureBias,
    sourceDrivenSpectralLocality, sourceDrivenCandidate]

/-- A nonzero defect rank produces a genuinely negative value of the actual
harmonic protected source at some site. -/
theorem exists_harmonicBornProtectedRepairSource_neg_of_rank_ne_zero
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    {countGap curvatureGap spectralGap : ℝ}
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) (n : ℕ)
    (hrank :
      (sourceDrivenTrajectory countGap curvatureGap spectralGap
        scale edge initial n).defectRank edge ≠ 0) :
    ∃ i,
      harmonicBornProtectedRepairSource chirality parentSchedule observe
        (fun _ _ => 0)
        (sourceDrivenCountWindow countGap curvatureGap spectralGap
          scale edge initial)
        (sourceDrivenCurvatureBias countGap curvatureGap spectralGap
          scale edge initial)
        (sourceDrivenSpectralLocality countGap curvatureGap spectralGap
          scale edge initial)
        (fun _ _ => 0) scale (fun _ => 0)
        (fun _ => edge)
        (sourceDrivenCandidate countGap curvatureGap spectralGap
          scale edge initial) n i < 0 := by
  let s := sourceDrivenTrajectory countGap curvatureGap spectralGap
    scale edge initial n
  have hexists :
      ∃ i, negativeDistortionSource
        countGap curvatureGap spectralGap (scale n) edge s i < 0 := by
    by_contra hnone
    push_neg at hnone
    have hlocal : ∀ i, s.localDefectRank edge i = 0 := by
      intro i
      by_contra hi
      exact (not_lt_of_ge (hnone i))
        (negativeDistortionSource_neg_of_localDefectRank_ne_zero
          hcountGap hcurvatureGap hspectralGap edge s i hi)
    apply hrank
    rw [defectRank_eq_sum_local]
    exact Finset.sum_eq_zero fun i _ => hlocal i
  rw [harmonicBornProtectedRepairSource_eq_negativeDistortionSource
    chirality parentSchedule observe countGap curvatureGap spectralGap
      scale edge initial n]
  exact hexists

/-- The full harmonic Gate 3 data record generated by the explicit trajectory.
Unlike the generic record constructor, this definition has no `rank_step`
argument: the rank law is discharged by the source-driven update theorem. -/
noncomputable def sourceDrivenHarmonicBornProtectedWellFoundedGate3Data
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (countGap curvatureGap spectralGap : ℝ)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (scale c : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) :
    HarmonicBornProtectedWellFoundedGate3Data chirality parentSchedule observe
      (fun _ _ => 0)
      (sourceDrivenCountWindow countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenCurvatureBias countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenSpectralLocality countGap curvatureGap spectralGap
        scale edge initial)
      (fun _ _ => 0) scale c
      (sourceDrivenTotal countGap curvatureGap spectralGap
        scale edge initial)
      (fun _ => 0) (fun _ => edge)
      (sourceDrivenCandidate countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenCountQuantum countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenCurvatureQuantum countGap curvatureGap spectralGap
        scale edge initial)
      (sourceDrivenSpectralQuantum countGap curvatureGap spectralGap
        scale edge initial)
      countGap curvatureGap spectralGap where
  leakage_null_cone_of_variance_ne_zero := by
    intro n hvar
    exfalso
    apply hvar
    simp [variance, covariance, expectation]
  countGap_pos := hcountGap
  curvatureGap_pos := hcurvatureGap
  spectralGap_pos := hspectralGap
  count_eq := by
    intro n i
    rfl
  curvature_eq := by
    intro n i
    rfl
  spectral_eq := by
    intro n i
    rfl
  total_eq := by
    intro n
    rfl
  rank_step := by
    exact sourceDrivenTrajectory_rank_step
      hcountGap hcurvatureGap hspectralGap scale edge initial

/-- The concrete source-driven construction therefore reaches the complete
Gate 3 closed interface, with recovery bound equal to its initial rank. -/
theorem sourceDrivenHarmonicBornProtectedWellFoundedGate3_closed
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (countGap curvatureGap spectralGap : ℝ)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (scale c : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) :
    (sourceDrivenHarmonicBornProtectedWellFoundedGate3Data
      chirality parentSchedule observe
      countGap curvatureGap spectralGap
      hcountGap hcurvatureGap hspectralGap
      scale c edge initial).Closed := by
  exact
    (sourceDrivenHarmonicBornProtectedWellFoundedGate3Data
      chirality parentSchedule observe
      countGap curvatureGap spectralGap
      hcountGap hcurvatureGap hspectralGap
      scale c edge initial).closed

/-! ## 6. Source-driven Gate 4 handoff -/

variable {X Y chart : Type*}
variable [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]

/-- Wire the explicit source-driven Gate 3 sector into the existing harmonic
Gate 4 interface.  No `rank_step` premise appears: only the independently
physical chart matching, affine density, and analytic kernel data remain as
arguments. -/
noncomputable def sourceDrivenHarmonicBornProtectedWellFoundedGate4Data
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (countGap curvatureGap spectralGap : ℝ)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (scale c : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι)
    (chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (countWindow_eq_sum : ∀ n,
      (chartCertificate n).countWindow =
        ∑ i, sourceDrivenCountWindow countGap curvatureGap spectralGap
          scale edge initial n i)
    (curvatureBias_eq_sum : ∀ n,
      (chartCertificate n).curvatureBias =
        ∑ i, sourceDrivenCurvatureBias countGap curvatureGap spectralGap
          scale edge initial n i)
    (pairConsistency_eq_spectral_sum : ∀ n,
      (chartCertificate n).pairConsistency =
        ∑ i, sourceDrivenSpectralLocality countGap curvatureGap spectralGap
          scale edge initial n i)
    (densityBase densityStep : ℝ)
    (densityStep_pos : 0 < densityStep)
    (density_eq_affine : ∀ n,
      (chartCertificate n).density =
        densityBase + densityStep * (n : ℝ))
    (operatorKernelData : BDG4DOperatorProfileKernelSplitData) :
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
      countGap curvatureGap spectralGap where
  gate3 := sourceDrivenHarmonicBornProtectedWellFoundedGate3Data
    chirality parentSchedule observe
    countGap curvatureGap spectralGap
    hcountGap hcurvatureGap hspectralGap scale c edge initial
  chartCertificate := chartCertificate
  countWindow_eq_sum := countWindow_eq_sum
  curvatureBias_eq_sum := curvatureBias_eq_sum
  pairConsistency_eq_spectral_sum := pairConsistency_eq_spectral_sum
  densityBase := densityBase
  densityStep := densityStep
  densityStep_pos := densityStep_pos
  density_eq_affine := density_eq_affine
  operatorKernelData := operatorKernelData

/-- The source-driven Gate 4 instance inherits exact finite recovery, eventual
zero chart distortion, the scheduled density limit, and the supplied analytic
operator limit without any separate dynamical-rank axiom. -/
theorem sourceDrivenHarmonicBornProtectedWellFoundedGate4_closed
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (countGap curvatureGap spectralGap : ℝ)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (scale c : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι)
    (chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (countWindow_eq_sum : ∀ n,
      (chartCertificate n).countWindow =
        ∑ i, sourceDrivenCountWindow countGap curvatureGap spectralGap
          scale edge initial n i)
    (curvatureBias_eq_sum : ∀ n,
      (chartCertificate n).curvatureBias =
        ∑ i, sourceDrivenCurvatureBias countGap curvatureGap spectralGap
          scale edge initial n i)
    (pairConsistency_eq_spectral_sum : ∀ n,
      (chartCertificate n).pairConsistency =
        ∑ i, sourceDrivenSpectralLocality countGap curvatureGap spectralGap
          scale edge initial n i)
    (densityBase densityStep : ℝ)
    (densityStep_pos : 0 < densityStep)
    (density_eq_affine : ∀ n,
      (chartCertificate n).density =
        densityBase + densityStep * (n : ℝ))
    (operatorKernelData : BDG4DOperatorProfileKernelSplitData)
    (errorScale : ℝ) :
    (sourceDrivenHarmonicBornProtectedWellFoundedGate4Data
      chirality parentSchedule observe
      countGap curvatureGap spectralGap
      hcountGap hcurvatureGap hspectralGap scale c edge initial
      chartCertificate countWindow_eq_sum curvatureBias_eq_sum
      pairConsistency_eq_spectral_sum densityBase densityStep
      densityStep_pos density_eq_affine operatorKernelData).Closed
        errorScale := by
  exact
    (sourceDrivenHarmonicBornProtectedWellFoundedGate4Data
      chirality parentSchedule observe
      countGap curvatureGap spectralGap
      hcountGap hcurvatureGap hspectralGap scale c edge initial
      chartCertificate countWindow_eq_sum curvatureBias_eq_sum
      pairConsistency_eq_spectral_sum densityBase densityStep
      densityStep_pos density_eq_affine operatorKernelData).closed errorScale

#print axioms varianceSafeHorizonOrthogonalResidual_self_eq_zero
#print axioms QuantizedGate3State.defectRank_repairAt_lt
#print axioms QuantizedGate3State.sourceDrivenTrajectory_rank_step
#print axioms harmonicBornProtectedRepairSource_eq_negativeDistortionSource
#print axioms exists_harmonicBornProtectedRepairSource_neg_of_rank_ne_zero
#print axioms sourceDrivenHarmonicBornProtectedWellFoundedGate3_closed
#print axioms sourceDrivenHarmonicBornProtectedWellFoundedGate4_closed

end

end UnifiedTheory.Audit.KFCausalCSpecHarmonicBornSourceDrivenRank
