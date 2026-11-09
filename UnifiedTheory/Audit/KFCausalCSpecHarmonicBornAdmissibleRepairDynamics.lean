/-
  Audit/KFCausalCSpecHarmonicBornAdmissibleRepairDynamics.lean

  CHOICE-INDEPENDENT HARMONIC BORN REPAIR DYNAMICS

  The explicit source-driven Gate-3 construction chooses one negative-source
  site with `Classical.choose`.  That proves existence of a terminating
  trajectory, but a physical law should not depend on that hidden selector.

  This module replaces the selector by a relation: an admissible step may
  repair any negative-source site, and it may remain fixed only when no such
  site exists.  Soundness and completeness of the source imply that every
  admissible trajectory has strict natural-rank descent away from zero and an
  absorbing zero state.  For the zero-horizon harmonic sector, negativity of
  the displayed protected source is equivalent to positive local defect, so
  the result applies to every allowed site choice.

  The resulting Gate-3 constructor has no `rank_step` argument and no hidden
  choice of repair site.  It does not claim that the vacuum spectator action
  supplies this repair relation; that final action-to-update identification
  remains an explicit physical selection frontier.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornSourceDrivenRank

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHarmonicBornAdmissibleRepairDynamics

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecBridgePoset
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedRank
open UnifiedTheory.Audit.KFCausalCSpecVarianceSafeHorizonProjection
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornProtectedWellFoundedGate3
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornSourceDrivenRank
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornSourceDrivenRank.QuantizedGate3State

/-! ## 1. A selector-free repair relation -/

variable {ι : Type*} [Fintype ι]

/-- One admissible repair step.  A negative-source site may be repaired, but a
stationary step is legal only when the source is nowhere negative.  This is a
relation rather than a function, so no arbitrary tie breaker is embedded in
the physical interface. -/
def NegativeSourceRepairTransition
    (edge : ι → E4) (source : ι → ℝ)
    (current next : QuantizedGate3State ι) : Prop :=
  (∃ i, source i < 0 ∧ next = current.repairAt edge i) ∨
    ((¬ ∃ i, source i < 0) ∧ next = current)

/-- Every admissible step driven by a sound and complete source either lowers
the global defect rank or stays at an already recovered zero state. -/
theorem negativeSourceRepairTransition_rank_of_detecting
    (edge : ι → E4) (source : ι → ℝ)
    (current next : QuantizedGate3State ι)
    (hstep : NegativeSourceRepairTransition edge source current next)
    (hsound : NegativeSourceSound edge source current)
    (hcomplete : NegativeSourceComplete edge source current) :
    next.defectRank edge < current.defectRank edge ∨
      (current.defectRank edge = 0 ∧ next.defectRank edge = 0) := by
  rcases hstep with hrepair | hstay
  · rcases hrepair with ⟨i, hi, rfl⟩
    exact Or.inl (defectRank_repairAt_lt edge current i (hsound i hi))
  · rcases hstay with ⟨hnone, hnext⟩
    subst next
    apply Or.inr
    have hrank : current.defectRank edge = 0 := by
      by_contra hne
      exact hnone (hcomplete hne)
    exact ⟨hrank, hrank⟩

/-- Pointwise admissible steps give the well-founded stopping law independently
of how a negative-source site is selected at each stage. -/
theorem admissibleRepairTrajectory_rank_step
    (edge : ι → E4)
    (source : ℕ → QuantizedGate3State ι → ι → ℝ)
    (state : ℕ → QuantizedGate3State ι)
    (hstep : ∀ n,
      NegativeSourceRepairTransition edge (source n (state n))
        (state n) (state (n + 1)))
    (hsound : ∀ n,
      NegativeSourceSound edge (source n (state n)) (state n))
    (hcomplete : ∀ n,
      NegativeSourceComplete edge (source n (state n)) (state n)) :
    StoppableNatRankStep (fun n => (state n).defectRank edge) := by
  intro n
  exact negativeSourceRepairTransition_rank_of_detecting
    edge (source n (state n)) (state n) (state (n + 1))
    (hstep n) (hsound n) (hcomplete n)

/-! ## 2. Exact detection by the negative physical distortion -/

/-- In the quantized zero-horizon sector, the negative physical distortion is
strictly negative exactly at the locally defective sites. -/
theorem negativeDistortionSource_neg_iff_localDefectRank_ne_zero
    {countGap curvatureGap spectralGap scale : ℝ}
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (edge : ι → E4) (state : QuantizedGate3State ι) (i : ι) :
    negativeDistortionSource countGap curvatureGap spectralGap scale
        edge state i < 0 ↔
      state.localDefectRank edge i ≠ 0 := by
  constructor
  · intro hnegative
    by_contra hlocal
    have hlocalZero : state.localDefectRank edge i = 0 := hlocal
    have hcountZero : state.countQuantum i = 0 := by
      unfold QuantizedGate3State.localDefectRank at hlocalZero
      omega
    have hcurvatureZero : state.curvatureQuantum i = 0 := by
      unfold QuantizedGate3State.localDefectRank at hlocalZero
      omega
    have hspectralZero : state.spectralQuantum i = 0 := by
      unfold QuantizedGate3State.localDefectRank at hlocalZero
      omega
    have hmismatch : bridgeMismatchRank edge state.candidate i = 0 := by
      unfold QuantizedGate3State.localDefectRank at hlocalZero
      omega
    have hcandidate : state.candidate i = fourState.perm (edge i) := by
      by_contra hne
      simp [bridgeMismatchRank, hne] at hmismatch
    have hsourceZero :
        negativeDistortionSource countGap curvatureGap spectralGap scale
            edge state i = 0 := by
      unfold negativeDistortionSource
      rw [(physicalHauptvermutungDistortion_zero_iff
        (QuantizedGate3State.countWindow countGap state)
        (QuantizedGate3State.curvatureBias curvatureGap state)
        (QuantizedGate3State.spectralLocality spectralGap state)
        scale edge state.candidate i
        (mul_nonneg (le_of_lt hcountGap) (Nat.cast_nonneg _))
        (mul_nonneg (le_of_lt hcurvatureGap) (Nat.cast_nonneg _))
        (mul_nonneg (le_of_lt hspectralGap) (Nat.cast_nonneg _))).2]
      · norm_num
      · exact ⟨by simp [QuantizedGate3State.countWindow, hcountZero],
          by simp [QuantizedGate3State.curvatureBias, hcurvatureZero],
          by simp [QuantizedGate3State.spectralLocality, hspectralZero],
          hcandidate⟩
    linarith
  · exact negativeDistortionSource_neg_of_localDefectRank_ne_zero
      hcountGap hcurvatureGap hspectralGap edge state i

/-- The negative physical distortion never selects a recovered site. -/
theorem negativeDistortionSource_sound
    {countGap curvatureGap spectralGap scale : ℝ}
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (edge : ι → E4) (state : QuantizedGate3State ι) :
    NegativeSourceSound edge
      (negativeDistortionSource countGap curvatureGap spectralGap scale
        edge state) state := by
  intro i hi
  exact (negativeDistortionSource_neg_iff_localDefectRank_ne_zero
    hcountGap hcurvatureGap hspectralGap edge state i).1 hi

/-- Every nonzero global defect exposes a negative physical-distortion site. -/
theorem negativeDistortionSource_complete
    {countGap curvatureGap spectralGap scale : ℝ}
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (edge : ι → E4) (state : QuantizedGate3State ι) :
    NegativeSourceComplete edge
      (negativeDistortionSource countGap curvatureGap spectralGap scale
        edge state) state := by
  intro hrank
  by_contra hnone
  push_neg at hnone
  apply hrank
  rw [QuantizedGate3State.defectRank_eq_sum_local]
  apply Finset.sum_eq_zero
  intro i _
  by_contra hi
  exact (not_lt_of_ge (hnone i))
    ((negativeDistortionSource_neg_iff_localDefectRank_ne_zero
      hcountGap hcurvatureGap hspectralGap edge state i).2 hi)

/-! ## 3. All admissible harmonic repair trajectories terminate -/

/-- A trajectory following the negative-distortion repair relation.  The
trajectory may choose different negative sites, but every allowed choice is
subject to the same physical source and update relation. -/
structure HarmonicBornAdmissibleRepairTrajectory
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) where
  state : ℕ → QuantizedGate3State ι
  state_zero : state 0 = initial
  step : ∀ n,
    NegativeSourceRepairTransition edge
      (negativeDistortionSource countGap curvatureGap spectralGap
        (scale n) edge (state n))
      (state n) (state (n + 1))

namespace HarmonicBornAdmissibleRepairTrajectory

variable {countGap curvatureGap spectralGap : ℝ}
variable {scale : ℕ → ℝ} {edge : ι → E4}
variable {initial : QuantizedGate3State ι}

variable
  (T : HarmonicBornAdmissibleRepairTrajectory
    countGap curvatureGap spectralGap scale edge initial)

/-- The relational dynamics has strict rank descent until an absorbing zero,
for every admissible sequence of site choices. -/
theorem rank_step
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap) :
    StoppableNatRankStep (fun n => (T.state n).defectRank edge) := by
  apply admissibleRepairTrajectory_rank_step edge
    (fun n state => negativeDistortionSource
      countGap curvatureGap spectralGap (scale n) edge state)
    T.state T.step
  · intro n
    exact negativeDistortionSource_sound
      hcountGap hcurvatureGap hspectralGap edge (T.state n)
  · intro n
    exact negativeDistortionSource_complete
      hcountGap hcurvatureGap hspectralGap edge (T.state n)

/-- The initial natural defect rank is a uniform recovery deadline for every
admissible selection of negative-source repair sites. -/
theorem defectRank_zero_after_initial
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap) :
    ∀ n, initial.defectRank edge ≤ n →
      (T.state n).defectRank edge = 0 := by
  intro n hn
  have hzero := (T.rank_step
    hcountGap hcurvatureGap hspectralGap).zero_after_initial_rank n
  rw [T.state_zero] at hzero
  exact hzero hn

/-- The earlier choice-based trajectory is one inhabitant of the relational
law, establishing that the admissible dynamics is nonempty. -/
noncomputable def sourceDriven
    (countGap curvatureGap spectralGap : ℝ)
    (scale : ℕ → ℝ) (edge : ι → E4)
    (initial : QuantizedGate3State ι) :
    HarmonicBornAdmissibleRepairTrajectory
      countGap curvatureGap spectralGap scale edge initial where
  state := sourceDrivenTrajectory
    countGap curvatureGap spectralGap scale edge initial
  state_zero := rfl
  step := by
    intro n
    rw [sourceDrivenTrajectory_succ]
    unfold negativeSourceRepairStep
    split
    next h =>
      exact Or.inl
        ⟨Classical.choose h, Classical.choose_spec h, rfl⟩
    next h =>
      exact Or.inr ⟨h, rfl⟩

/-! ## 4. Lift every admissible trajectory to the harmonic Gate-3 interface -/

noncomputable def countQuantum : ℕ → ι → ℕ :=
  fun n => (T.state n).countQuantum

noncomputable def curvatureQuantum : ℕ → ι → ℕ :=
  fun n => (T.state n).curvatureQuantum

noncomputable def spectralQuantum : ℕ → ι → ℕ :=
  fun n => (T.state n).spectralQuantum

noncomputable def candidate : ℕ → ι → Equiv.Perm Direction :=
  fun n => (T.state n).candidate

noncomputable def countWindow : ℕ → ι → ℝ :=
  fun n => QuantizedGate3State.countWindow countGap (T.state n)

noncomputable def curvatureBias : ℕ → ι → ℝ :=
  fun n => QuantizedGate3State.curvatureBias curvatureGap (T.state n)

noncomputable def spectralLocality : ℕ → ι → ℝ :=
  fun n => QuantizedGate3State.spectralLocality spectralGap (T.state n)

noncomputable def total : ℕ → ℝ :=
  fun n => physicalHauptvermutungTotalDistortion
    (T.countWindow n) (T.curvatureBias n) (T.spectralLocality n)
    (scale n) edge (T.candidate n)

/-- Along every admissible trajectory, the displayed zero-horizon harmonic
source is exactly the negative distortion that drives the relational update. -/
theorem protectedSource_eq_negativeDistortion
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (n : ℕ) :
    harmonicBornProtectedRepairSource chirality parentSchedule observe
        (fun _ _ => 0) T.countWindow T.curvatureBias T.spectralLocality
        (fun _ _ => 0) scale (fun _ => 0) (fun _ => edge) T.candidate n =
      negativeDistortionSource countGap curvatureGap spectralGap (scale n)
        edge (T.state n) := by
  funext i
  simp [harmonicBornProtectedRepairSource,
    varianceSafeHorizonOrthogonalResidual, variance, covariance, expectation,
    harmonicBornPhysicalDistortion, negativeDistortionSource,
    countWindow, curvatureBias, spectralLocality, candidate]

/-- Choice-independent Gate-3 data.  No `rank_step` or repair-site selector is
an argument; well-founded descent follows for every trajectory satisfying the
canonical negative-source repair relation. -/
noncomputable def toHarmonicBornProtectedWellFoundedGate3Data
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (c : ℕ → ℝ) :
    HarmonicBornProtectedWellFoundedGate3Data chirality parentSchedule observe
      (fun _ _ => 0) T.countWindow T.curvatureBias T.spectralLocality
      (fun _ _ => 0) scale c T.total (fun _ => 0) (fun _ => edge) T.candidate
      T.countQuantum T.curvatureQuantum T.spectralQuantum
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
    simpa [QuantizedGate3State.defectRank, countQuantum,
      curvatureQuantum, spectralQuantum, candidate] using
      T.rank_step hcountGap hcurvatureGap hspectralGap

/-- Complete harmonic Gate-3 closure for every admissible repair trajectory. -/
theorem closed
    (chirality : Fin 2)
    (parentSchedule :
      (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n)
    (observe : (n : ℕ) → CausalSetGrowthBranch n → ι)
    (hcountGap : 0 < countGap)
    (hcurvatureGap : 0 < curvatureGap)
    (hspectralGap : 0 < spectralGap)
    (c : ℕ → ℝ) :
    (T.toHarmonicBornProtectedWellFoundedGate3Data
      chirality parentSchedule observe
      hcountGap hcurvatureGap hspectralGap c).Closed := by
  exact
    (T.toHarmonicBornProtectedWellFoundedGate3Data
      chirality parentSchedule observe
      hcountGap hcurvatureGap hspectralGap c).closed

#print axioms negativeSourceRepairTransition_rank_of_detecting
#print axioms admissibleRepairTrajectory_rank_step
#print axioms negativeDistortionSource_neg_iff_localDefectRank_ne_zero
#print axioms negativeDistortionSource_sound
#print axioms negativeDistortionSource_complete
#print axioms rank_step
#print axioms defectRank_zero_after_initial
#print axioms protectedSource_eq_negativeDistortion
#print axioms toHarmonicBornProtectedWellFoundedGate3Data
#print axioms closed

end HarmonicBornAdmissibleRepairTrajectory

end

end UnifiedTheory.Audit.KFCausalCSpecHarmonicBornAdmissibleRepairDynamics
