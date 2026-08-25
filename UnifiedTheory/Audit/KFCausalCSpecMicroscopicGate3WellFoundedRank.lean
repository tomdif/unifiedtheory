/-
  Audit/KFCausalCSpecMicroscopicGate3WellFoundedRank.lean

  A well-founded, finite-time Gate 3 recovery route.

  The real-contraction route proves exact recovery by first proving convergence
  and then invoking positive residual gaps.  This file instead uses the
  discrete data already present in the model.  Its defect rank is the finite
  sum of the three natural residual occupations and one bridge-mismatch bit at
  every site.  Thus rank zero is definitionally the complete quantized vacuum
  with canonical bridge transport.

  The only new dynamical premise is `StoppableNatRankStep`: at each update the
  rank either strictly decreases, or both the current and next ranks are zero.
  Well-foundedness of `Nat` then gives exact recovery at stage `rank 0`, and
  zero remains absorbing forever.  No asymptotic convergence, real contraction
  factor, rate floor, or recovery conclusion is assumed.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3StoppableDirectRate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedRank

open Filter
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecBridgePoset
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3StoppableDirectRate

/-! ## 1. The finite quantum/bridge defect rank -/

/-- One unit of rank records a noncanonical bridge candidate at a site. -/
noncomputable def bridgeMismatchRank
    {ι : Type*} (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction) (i : ι) : ℕ :=
  if candidate i = fourState.perm (edge i) then 0 else 1

/-- The discrete Gate 3 defect rank: all three occupation counters plus one
bit for each incorrect bridge transport. -/
noncomputable def gate3DefectRank
    {ι : Type*} [Fintype ι]
    (countQuantum curvatureQuantum spectralQuantum : ι → ℕ)
    (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction) : ℕ :=
  Finset.univ.sum (fun i =>
    countQuantum i + curvatureQuantum i + spectralQuantum i +
      bridgeMismatchRank edge candidate i)

/-- Rank zero has no hidden analytic content: it is exactly simultaneous
vacuum of all natural residual counters and canonical bridge transport. -/
theorem gate3DefectRank_eq_zero_iff
    {ι : Type*} [Fintype ι]
    (countQuantum curvatureQuantum spectralQuantum : ι → ℕ)
    (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction) :
    gate3DefectRank countQuantum curvatureQuantum spectralQuantum
        edge candidate = 0 ↔
      (∀ i, countQuantum i = 0) ∧
        (∀ i, curvatureQuantum i = 0) ∧
          (∀ i, spectralQuantum i = 0) ∧
            candidate = canonicalCSpecBridgeCandidate edge := by
  constructor
  · intro hrank
    have hterm :
        ∀ i,
          countQuantum i + curvatureQuantum i + spectralQuantum i +
              bridgeMismatchRank edge candidate i = 0 := by
      intro i
      have hsum :
          Finset.univ.sum (fun j =>
            countQuantum j + curvatureQuantum j + spectralQuantum j +
              bridgeMismatchRank edge candidate j) = 0 := by
        simpa [gate3DefectRank] using hrank
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => Nat.zero_le _)).1 hsum i (Finset.mem_univ i)
    have hcount : ∀ i, countQuantum i = 0 := by
      intro i
      have hi := hterm i
      omega
    have hcurvature : ∀ i, curvatureQuantum i = 0 := by
      intro i
      have hi := hterm i
      omega
    have hspectral : ∀ i, spectralQuantum i = 0 := by
      intro i
      have hi := hterm i
      omega
    have hcandidate :
        candidate = canonicalCSpecBridgeCandidate edge := by
      funext i
      have hmismatch : bridgeMismatchRank edge candidate i = 0 := by
        have hi := hterm i
        omega
      have heq : candidate i = fourState.perm (edge i) := by
        by_contra hne
        simp [bridgeMismatchRank, hne] at hmismatch
      simpa [canonicalCSpecBridgeCandidate] using heq
    exact ⟨hcount, hcurvature, hspectral, hcandidate⟩
  · rintro ⟨hcount, hcurvature, hspectral, hcandidate⟩
    subst candidate
    simp [gate3DefectRank, bridgeMismatchRank,
      canonicalCSpecBridgeCandidate, hcount, hcurvature, hspectral]

/-! ## 2. Abstract well-founded stopping theorem -/

/-- A maximally atomic discrete update law.  Every step is either a strict
rank decrease, or an absorbing zero-to-zero step. -/
def StoppableNatRankStep (rank : ℕ → ℕ) : Prop :=
  ∀ n, rank (n + 1) < rank n ∨ (rank n = 0 ∧ rank (n + 1) = 0)

theorem StoppableNatRankStep.next_lt_of_ne_zero
    {rank : ℕ → ℕ} (hstep : StoppableNatRankStep rank)
    {n : ℕ} (hne : rank n ≠ 0) :
    rank (n + 1) < rank n := by
  rcases hstep n with hlt | hzero
  · exact hlt
  · exact False.elim (hne hzero.1)

theorem StoppableNatRankStep.next_eq_zero_of_eq_zero
    {rank : ℕ → ℕ} (hstep : StoppableNatRankStep rank)
    {n : ℕ} (hzero : rank n = 0) :
    rank (n + 1) = 0 := by
  rcases hstep n with hlt | hstay
  · omega
  · exact hstay.2

/-- A rank bounded by `budget` is zero after at most `budget` further steps.
This is induction on the budget, not a limit argument. -/
theorem StoppableNatRankStep.zero_after_budget
    {rank : ℕ → ℕ} (hstep : StoppableNatRankStep rank) :
    ∀ (n budget : ℕ), rank n ≤ budget → rank (n + budget) = 0 := by
  intro n budget
  induction budget generalizing n with
  | zero =>
      intro hbound
      simpa using Nat.eq_zero_of_le_zero hbound
  | succ budget ih =>
      intro hbound
      by_cases hzero : rank n = 0
      · have hnext : rank (n + 1) = 0 :=
          hstep.next_eq_zero_of_eq_zero hzero
        have htail : rank ((n + 1) + budget) = 0 :=
          ih (n + 1) (by rw [hnext]; exact Nat.zero_le _)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
      · have hlt : rank (n + 1) < rank n :=
          hstep.next_lt_of_ne_zero hzero
        have hnext_bound : rank (n + 1) ≤ budget := by omega
        have htail : rank ((n + 1) + budget) = 0 :=
          ih (n + 1) hnext_bound
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Starting from zero, the rank is zero at every later offset. -/
theorem StoppableNatRankStep.zero_add_of_zero
    {rank : ℕ → ℕ} (hstep : StoppableNatRankStep rank)
    {n : ℕ} (hzero : rank n = 0) :
    ∀ k, rank (n + k) = 0 := by
  intro k
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
      have hnext := hstep.next_eq_zero_of_eq_zero ih
      simpa [Nat.add_assoc] using hnext

/-- The initial rank itself is an explicit exact-recovery time. -/
theorem StoppableNatRankStep.zero_at_initial_rank
    {rank : ℕ → ℕ} (hstep : StoppableNatRankStep rank) :
    rank (rank 0) = 0 := by
  simpa using hstep.zero_after_budget 0 (rank 0) (le_refl _)

/-- Recovery is permanent at and after the explicit initial-rank bound. -/
theorem StoppableNatRankStep.zero_after_initial_rank
    {rank : ℕ → ℕ} (hstep : StoppableNatRankStep rank) :
    ∀ n, rank 0 ≤ n → rank n = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact hstep.zero_add_of_zero hstep.zero_at_initial_rank k

/-! ## 3. Physical Gate 3 data with one discrete update premise -/

/-- Quantized Gate 3 data whose termination principle is well-founded rank
descent rather than real asymptotic contraction.

`refinement` retains the certified horizon-preserving physical update.  The
sole additional dynamical obligation is `rank_step`; none of the conclusions
about convergence, exact recovery, or a recovery stage appear as fields. -/
structure MicroscopicGate3WellFoundedRankData
    {ι : Type*} [Fintype ι]
    (w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (scale c step descentRate remainder total : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction)
    (countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ)
    (countGap curvatureGap spectralGap : ℝ) : Prop where
  refinement :
    StoppablePhysicalGrowthRepairRefinement w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
  countGap_pos : 0 < countGap
  curvatureGap_pos : 0 < curvatureGap
  spectralGap_pos : 0 < spectralGap
  count_eq :
    ∀ n i, countWindow n i = countGap * (countQuantum n i : ℝ)
  curvature_eq :
    ∀ n i, curvatureBias n i = curvatureGap * (curvatureQuantum n i : ℝ)
  spectral_eq :
    ∀ n i, spectralLocality n i = spectralGap * (spectralQuantum n i : ℝ)
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

namespace MicroscopicGate3WellFoundedRankData

variable {ι : Type*} [Fintype ι]
variable {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
variable {scale c step descentRate remainder total : ℕ → ℝ}
variable {edge : ℕ → ι → E4}
variable {candidate : ℕ → ι → Equiv.Perm Direction}
variable {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
variable {countGap curvatureGap spectralGap : ℝ}

variable
  (D : MicroscopicGate3WellFoundedRankData w J source
    countWindow curvatureBias spectralLocality
    scale c step descentRate remainder total edge candidate
    countQuantum curvatureQuantum spectralQuantum
    countGap curvatureGap spectralGap)

include D

/-- The stagewise discrete defect rank. -/
noncomputable def defectRank
    (_D : MicroscopicGate3WellFoundedRankData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap)
    (n : ℕ) : ℕ :=
  gate3DefectRank
    (countQuantum n) (curvatureQuantum n) (spectralQuantum n)
    (edge n) (candidate n)

theorem defectRank_step : StoppableNatRankStep D.defectRank := by
  exact D.rank_step

/-- Exact zero-characterization specialized to the data record. -/
theorem defectRank_eq_zero_iff (n : ℕ) :
    D.defectRank n = 0 ↔
      (∀ i, countQuantum n i = 0) ∧
        (∀ i, curvatureQuantum n i = 0) ∧
          (∀ i, spectralQuantum n i = 0) ∧
            candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  exact
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

/-- Rank zero gives exact real residual zero, zero physical total distortion,
and canonical bridge transport at the same stage. -/
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

/-- Rank zero constructs the operational recovered-stage predicate consumed
by Gate 4; recovery is not a field of the data record. -/
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
        exact
          bridge_incidence_recovers_transport fourState (edge n i) a b hcov
            (fourState_src_ne_dst (edge n i)) }

/-- The discrete rank is not merely sufficient for recovery: with positive
quantization gaps it is exactly the operational recovered-stage predicate. -/
theorem defectRank_eq_zero_iff_recoveredStage (n : ℕ) :
    D.defectRank n = 0 ↔
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  constructor
  · exact D.recoveredStage_of_defectRank_eq_zero
  · intro R
    rcases R.residuals_zero
        (D.count_nonneg n) (D.curvature_nonneg n) (D.spectral_nonneg n) with
      ⟨hcount, hcurvature, hspectral⟩
    apply (D.defectRank_eq_zero_iff n).2
    refine ⟨?_, ?_, ?_, R.candidate_eq_canonical⟩
    · intro i
      have hmul : countGap * (countQuantum n i : ℝ) = 0 := by
        rw [← D.count_eq n i, hcount i]
      have hcast : (countQuantum n i : ℝ) = 0 :=
        (mul_eq_zero.mp hmul).resolve_left (ne_of_gt D.countGap_pos)
      exact_mod_cast hcast
    · intro i
      have hmul : curvatureGap * (curvatureQuantum n i : ℝ) = 0 := by
        rw [← D.curvature_eq n i, hcurvature i]
      have hcast : (curvatureQuantum n i : ℝ) = 0 :=
        (mul_eq_zero.mp hmul).resolve_left (ne_of_gt D.curvatureGap_pos)
      exact_mod_cast hcast
    · intro i
      have hmul : spectralGap * (spectralQuantum n i : ℝ) = 0 := by
        rw [← D.spectral_eq n i, hspectral i]
      have hcast : (spectralQuantum n i : ℝ) = 0 :=
        (mul_eq_zero.mp hmul).resolve_left (ne_of_gt D.spectralGap_pos)
      exact_mod_cast hcast

/-- Both protected horizon responses remain zero at every discrete update. -/
theorem horizonProtection :
    ∀ n,
      linearResponse (w n) (source n) (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse (w n) (source n)
          (finiteAreaChange (c n) (J n)) = 0 := by
  intro n
  exact D.refinement.step_protected n

/-- Exact recovery occurs by the explicit stage equal to the initial defect
rank. -/
theorem recoveredStage_at_initial_defectRank :
    PhysicalHauptvermutungRecoveredStage
      (countWindow (D.defectRank 0))
      (curvatureBias (D.defectRank 0))
      (spectralLocality (D.defectRank 0))
      (scale (D.defectRank 0)) (total (D.defectRank 0))
      (edge (D.defectRank 0)) (candidate (D.defectRank 0)) := by
  exact
    D.recoveredStage_of_defectRank_eq_zero
      D.defectRank_step.zero_at_initial_rank

/-- The rank is zero permanently from the explicit bound `defectRank 0`. -/
theorem defectRank_zero_after_initial_bound :
    ∀ n, D.defectRank 0 ≤ n → D.defectRank n = 0 := by
  exact D.defectRank_step.zero_after_initial_rank

/-- The full exact-zero characterization, including all real residuals and
canonical transport, is permanent from the explicit initial-rank bound. -/
theorem exact_zero_after_initial_defectRank :
    ∀ n, D.defectRank 0 ≤ n →
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  intro n hn
  exact
    D.exact_zero_of_defectRank_eq_zero
      (D.defectRank_zero_after_initial_bound n hn)

/-- Operational Gate 3 recovery is permanent from the same explicit bound. -/
theorem recoveredStage_after_initial_defectRank :
    ∀ n, D.defectRank 0 ≤ n →
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  intro n hn
  exact
    D.recoveredStage_of_defectRank_eq_zero
      (D.defectRank_zero_after_initial_bound n hn)

/-- Filter-form exact recovery, derived from the explicit finite bound for
compatibility with the existing Gate 3-to-Gate 4 interfaces. -/
theorem eventually_exact_zero :
    ∀ᶠ n in atTop,
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  rw [eventually_atTop]
  exact ⟨D.defectRank 0, D.exact_zero_after_initial_defectRank⟩

/-- Filter-form recovered-stage tail, again with witness exactly `defectRank
0`. -/
theorem eventually_recoveredStage :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  rw [eventually_atTop]
  exact ⟨D.defectRank 0, D.recoveredStage_after_initial_defectRank⟩

/-- A single finite bound packages horizon protection and the permanent
recovered tail, with no appeal to topology or asymptotics. -/
theorem horizonProtection_and_bounded_exact_recovery :
    (∀ n,
      linearResponse (w n) (source n) (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse (w n) (source n)
          (finiteAreaChange (c n) (J n)) = 0) ∧
      ∀ n, D.defectRank 0 ≤ n →
        PhysicalHauptvermutungRecoveredStage
          (countWindow n) (curvatureBias n) (spectralLocality n)
          (scale n) (total n) (edge n) (candidate n) := by
  exact ⟨D.horizonProtection, D.recoveredStage_after_initial_defectRank⟩

#print axioms gate3DefectRank_eq_zero_iff
#print axioms StoppableNatRankStep.zero_after_budget
#print axioms StoppableNatRankStep.zero_at_initial_rank
#print axioms StoppableNatRankStep.zero_after_initial_rank
#print axioms defectRank_eq_zero_iff
#print axioms exact_zero_of_defectRank_eq_zero
#print axioms defectRank_eq_zero_iff_recoveredStage
#print axioms recoveredStage_at_initial_defectRank
#print axioms exact_zero_after_initial_defectRank
#print axioms recoveredStage_after_initial_defectRank
#print axioms eventually_exact_zero
#print axioms eventually_recoveredStage
#print axioms horizonProtection_and_bounded_exact_recovery

end MicroscopicGate3WellFoundedRankData

end UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedRank
