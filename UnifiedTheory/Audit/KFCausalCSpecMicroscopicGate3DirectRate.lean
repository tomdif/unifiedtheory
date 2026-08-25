/-
  Audit/KFCausalCSpecMicroscopicGate3DirectRate.lean

  First aggregate-rate Gate 3 attempt (retained for consistency audit).

  The older componentwise centered-source target asks every centered source
  component to be uniformly negative.  That cannot hold for normalized
  weights because the weighted expectation of a centered source is zero.
  The physical contraction theorem only needs the aggregate descent rate, so
  this file packages that weaker hypothesis and carries it to eventual exact
  Hauptvermutung recovery.  A later audit found that the embedded
  `PhysicalGrowthRepairRefinement` still requires strictly positive descent at
  every stage, including after exact recovery.  Therefore the complete record
  below is uninhabited; see
  `KFCausalCSpecMicroscopicGate3DirectRateStrictNoGo.lean`.  It remains here to
  preserve the proof history.  The corrected supplier is
  `KFCausalCSpecMicroscopicGate3StoppableDirectRate.lean`.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3DirectRate

open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecBridgePoset
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open Filter Topology
open scoped BigOperators

/-- Historical raw Gate 3 data stated with the aggregate descent inequality
used by the contraction proof.  The aggregate inequality itself is compatible
with normalized weights, but this record is not: its embedded strict-forever
refinement conflicts with eventual nonnegative exact recovery. -/
structure MicroscopicGate3DirectRateQuantizedData
    {ι : Type*} [Fintype ι]
    (w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (scale c step descentRate remainder total : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction)
    (countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ)
    (rateBase stepFloor countGap curvatureGap spectralGap : ℝ) : Prop where
  refinement :
    PhysicalGrowthRepairRefinement w J source
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
  rateBase_pos : 0 < rateBase
  stepFloor_pos : 0 < stepFloor
  total_eq :
    ∀ n,
      total n =
        physicalHauptvermutungTotalDistortion
          (countWindow n) (curvatureBias n) (spectralLocality n)
          (scale n) (edge n) (candidate n)
  step_floor : ∀ n, stepFloor ≤ step n
  aggregate_rate : ∀ n, rateBase * total n ≤ descentRate n

/-- A positive-gap natural quantization has a fixed lower bound whenever it
is nonzero. -/
theorem quantizedResidual_gap_of_nonzero
    {x gap : ℝ} {k : ℕ}
    (hgap : 0 < gap)
    (hx : x = gap * (k : ℝ))
    (hne : x ≠ 0) :
    gap ≤ x := by
  have hk_ne : k ≠ 0 := by
    intro hk
    apply hne
    rw [hx, hk]
    norm_num
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne
  have hk_one_nat : 1 ≤ k := Nat.succ_le_of_lt hk_pos
  have hk_one : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk_one_nat
  calc
    gap = gap * (1 : ℝ) := by ring
    _ ≤ gap * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hk_one (le_of_lt hgap)
    _ = x := by rw [hx]

theorem MicroscopicGate3DirectRateQuantizedData.count_nonneg
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {rateBase stepFloor countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3DirectRateQuantizedData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      rateBase stepFloor countGap curvatureGap spectralGap) :
    ∀ n i, 0 ≤ countWindow n i := by
  intro n i
  rw [D.count_eq n i]
  exact mul_nonneg (le_of_lt D.countGap_pos) (Nat.cast_nonneg _)

theorem MicroscopicGate3DirectRateQuantizedData.curvature_nonneg
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {rateBase stepFloor countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3DirectRateQuantizedData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      rateBase stepFloor countGap curvatureGap spectralGap) :
    ∀ n i, 0 ≤ curvatureBias n i := by
  intro n i
  rw [D.curvature_eq n i]
  exact mul_nonneg (le_of_lt D.curvatureGap_pos) (Nat.cast_nonneg _)

theorem MicroscopicGate3DirectRateQuantizedData.spectral_nonneg
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {rateBase stepFloor countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3DirectRateQuantizedData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      rateBase stepFloor countGap curvatureGap spectralGap) :
    ∀ n i, 0 ≤ spectralLocality n i := by
  intro n i
  rw [D.spectral_eq n i]
  exact mul_nonneg (le_of_lt D.spectralGap_pos) (Nat.cast_nonneg _)

/-- Quantization and the physical total-distortion identity make the tracked
total nonnegative. -/
theorem MicroscopicGate3DirectRateQuantizedData.total_nonneg
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {rateBase stepFloor countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3DirectRateQuantizedData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      rateBase stepFloor countGap curvatureGap spectralGap) :
    ∀ n, 0 ≤ total n := by
  exact
    physicalHauptvermutungTotalDistortion_sequence_nonneg
      D.count_nonneg D.curvature_nonneg D.spectral_nonneg
      D.total_eq

/-- The direct-rate target supplies horizon protection and convergence of the
tracked total distortion without any componentwise centered-source floor. -/
theorem MicroscopicGate3DirectRateQuantizedData.horizonProtection_and_total_tendsto_zero
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {rateBase stepFloor countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3DirectRateQuantizedData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      rateBase stepFloor countGap curvatureGap spectralGap) :
    (∀ n,
      linearResponse (w n) (source n) (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse (w n) (source n)
          (finiteAreaChange (c n) (J n)) = 0) ∧
      Tendsto total atTop (nhds 0) := by
  exact
    physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_positive_uniform_direct_rate_floor
      D.refinement rateBase stepFloor D.rateBase_pos D.stepFloor_pos
      D.total_nonneg D.aggregate_rate D.step_floor

/-- Every count residual is bounded above by the physical total distortion. -/
theorem countWindow_le_physicalHauptvermutungTotalDistortion
    {ι : Type*} [Fintype ι]
    (countWindow curvatureBias spectralLocality : ι → ℝ)
    (scale : ℝ) (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction)
    (hcount : ∀ i, 0 ≤ countWindow i)
    (hcurvature : ∀ i, 0 ≤ curvatureBias i)
    (hspectral : ∀ i, 0 ≤ spectralLocality i)
    (i : ι) :
    countWindow i ≤
      physicalHauptvermutungTotalDistortion
        countWindow curvatureBias spectralLocality scale edge candidate := by
  rw [physicalHauptvermutungTotalDistortion_eq_base_plus_bridge]
  have hterm :
      countWindow i ≤
        countWindow i + curvatureBias i + spectralLocality i := by
    linarith [hcurvature i, hspectral i]
  have hsingle :
      countWindow i + curvatureBias i + spectralLocality i ≤
        physicalHauptvermutungBaseDistortion
          countWindow curvatureBias spectralLocality := by
    unfold physicalHauptvermutungBaseDistortion
    exact
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j =>
          countWindow j + curvatureBias j + spectralLocality j)
        (fun j _ => by
          linarith [hcount j, hcurvature j, hspectral j])
        (Finset.mem_univ i)
  have hbridge :
      0 ≤ cSpecBridgeTotalDistortion scale edge candidate :=
    cSpecBridgeTotalDistortion_nonneg scale edge candidate
  linarith

/-- Every curvature residual is bounded above by the physical total
distortion. -/
theorem curvatureBias_le_physicalHauptvermutungTotalDistortion
    {ι : Type*} [Fintype ι]
    (countWindow curvatureBias spectralLocality : ι → ℝ)
    (scale : ℝ) (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction)
    (hcount : ∀ i, 0 ≤ countWindow i)
    (hcurvature : ∀ i, 0 ≤ curvatureBias i)
    (hspectral : ∀ i, 0 ≤ spectralLocality i)
    (i : ι) :
    curvatureBias i ≤
      physicalHauptvermutungTotalDistortion
        countWindow curvatureBias spectralLocality scale edge candidate := by
  rw [physicalHauptvermutungTotalDistortion_eq_base_plus_bridge]
  have hterm :
      curvatureBias i ≤
        countWindow i + curvatureBias i + spectralLocality i := by
    linarith [hcount i, hspectral i]
  have hsingle :
      countWindow i + curvatureBias i + spectralLocality i ≤
        physicalHauptvermutungBaseDistortion
          countWindow curvatureBias spectralLocality := by
    unfold physicalHauptvermutungBaseDistortion
    exact
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j =>
          countWindow j + curvatureBias j + spectralLocality j)
        (fun j _ => by
          linarith [hcount j, hcurvature j, hspectral j])
        (Finset.mem_univ i)
  have hbridge :
      0 ≤ cSpecBridgeTotalDistortion scale edge candidate :=
    cSpecBridgeTotalDistortion_nonneg scale edge candidate
  linarith

/-- Every spectral/locality residual is bounded above by the physical total
distortion. -/
theorem spectralLocality_le_physicalHauptvermutungTotalDistortion
    {ι : Type*} [Fintype ι]
    (countWindow curvatureBias spectralLocality : ι → ℝ)
    (scale : ℝ) (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction)
    (hcount : ∀ i, 0 ≤ countWindow i)
    (hcurvature : ∀ i, 0 ≤ curvatureBias i)
    (hspectral : ∀ i, 0 ≤ spectralLocality i)
    (i : ι) :
    spectralLocality i ≤
      physicalHauptvermutungTotalDistortion
        countWindow curvatureBias spectralLocality scale edge candidate := by
  rw [physicalHauptvermutungTotalDistortion_eq_base_plus_bridge]
  have hterm :
      spectralLocality i ≤
        countWindow i + curvatureBias i + spectralLocality i := by
    linarith [hcount i, hcurvature i]
  have hsingle :
      countWindow i + curvatureBias i + spectralLocality i ≤
        physicalHauptvermutungBaseDistortion
          countWindow curvatureBias spectralLocality := by
    unfold physicalHauptvermutungBaseDistortion
    exact
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j =>
          countWindow j + curvatureBias j + spectralLocality j)
        (fun j _ => by
          linarith [hcount j, hcurvature j, hspectral j])
        (Finset.mem_univ i)
  have hbridge :
      0 ≤ cSpecBridgeTotalDistortion scale edge candidate :=
    cSpecBridgeTotalDistortion_nonneg scale edge candidate
  linarith

/-- Aggregate-rate contraction plus finite-spectrum quantization gives exact
residual zero and canonical bridge recovery after a finite threshold. -/
theorem MicroscopicGate3DirectRateQuantizedData.eventually_exact_zero
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {rateBase stepFloor countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3DirectRateQuantizedData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      rateBase stepFloor countGap curvatureGap spectralGap) :
    ∀ᶠ n in atTop,
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  have htotal_tendsto : Tendsto total atTop (nhds 0) :=
    D.horizonProtection_and_total_tendsto_zero.2
  have hcount_lt : ∀ᶠ n in atTop, total n < countGap := by
    exact htotal_tendsto (Iio_mem_nhds D.countGap_pos)
  have hcurvature_lt : ∀ᶠ n in atTop, total n < curvatureGap := by
    exact htotal_tendsto (Iio_mem_nhds D.curvatureGap_pos)
  have hspectral_lt : ∀ᶠ n in atTop, total n < spectralGap := by
    exact htotal_tendsto (Iio_mem_nhds D.spectralGap_pos)
  have hbridge_lt : ∀ᶠ n in atTop, total n < 18 := by
    exact htotal_tendsto (Iio_mem_nhds (by norm_num))
  have hcount_zero : ∀ᶠ n in atTop, ∀ i, countWindow n i = 0 := by
    filter_upwards [hcount_lt] with n hn
    intro i
    by_contra hne
    have hgap : countGap ≤ countWindow n i :=
      quantizedResidual_gap_of_nonzero D.countGap_pos (D.count_eq n i) hne
    have hle : countWindow n i ≤ total n := by
      rw [D.total_eq n]
      exact
        countWindow_le_physicalHauptvermutungTotalDistortion
          (countWindow n) (curvatureBias n) (spectralLocality n)
          (scale n) (edge n) (candidate n)
          (D.count_nonneg n) (D.curvature_nonneg n)
          (D.spectral_nonneg n) i
    exact (not_le_of_gt hn) (le_trans hgap hle)
  have hcurvature_zero :
      ∀ᶠ n in atTop, ∀ i, curvatureBias n i = 0 := by
    filter_upwards [hcurvature_lt] with n hn
    intro i
    by_contra hne
    have hgap : curvatureGap ≤ curvatureBias n i :=
      quantizedResidual_gap_of_nonzero
        D.curvatureGap_pos (D.curvature_eq n i) hne
    have hle : curvatureBias n i ≤ total n := by
      rw [D.total_eq n]
      exact
        curvatureBias_le_physicalHauptvermutungTotalDistortion
          (countWindow n) (curvatureBias n) (spectralLocality n)
          (scale n) (edge n) (candidate n)
          (D.count_nonneg n) (D.curvature_nonneg n)
          (D.spectral_nonneg n) i
    exact (not_le_of_gt hn) (le_trans hgap hle)
  have hspectral_zero :
      ∀ᶠ n in atTop, ∀ i, spectralLocality n i = 0 := by
    filter_upwards [hspectral_lt] with n hn
    intro i
    by_contra hne
    have hgap : spectralGap ≤ spectralLocality n i :=
      quantizedResidual_gap_of_nonzero
        D.spectralGap_pos (D.spectral_eq n i) hne
    have hle : spectralLocality n i ≤ total n := by
      rw [D.total_eq n]
      exact
        spectralLocality_le_physicalHauptvermutungTotalDistortion
          (countWindow n) (curvatureBias n) (spectralLocality n)
          (scale n) (edge n) (candidate n)
          (D.count_nonneg n) (D.curvature_nonneg n)
          (D.spectral_nonneg n) i
    exact (not_le_of_gt hn) (le_trans hgap hle)
  have hcanonical :
      ∀ᶠ n in atTop,
        candidate n = canonicalCSpecBridgeCandidate (edge n) := by
    filter_upwards [hbridge_lt] with n hn
    by_contra hne
    have hgap : 18 ≤ total n := by
      rw [D.total_eq n]
      exact
        physicalHauptvermutungTotalDistortion_gap_of_bridge_defect_floor
          (countWindow n) (curvatureBias n) (spectralLocality n)
          (scale n) (edge n) (candidate n) 18
          (D.count_nonneg n) (D.curvature_nonneg n)
          (D.spectral_nonneg n)
          (fun i hi => bridgeCensusDefect_wrong_floor (edge n i) (candidate n i) hi)
          hne
    exact (not_le_of_gt hn) hgap
  filter_upwards [hcount_zero, hcurvature_zero, hspectral_zero, hcanonical]
    with n hcount hcurvature hspectral hcandidate
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

/-- The corrected direct-rate target reaches the same operational recovered
stage needed by the Gate 4 interfaces. -/
theorem MicroscopicGate3DirectRateQuantizedData.eventually_recoveredStage
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {rateBase stepFloor countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3DirectRateQuantizedData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      rateBase stepFloor countGap curvatureGap spectralGap) :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  filter_upwards [D.eventually_exact_zero]
    with n hrecover
  rcases hrecover with
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

/-- Eventual direct-rate recovery has an explicit finite threshold. -/
theorem MicroscopicGate3DirectRateQuantizedData.exists_recovered_after
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {rateBase stepFloor countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3DirectRateQuantizedData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      rateBase stepFloor countGap curvatureGap spectralGap) :
    ∃ N, ∀ n, N ≤ n →
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  have hrecovered := D.eventually_recoveredStage
  rw [eventually_atTop] at hrecovered
  exact hrecovered

#print axioms MicroscopicGate3DirectRateQuantizedData.total_nonneg
#print axioms MicroscopicGate3DirectRateQuantizedData.horizonProtection_and_total_tendsto_zero
#print axioms MicroscopicGate3DirectRateQuantizedData.eventually_exact_zero
#print axioms MicroscopicGate3DirectRateQuantizedData.eventually_recoveredStage
#print axioms MicroscopicGate3DirectRateQuantizedData.exists_recovered_after

end UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3DirectRate
