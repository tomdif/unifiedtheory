/-
  Audit/KFCausalCSpecMicroscopicGate3StoppableDirectRate.lean

  A consistent normalized-weight-compatible Gate 3 supplier.

  The legacy direct-rate record embedded `PhysicalGrowthRepairRefinement`,
  whose unconditional `descent_pos` field continues demanding strict descent
  after a nonnegative quantized distortion reaches zero.  Here the refinement
  retains the actual per-step repair certificate and nonnegative step size,
  but permits the aggregate descent rate to stop at zero.  A positive uniform
  aggregate rate is imposed only relative to the current total distortion.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3StoppableDirectRate

open Filter Topology
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecBridgePoset
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization

/-- A positive-gap natural quantization has a fixed lower bound whenever its
residual is nonzero. -/
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
  have hk_one_nat : 1 ≤ k := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hk_ne)
  have hk_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_one_nat
  calc
    gap = gap * (1 : ℝ) := by ring
    _ ≤ gap * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hk_one (le_of_lt hgap)
    _ = x := by rw [hx]

/-- Any component bounded by its local nonnegative residual sum is bounded by
the full physical Hauptvermutung distortion. -/
theorem residualComponent_le_physicalHauptvermutungTotalDistortion
    {ι : Type*} [Fintype ι]
    (component countWindow curvatureBias spectralLocality : ι → ℝ)
    (scale : ℝ) (edge : ι → E4)
    (candidate : ι → Equiv.Perm Direction)
    (hcount : ∀ i, 0 ≤ countWindow i)
    (hcurvature : ∀ i, 0 ≤ curvatureBias i)
    (hspectral : ∀ i, 0 ≤ spectralLocality i)
    (hcomponent : ∀ i,
      component i ≤ countWindow i + curvatureBias i + spectralLocality i)
    (i : ι) :
    component i ≤
      physicalHauptvermutungTotalDistortion
        countWindow curvatureBias spectralLocality scale edge candidate := by
  rw [physicalHauptvermutungTotalDistortion_eq_base_plus_bridge]
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
  have hbridge : 0 ≤ cSpecBridgeTotalDistortion scale edge candidate :=
    cSpecBridgeTotalDistortion_nonneg scale edge candidate
  linarith [hcomponent i]

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
  exact
    residualComponent_le_physicalHauptvermutungTotalDistortion
      countWindow countWindow curvatureBias spectralLocality
      scale edge candidate hcount hcurvature hspectral
      (fun j => by linarith [hcurvature j, hspectral j]) i

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
  exact
    residualComponent_le_physicalHauptvermutungTotalDistortion
      curvatureBias countWindow curvatureBias spectralLocality
      scale edge candidate hcount hcurvature hspectral
      (fun j => by linarith [hcount j, hspectral j]) i

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
  exact
    residualComponent_le_physicalHauptvermutungTotalDistortion
      spectralLocality countWindow curvatureBias spectralLocality
      scale edge candidate hcount hcurvature hspectral
      (fun j => by linarith [hcount j, hcurvature j]) i

/-- A repair refinement which may stop.  The per-step certificate still
contains both horizon identities, aggregate descent, the update estimate, and
the remainder estimate.  Unlike `PhysicalGrowthRepairRefinement`, this record
does not assert that the descent rate is strictly positive at every stage. -/
structure StoppablePhysicalGrowthRepairRefinement
    {ι : Type*} [Fintype ι]
    (w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (scale c step descentRate remainder total : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction) : Prop where
  certified_step :
    ∀ n,
      PhysicalGrowthSuppliesRepairSource (w n) (J n) (source n)
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (c n) (step n) (descentRate n) (remainder n)
        (total n) (total (n + 1)) (edge n) (candidate n)
  step_nonneg : ∀ n, 0 ≤ step n

/-- The certified stoppable update satisfies the same weak contraction
recurrence as the legacy strict refinement. -/
theorem StoppablePhysicalGrowthRepairRefinement.step_contracts
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    (R : StoppablePhysicalGrowthRepairRefinement w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate)
    (n : ℕ) :
    total (n + 1) ≤ total n - step n * descentRate n / 2 := by
  exact
    physicalGrowthSuppliesRepairSource_contracts
      (R.certified_step n) (R.step_nonneg n)

/-- Each stoppable repair step preserves both horizon-area responses. -/
theorem StoppablePhysicalGrowthRepairRefinement.step_protected
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    (R : StoppablePhysicalGrowthRepairRefinement w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate)
    (n : ℕ) :
    linearResponse (w n) (source n) (finiteAreaChange (c n) (J n)) = 0 ∧
      quadraticResponse (w n) (source n)
        (finiteAreaChange (c n) (J n)) = 0 := by
  exact
    ⟨(R.certified_step n).first_horizon_area_zero,
      (R.certified_step n).second_horizon_area_zero⟩

/-- A uniform aggregate-rate floor gives a one-step multiplicative bound for
the stoppable refinement. -/
theorem StoppablePhysicalGrowthRepairRefinement.step_factor_of_uniform_rate_floor
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    (R : StoppablePhysicalGrowthRepairRefinement w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate)
    (q gamma stepFloor : ℝ)
    (htotal_nonneg : ∀ n, 0 ≤ total n)
    (hgamma_nonneg : 0 ≤ gamma)
    (hrate : ∀ n, gamma * total n ≤ descentRate n)
    (hstep_floor : ∀ n, stepFloor ≤ step n)
    (hfloor_budget : 2 * (1 - q) ≤ stepFloor * gamma) :
    ∀ n, total (n + 1) ≤ q * total n := by
  intro n
  exact
    physicalGrowthSuppliesRepairSource_step_factor_of_rate_floor
      (R.certified_step n) (R.step_nonneg n) (htotal_nonneg n) (hrate n)
      (le_trans hfloor_budget
        (mul_le_mul_of_nonneg_right (hstep_floor n) hgamma_nonneg))

/-- A nonnegative fixed step factor has its usual geometric majorant. -/
theorem stoppable_geometric_bound_of_step_factor
    {total : ℕ → ℝ} (q : ℝ) (hq0 : 0 ≤ q)
    (hstep_factor : ∀ n, total (n + 1) ≤ q * total n) :
    ∀ n, total n ≤ total 0 * q ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      change total (n + 1) ≤ total 0 * q ^ (n + 1)
      have hmul : q * total n ≤ q * (total 0 * q ^ n) :=
        mul_le_mul_of_nonneg_left ih hq0
      calc
        total (n + 1) ≤ q * total n := hstep_factor n
        _ ≤ q * (total 0 * q ^ n) := hmul
        _ = total 0 * q ^ (n + 1) := by
          rw [pow_succ]
          ring

/-- A nonnegative sequence under a geometric majorant with factor below one
converges to zero. -/
theorem stoppable_total_tendsto_zero_of_step_factor
    {total : ℕ → ℝ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (htotal_nonneg : ∀ n, 0 ≤ total n)
    (hstep_factor : ∀ n, total (n + 1) ≤ q * total n) :
    Tendsto total atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hmajor :
      Tendsto (fun n : ℕ => total 0 * q ^ n) atTop (nhds 0) := by
    simpa using hpow.const_mul (total 0)
  exact
    squeeze_zero htotal_nonneg
      (stoppable_geometric_bound_of_step_factor q hq0 hstep_factor)
      hmajor

/-- Quantized Gate 3 data using a stoppable repair refinement and the direct
aggregate rate actually needed by the convergence proof. -/
structure MicroscopicGate3StoppableDirectRateQuantizedData
    {ι : Type*} [Fintype ι]
    (w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (scale c step descentRate remainder total : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction)
    (countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ)
    (rateBase stepFloor countGap curvatureGap spectralGap : ℝ) : Prop where
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

namespace MicroscopicGate3StoppableDirectRateQuantizedData

variable {ι : Type*} [Fintype ι]
variable {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
variable {scale c step descentRate remainder total : ℕ → ℝ}
variable {edge : ℕ → ι → E4}
variable {candidate : ℕ → ι → Equiv.Perm Direction}
variable {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
variable {rateBase stepFloor countGap curvatureGap spectralGap : ℝ}

variable
  (D : MicroscopicGate3StoppableDirectRateQuantizedData w J source
    countWindow curvatureBias spectralLocality
    scale c step descentRate remainder total edge candidate
    countQuantum curvatureQuantum spectralQuantum
    rateBase stepFloor countGap curvatureGap spectralGap)

include D

theorem count_nonneg : ∀ n i, 0 ≤ countWindow n i := by
  intro n i
  rw [D.count_eq n i]
  exact mul_nonneg (le_of_lt D.countGap_pos) (Nat.cast_nonneg _)

theorem curvature_nonneg : ∀ n i, 0 ≤ curvatureBias n i := by
  intro n i
  rw [D.curvature_eq n i]
  exact mul_nonneg (le_of_lt D.curvatureGap_pos) (Nat.cast_nonneg _)

theorem spectral_nonneg : ∀ n i, 0 ≤ spectralLocality n i := by
  intro n i
  rw [D.spectral_eq n i]
  exact mul_nonneg (le_of_lt D.spectralGap_pos) (Nat.cast_nonneg _)

/-- Quantization and the physical-total identity make every tracked total
nonnegative. -/
theorem total_nonneg : ∀ n, 0 ≤ total n := by
  exact
    physicalHauptvermutungTotalDistortion_sequence_nonneg
      D.count_nonneg D.curvature_nonneg D.spectral_nonneg D.total_eq

/-- The clipped positive direct rate supplies a fixed contraction factor, so
the stoppable recurrence converges without assuming the desired convergence. -/
theorem horizonProtection_and_total_tendsto_zero :
    (∀ n,
      linearResponse (w n) (source n) (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse (w n) (source n)
          (finiteAreaChange (c n) (J n)) = 0) ∧
      Tendsto total atTop (nhds 0) := by
  let gamma : ℝ := min rateBase (1 / stepFloor)
  let q : ℝ := 1 - stepFloor * gamma / 2
  have hstep_inv_pos : 0 < 1 / stepFloor := one_div_pos.mpr D.stepFloor_pos
  have hgamma_pos : 0 < gamma := by
    dsimp [gamma]
    exact lt_min D.rateBase_pos hstep_inv_pos
  have hgamma_nonneg : 0 ≤ gamma := le_of_lt hgamma_pos
  have hgamma_rate : gamma ≤ rateBase := by
    dsimp [gamma]
    exact min_le_left _ _
  have hgamma_step : gamma ≤ 1 / stepFloor := by
    dsimp [gamma]
    exact min_le_right _ _
  have hprod_pos : 0 < stepFloor * gamma :=
    mul_pos D.stepFloor_pos hgamma_pos
  have hprod_le_one : stepFloor * gamma ≤ 1 := by
    calc
      stepFloor * gamma ≤ stepFloor * (1 / stepFloor) :=
        mul_le_mul_of_nonneg_left hgamma_step (le_of_lt D.stepFloor_pos)
      _ = 1 := by field_simp [ne_of_gt D.stepFloor_pos]
  have hq0 : 0 ≤ q := by
    dsimp [q]
    nlinarith
  have hq1 : q < 1 := by
    dsimp [q]
    nlinarith
  have hrate_clipped : ∀ n, gamma * total n ≤ descentRate n := by
    intro n
    have hclip : gamma * total n ≤ rateBase * total n :=
      mul_le_mul_of_nonneg_right hgamma_rate (D.total_nonneg n)
    exact le_trans hclip (D.aggregate_rate n)
  have hfloor_budget : 2 * (1 - q) ≤ stepFloor * gamma := by
    dsimp [q]
    nlinarith
  have hfactor : ∀ n, total (n + 1) ≤ q * total n :=
    D.refinement.step_factor_of_uniform_rate_floor
      q gamma stepFloor D.total_nonneg hgamma_nonneg hrate_clipped
      D.step_floor hfloor_budget
  exact
    ⟨fun n => D.refinement.step_protected n,
      stoppable_total_tendsto_zero_of_step_factor
        q hq0 hq1 D.total_nonneg hfactor⟩

/-- At zero total distortion the aggregate descent rate is forced to stop.
This is derived from next-total nonnegativity, certified contraction, the
positive step floor, and the aggregate-rate inequality. -/
theorem descentRate_eq_zero_of_total_eq_zero
    {n : ℕ} (hzero : total n = 0) : descentRate n = 0 := by
  have hdescent_nonneg : 0 ≤ descentRate n := by
    have hrate := D.aggregate_rate n
    rw [hzero] at hrate
    simpa using hrate
  have hstep_pos : 0 < step n :=
    lt_of_lt_of_le D.stepFloor_pos (D.step_floor n)
  have hcontract := D.refinement.step_contracts n
  have hnext_nonneg := D.total_nonneg (n + 1)
  rw [hzero] at hcontract
  nlinarith

/-- Zero total distortion is absorbing for the tracked total. -/
theorem total_next_eq_zero_of_total_eq_zero
    {n : ℕ} (hzero : total n = 0) : total (n + 1) = 0 := by
  have hdescent := D.descentRate_eq_zero_of_total_eq_zero hzero
  have hcontract := D.refinement.step_contracts n
  have hnext_nonneg := D.total_nonneg (n + 1)
  rw [hzero, hdescent] at hcontract
  have hnext_le : total (n + 1) ≤ 0 := by nlinarith
  exact le_antisymm hnext_le hnext_nonneg

/-- Quantized residual gaps and the finite bridge-defect gap turn asymptotic
convergence into exact recovery after a finite stage. -/
theorem eventually_exact_zero :
    ∀ᶠ n in atTop,
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  have htotal_tendsto : Tendsto total atTop (nhds 0) :=
    D.horizonProtection_and_total_tendsto_zero.2
  have hcount_lt : ∀ᶠ n in atTop, total n < countGap :=
    htotal_tendsto (Iio_mem_nhds D.countGap_pos)
  have hcurvature_lt : ∀ᶠ n in atTop, total n < curvatureGap :=
    htotal_tendsto (Iio_mem_nhds D.curvatureGap_pos)
  have hspectral_lt : ∀ᶠ n in atTop, total n < spectralGap :=
    htotal_tendsto (Iio_mem_nhds D.spectralGap_pos)
  have hbridge_lt : ∀ᶠ n in atTop, total n < 18 :=
    htotal_tendsto (Iio_mem_nhds (by norm_num))
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
          (fun i hi =>
            bridgeCensusDefect_wrong_floor (edge n i) (candidate n i) hi)
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

/-- The corrected stoppable supplier reaches the operational recovered-stage
predicate consumed by Gate 4. -/
theorem eventually_recoveredStage :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  filter_upwards [D.eventually_exact_zero] with n hrecover
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

/-- Eventual stoppable recovery has an explicit finite threshold. -/
theorem exists_recovered_after :
    ∃ N, ∀ n, N ≤ n →
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  have hrecovered := D.eventually_recoveredStage
  rw [eventually_atTop] at hrecovered
  exact hrecovered

#print axioms StoppablePhysicalGrowthRepairRefinement.step_contracts
#print axioms horizonProtection_and_total_tendsto_zero
#print axioms descentRate_eq_zero_of_total_eq_zero
#print axioms total_next_eq_zero_of_total_eq_zero
#print axioms eventually_exact_zero
#print axioms eventually_recoveredStage
#print axioms exists_recovered_after

end MicroscopicGate3StoppableDirectRateQuantizedData

end UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3StoppableDirectRate
