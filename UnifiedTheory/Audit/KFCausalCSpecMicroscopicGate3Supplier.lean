/-
  Audit/KFCausalCSpecMicroscopicGate3Supplier.lean

  Microscopic supplier interface for Gate 3 rates and residual gaps.

  The lower Gate 3 library already proves that a physical repair refinement
  with a positive aggregate descent rate contracts the Hauptvermutung
  distortion, and that a convergence certificate plus positive residual gaps
  upgrades convergence to eventual exact recovery.  This file records the
  smallest Lean-facing package that microscopic dynamics must now supply.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFTOESevenGateAttack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3Supplier

open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFTOESevenGateAttack
open Filter Topology
open scoped BigOperators

/-- The direct microscopic Gate 3 rate/gap package.

The intended microscopic content is:

* `refinement`: each finite birth/repair step is certified by the actual
  physical growth source;
* `aggregate_rate`: the microscopic source has a uniform negative Lyapunov
  drift against the physical Hauptvermutung distortion;
* `count_gap`, `curvature_gap`, and `spectral_gap`: the non-bridge residuals
  are finite-spectrum observables, so nonzero residual means uniformly
  positive residual.

This is deliberately weaker than a full exact-recovery certificate: it closes
the aggregate-rate Gate 3 subcertificate directly, and it supplies the residual
gaps needed by any separately constructed convergence certificate. -/
structure MicroscopicGate3RatesGaps
    {ι : Type*} [Fintype ι]
    (w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (scale c step descentRate remainder total : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction)
    (rateBase stepFloor residualGap : ℝ) : Prop where
  refinement :
    PhysicalGrowthRepairRefinement w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
  rateBase_pos : 0 < rateBase
  stepFloor_pos : 0 < stepFloor
  total_nonneg : ∀ n, 0 ≤ total n
  aggregate_rate : ∀ n, rateBase * total n ≤ descentRate n
  step_floor : ∀ n, stepFloor ≤ step n
  residualGap_pos : 0 < residualGap
  count_gap :
    ∀ n i, countWindow n i ≠ 0 → residualGap ≤ countWindow n i
  curvature_gap :
    ∀ n i, curvatureBias n i ≠ 0 → residualGap ≤ curvatureBias n i
  spectral_gap :
    ∀ n i, spectralLocality n i ≠ 0 → residualGap ≤ spectralLocality n i

/-- Microscopic rate data closes the direct aggregate-rate Gate 3
subcertificate. -/
theorem microscopicGate3RatesGaps_aggregateRateContraction_closed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {rateBase stepFloor residualGap : ℝ}
    (S : MicroscopicGate3RatesGaps w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      rateBase stepFloor residualGap) :
    Gate3AggregateRateContractionClosed
      S.refinement rateBase stepFloor := by
  exact
    gate3_aggregateRateContraction_closed
      S.refinement S.rateBase_pos S.stepFloor_pos
      S.total_nonneg S.aggregate_rate S.step_floor

/-- Microscopic residual-gap data upgrades any supplied Gate 3 convergence
certificate to the residual exact-zero subcertificate. -/
theorem microscopicGate3RatesGaps_residualGapExactZero_closed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {rateBase stepFloor weightBase sourceBase residualGap : ℝ}
    (S : MicroscopicGate3RatesGaps w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      rateBase stepFloor residualGap)
    (C : PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase) :
    Gate3ResidualGapExactZeroClosed C residualGap := by
  exact
    gate3_residualGapExactZero_closed
      C S.residualGap_pos S.count_gap S.curvature_gap S.spectral_gap

/-- The common residual gap obtained from separately certified finite-spectrum
floors for the count, curvature, and spectral/locality residuals. -/
def commonResidualGap
    (countGap curvatureGap spectralGap : ℝ) : ℝ :=
  min countGap (min curvatureGap spectralGap)

/-- Separate finite-spectrum residual floors for the three non-bridge
Hauptvermutung residual families. -/
structure MicroscopicGate3ComponentResidualGaps
    {ι : Type*}
    (countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (countGap curvatureGap spectralGap : ℝ) : Prop where
  countGap_pos : 0 < countGap
  curvatureGap_pos : 0 < curvatureGap
  spectralGap_pos : 0 < spectralGap
  count_gap :
    ∀ n i, countWindow n i ≠ 0 → countGap ≤ countWindow n i
  curvature_gap :
    ∀ n i, curvatureBias n i ≠ 0 → curvatureGap ≤ curvatureBias n i
  spectral_gap :
    ∀ n i, spectralLocality n i ≠ 0 → spectralGap ≤ spectralLocality n i

/-- Generic quantized-residual floor: if a real residual is a positive gap
times a natural occupation number, then every nonzero value is at least that
gap. -/
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

/-- If a positive-gap quantized real residual is zero, then its natural
occupation number is zero. -/
theorem quantizedResidual_quantum_eq_zero_of_value_zero
    {x gap : ℝ} {k : ℕ}
    (hgap : 0 < gap)
    (hx : x = gap * (k : ℝ))
    (hzero : x = 0) :
    k = 0 := by
  by_contra hk
  have hk_pos_nat : 0 < k := Nat.pos_of_ne_zero hk
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast hk_pos_nat
  have hprod_pos : 0 < gap * (k : ℝ) := mul_pos hgap hk_pos
  have hprod_zero : gap * (k : ℝ) = 0 := by
    rw [← hx, hzero]
  exact (ne_of_gt hprod_pos) hprod_zero

/-- Positive-gap quantization turns real zero into exactly natural occupation
zero. -/
theorem quantizedResidual_value_zero_iff_quantum_eq_zero
    {x gap : ℝ} {k : ℕ}
    (hgap : 0 < gap)
    (hx : x = gap * (k : ℝ)) :
    x = 0 ↔ k = 0 := by
  constructor
  · intro hzero
    exact quantizedResidual_quantum_eq_zero_of_value_zero hgap hx hzero
  · intro hk
    rw [hx, hk]
    norm_num

/-- A concrete finite-spectrum supplier for the residual gaps: each residual is
a positive real gap times a natural occupation number.  This matches the
intended order-count/polynomial-dictionary route for microscopic observables. -/
structure QuantizedGate3Residuals
    {ι : Type*}
    (countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ)
    (countGap curvatureGap spectralGap : ℝ) : Prop where
  countGap_pos : 0 < countGap
  curvatureGap_pos : 0 < curvatureGap
  spectralGap_pos : 0 < spectralGap
  count_eq :
    ∀ n i, countWindow n i = countGap * (countQuantum n i : ℝ)
  curvature_eq :
    ∀ n i, curvatureBias n i = curvatureGap * (curvatureQuantum n i : ℝ)
  spectral_eq :
    ∀ n i, spectralLocality n i = spectralGap * (spectralQuantum n i : ℝ)

/-- Quantized residuals supply the component finite-spectrum gaps needed by
Gate 3 exact-zero recovery. -/
theorem quantizedGate3Residuals_componentResidualGaps
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {countGap curvatureGap spectralGap : ℝ}
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap) :
    MicroscopicGate3ComponentResidualGaps
      countWindow curvatureBias spectralLocality
      countGap curvatureGap spectralGap where
  countGap_pos := Q.countGap_pos
  curvatureGap_pos := Q.curvatureGap_pos
  spectralGap_pos := Q.spectralGap_pos
  count_gap := fun n i hne =>
    quantizedResidual_gap_of_nonzero Q.countGap_pos (Q.count_eq n i) hne
  curvature_gap := fun n i hne =>
    quantizedResidual_gap_of_nonzero
      Q.curvatureGap_pos (Q.curvature_eq n i) hne
  spectral_gap := fun n i hne =>
    quantizedResidual_gap_of_nonzero
      Q.spectralGap_pos (Q.spectral_eq n i) hne

/-- Zero count residuals force zero count occupations. -/
theorem quantizedGate3Residuals_countQuantum_eq_zero_of_count_zero
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {countGap curvatureGap spectralGap : ℝ}
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap) :
    ∀ n i, countWindow n i = 0 → countQuantum n i = 0 := by
  intro n i hzero
  exact
    quantizedResidual_quantum_eq_zero_of_value_zero
      Q.countGap_pos (Q.count_eq n i) hzero

/-- Zero curvature residuals force zero curvature occupations. -/
theorem quantizedGate3Residuals_curvatureQuantum_eq_zero_of_curvature_zero
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {countGap curvatureGap spectralGap : ℝ}
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap) :
    ∀ n i, curvatureBias n i = 0 → curvatureQuantum n i = 0 := by
  intro n i hzero
  exact
    quantizedResidual_quantum_eq_zero_of_value_zero
      Q.curvatureGap_pos (Q.curvature_eq n i) hzero

/-- Zero spectral/locality residuals force zero spectral occupations. -/
theorem quantizedGate3Residuals_spectralQuantum_eq_zero_of_spectral_zero
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {countGap curvatureGap spectralGap : ℝ}
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap) :
    ∀ n i, spectralLocality n i = 0 → spectralQuantum n i = 0 := by
  intro n i hzero
  exact
    quantizedResidual_quantum_eq_zero_of_value_zero
      Q.spectralGap_pos (Q.spectral_eq n i) hzero

/-- Quantized count residuals are automatically nonnegative. -/
theorem quantizedGate3Residuals_count_nonneg
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {countGap curvatureGap spectralGap : ℝ}
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap) :
    ∀ n i, 0 ≤ countWindow n i := by
  intro n i
  rw [Q.count_eq n i]
  exact mul_nonneg (le_of_lt Q.countGap_pos) (Nat.cast_nonneg _)

/-- Quantized curvature residuals are automatically nonnegative. -/
theorem quantizedGate3Residuals_curvature_nonneg
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {countGap curvatureGap spectralGap : ℝ}
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap) :
    ∀ n i, 0 ≤ curvatureBias n i := by
  intro n i
  rw [Q.curvature_eq n i]
  exact mul_nonneg (le_of_lt Q.curvatureGap_pos) (Nat.cast_nonneg _)

/-- Quantized spectral/locality residuals are automatically nonnegative. -/
theorem quantizedGate3Residuals_spectral_nonneg
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {countGap curvatureGap spectralGap : ℝ}
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap) :
    ∀ n i, 0 ≤ spectralLocality n i := by
  intro n i
  rw [Q.spectral_eq n i]
  exact mul_nonneg (le_of_lt Q.spectralGap_pos) (Nat.cast_nonneg _)

/-- Count residual zero is equivalent to zero count occupation. -/
theorem quantizedGate3Residuals_count_zero_iff_quantum_zero
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {countGap curvatureGap spectralGap : ℝ}
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap)
    (n : ℕ) (i : ι) :
    countWindow n i = 0 ↔ countQuantum n i = 0 := by
  exact
    quantizedResidual_value_zero_iff_quantum_eq_zero
      Q.countGap_pos (Q.count_eq n i)

/-- Curvature residual zero is equivalent to zero curvature occupation. -/
theorem quantizedGate3Residuals_curvature_zero_iff_quantum_zero
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {countGap curvatureGap spectralGap : ℝ}
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap)
    (n : ℕ) (i : ι) :
    curvatureBias n i = 0 ↔ curvatureQuantum n i = 0 := by
  exact
    quantizedResidual_value_zero_iff_quantum_eq_zero
      Q.curvatureGap_pos (Q.curvature_eq n i)

/-- Spectral/locality residual zero is equivalent to zero spectral
occupation. -/
theorem quantizedGate3Residuals_spectral_zero_iff_quantum_zero
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {countGap curvatureGap spectralGap : ℝ}
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap)
    (n : ℕ) (i : ι) :
    spectralLocality n i = 0 ↔ spectralQuantum n i = 0 := by
  exact
    quantizedResidual_value_zero_iff_quantum_eq_zero
      Q.spectralGap_pos (Q.spectral_eq n i)

/-- The three real residual families vanish exactly when the three natural
occupation families vanish. -/
theorem quantizedGate3Residuals_residuals_zero_iff_quantum_zero
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {countGap curvatureGap spectralGap : ℝ}
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap)
    (n : ℕ) :
    ((∀ i, countWindow n i = 0) ∧
        (∀ i, curvatureBias n i = 0) ∧
          (∀ i, spectralLocality n i = 0)) ↔
      (∀ i, countQuantum n i = 0) ∧
        (∀ i, curvatureQuantum n i = 0) ∧
          (∀ i, spectralQuantum n i = 0) := by
  constructor
  · rintro ⟨hcount, hcurvature, hspectral⟩
    exact
      ⟨fun i =>
          (quantizedGate3Residuals_count_zero_iff_quantum_zero
            Q n i).1 (hcount i),
        fun i =>
          (quantizedGate3Residuals_curvature_zero_iff_quantum_zero
            Q n i).1 (hcurvature i),
        fun i =>
          (quantizedGate3Residuals_spectral_zero_iff_quantum_zero
            Q n i).1 (hspectral i)⟩
  · rintro ⟨hcount, hcurvature, hspectral⟩
    exact
      ⟨fun i =>
          (quantizedGate3Residuals_count_zero_iff_quantum_zero
            Q n i).2 (hcount i),
        fun i =>
          (quantizedGate3Residuals_curvature_zero_iff_quantum_zero
            Q n i).2 (hcurvature i),
        fun i =>
          (quantizedGate3Residuals_spectral_zero_iff_quantum_zero
            Q n i).2 (hspectral i)⟩

/-- In the quantized setting, base Hauptvermutung distortion is zero exactly
when all three natural residual occupation families vanish. -/
theorem quantizedGate3Residuals_baseDistortion_eq_zero_iff_quantum_zero
    {ι : Type*} [Fintype ι]
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {countGap curvatureGap spectralGap : ℝ}
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap)
    (n : ℕ) :
    physicalHauptvermutungBaseDistortion
        (countWindow n) (curvatureBias n) (spectralLocality n) = 0 ↔
      (∀ i, countQuantum n i = 0) ∧
        (∀ i, curvatureQuantum n i = 0) ∧
          (∀ i, spectralQuantum n i = 0) := by
  have hbase :=
    physicalHauptvermutungBaseDistortion_eq_zero_iff
      (countWindow n) (curvatureBias n) (spectralLocality n)
      (quantizedGate3Residuals_count_nonneg Q n)
      (quantizedGate3Residuals_curvature_nonneg Q n)
      (quantizedGate3Residuals_spectral_nonneg Q n)
  constructor
  · intro hzero
    exact
      (quantizedGate3Residuals_residuals_zero_iff_quantum_zero Q n).1
        (hbase.1 hzero)
  · intro hquantum
    exact
      hbase.2
        ((quantizedGate3Residuals_residuals_zero_iff_quantum_zero Q n).2
          hquantum)

/-- In the quantized setting, total Hauptvermutung distortion is zero exactly
when the natural residual occupations vanish and bridge transport is
canonical. -/
theorem quantizedGate3Residuals_totalDistortion_eq_zero_iff_quantum_zero_and_canonical
    {ι : Type*} [Fintype ι]
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {countGap curvatureGap spectralGap : ℝ}
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap)
    (scale : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction)
    (n : ℕ) :
    physicalHauptvermutungTotalDistortion
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (edge n) (candidate n) = 0 ↔
      (∀ i, countQuantum n i = 0) ∧
        (∀ i, curvatureQuantum n i = 0) ∧
          (∀ i, spectralQuantum n i = 0) ∧
            candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  have htotal :=
    physicalHauptvermutungTotalDistortion_eq_zero_iff
      (countWindow n) (curvatureBias n) (spectralLocality n)
      (scale n) (edge n) (candidate n)
      (quantizedGate3Residuals_count_nonneg Q n)
      (quantizedGate3Residuals_curvature_nonneg Q n)
      (quantizedGate3Residuals_spectral_nonneg Q n)
  constructor
  · intro hzero
    rcases htotal.1 hzero with
      ⟨hcount, hcurvature, hspectral, hcandidate⟩
    rcases
      (quantizedGate3Residuals_residuals_zero_iff_quantum_zero Q n).1
        ⟨hcount, hcurvature, hspectral⟩ with
      ⟨hcountQuantum, hcurvatureQuantum, hspectralQuantum⟩
    exact
      ⟨hcountQuantum, hcurvatureQuantum, hspectralQuantum, hcandidate⟩
  · rintro ⟨hcountQuantum, hcurvatureQuantum, hspectralQuantum, hcandidate⟩
    rcases
      (quantizedGate3Residuals_residuals_zero_iff_quantum_zero Q n).2
        ⟨hcountQuantum, hcurvatureQuantum, hspectralQuantum⟩ with
      ⟨hcount, hcurvature, hspectral⟩
    exact htotal.2 ⟨hcount, hcurvature, hspectral, hcandidate⟩

/-- Gate 2 semantic target induced by quantized residual observables: each
tracked real residual is zero exactly when its natural occupation counter is
zero.  This is the finite-spectrum zero-set semantics used by the Gate 3
exact-recovery supplier. -/
def gate2QuantizedResidualSemanticTargets
    {ι : Type*}
    (countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ) :
    Gate2HauptvermutungSemanticTargets where
  countWindowZeroSemantic :=
    ∀ n i, countWindow n i = 0 ↔ countQuantum n i = 0
  curvatureBiasZeroSemantic :=
    ∀ n i, curvatureBias n i = 0 ↔ curvatureQuantum n i = 0
  spectralLocalityZeroSemantic :=
    ∀ n i, spectralLocality n i = 0 ↔ spectralQuantum n i = 0

/-- Quantized residuals close Gate 2's finite-spectrum semantic zero-set
target. -/
theorem quantizedGate3Residuals_gate2HauptvermutungSemantic_closed
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {countGap curvatureGap spectralGap : ℝ}
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap) :
    Gate2HauptvermutungSemanticClosed
      (gate2QuantizedResidualSemanticTargets
        countWindow curvatureBias spectralLocality
        countQuantum curvatureQuantum spectralQuantum) := by
  exact
    ⟨quantizedGate3Residuals_count_zero_iff_quantum_zero Q,
      quantizedGate3Residuals_curvature_zero_iff_quantum_zero Q,
      quantizedGate3Residuals_spectral_zero_iff_quantum_zero Q⟩

/-- Raw repair/floor/descent data plus quantized residual observables build the
strong convergence certificate.  This removes the separate nonnegativity
obligations from the microscopic Gate 3 target. -/
theorem physicalHauptvermutungConvergenceCertificate_of_quantizedResiduals
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (R : PhysicalGrowthRepairRefinement w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate)
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap)
    (hstep_pos : 0 < stepFloor)
    (hweight_pos : 0 < weightBase)
    (hsource_pos : 0 < sourceBase)
    (htotal_eq :
      ∀ n,
        total n =
          physicalHauptvermutungTotalDistortion
            (countWindow n) (curvatureBias n) (spectralLocality n)
            (scale n) (edge n) (candidate n))
    (hstep_floor : ∀ n, stepFloor ≤ step n)
    (hweight_floor : ∀ n i, weightBase ≤ w n i)
    (hsource_floor :
      ∀ n i, sourceBase ≤ -centeredSource (w n) (source n) i)
    (hdescent_eq :
      ∀ n,
        descentRate n =
          -linearResponse (w n) (source n)
            (physicalHauptvermutungDistortion
              (countWindow n) (curvatureBias n) (spectralLocality n)
              (scale n) (edge n) (candidate n))) :
    PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase where
  refinement := R
  stepFloor_pos := hstep_pos
  weightBase_pos := hweight_pos
  sourceBase_pos := hsource_pos
  count_nonneg := quantizedGate3Residuals_count_nonneg Q
  curvature_nonneg := quantizedGate3Residuals_curvature_nonneg Q
  spectral_nonneg := quantizedGate3Residuals_spectral_nonneg Q
  total_eq := htotal_eq
  step_floor := hstep_floor
  weight_floor := hweight_floor
  centered_source_floor := hsource_floor
  descent_eq := hdescent_eq

theorem commonResidualGap_pos
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countGap curvatureGap spectralGap : ℝ}
    (G : MicroscopicGate3ComponentResidualGaps
      countWindow curvatureBias spectralLocality
      countGap curvatureGap spectralGap) :
    0 < commonResidualGap countGap curvatureGap spectralGap := by
  unfold commonResidualGap
  exact lt_min G.countGap_pos (lt_min G.curvatureGap_pos G.spectralGap_pos)

theorem componentResidualGaps_common_count_gap
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countGap curvatureGap spectralGap : ℝ}
    (G : MicroscopicGate3ComponentResidualGaps
      countWindow curvatureBias spectralLocality
      countGap curvatureGap spectralGap) :
    ∀ n i,
      countWindow n i ≠ 0 →
        commonResidualGap countGap curvatureGap spectralGap ≤ countWindow n i := by
  intro n i hne
  exact le_trans (min_le_left _ _) (G.count_gap n i hne)

theorem componentResidualGaps_common_curvature_gap
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countGap curvatureGap spectralGap : ℝ}
    (G : MicroscopicGate3ComponentResidualGaps
      countWindow curvatureBias spectralLocality
      countGap curvatureGap spectralGap) :
    ∀ n i,
      curvatureBias n i ≠ 0 →
        commonResidualGap countGap curvatureGap spectralGap ≤
          curvatureBias n i := by
  intro n i hne
  exact
    le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
      (G.curvature_gap n i hne)

theorem componentResidualGaps_common_spectral_gap
    {ι : Type*}
    {countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {countGap curvatureGap spectralGap : ℝ}
    (G : MicroscopicGate3ComponentResidualGaps
      countWindow curvatureBias spectralLocality
      countGap curvatureGap spectralGap) :
    ∀ n i,
      spectralLocality n i ≠ 0 →
        commonResidualGap countGap curvatureGap spectralGap ≤
          spectralLocality n i := by
  intro n i hne
  exact
    le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
      (G.spectral_gap n i hne)

/-- The stronger convergence certificate already contains enough centered
source-floor data to supply the direct aggregate-rate field of
`MicroscopicGate3RatesGaps`.  Thus, once microscopic dynamics supplies the
convergence certificate and finite-spectrum residual gaps, the explicit
aggregate rate can be chosen as `weightBase * sourceBase`. -/
theorem microscopicGate3RatesGaps_of_convergenceCertificate
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase residualGap : ℝ}
    (C : PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase)
    (hgap_pos : 0 < residualGap)
    (hcount_gap :
      ∀ n i, countWindow n i ≠ 0 → residualGap ≤ countWindow n i)
    (hcurvature_gap :
      ∀ n i, curvatureBias n i ≠ 0 → residualGap ≤ curvatureBias n i)
    (hspectral_gap :
      ∀ n i, spectralLocality n i ≠ 0 → residualGap ≤ spectralLocality n i) :
    MicroscopicGate3RatesGaps w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      (weightBase * sourceBase) stepFloor residualGap where
  refinement := C.refinement
  rateBase_pos := mul_pos C.weightBase_pos C.sourceBase_pos
  stepFloor_pos := C.stepFloor_pos
  total_nonneg :=
    physicalHauptvermutungTotalDistortion_sequence_nonneg
      C.count_nonneg C.curvature_nonneg C.spectral_nonneg C.total_eq
  aggregate_rate :=
    physicalHauptvermutungTotalDistortion_uniform_rate_of_centered_source_floor
      C.count_nonneg C.curvature_nonneg C.spectral_nonneg C.total_eq
      (centeredSource_gamma_floor_of_uniform_centered_source_floor
        (le_of_lt C.weightBase_pos) (le_of_lt C.sourceBase_pos)
        C.weight_floor C.centered_source_floor le_rfl)
      C.descent_eq
  step_floor := C.step_floor
  residualGap_pos := hgap_pos
  count_gap := hcount_gap
  curvature_gap := hcurvature_gap
  spectral_gap := hspectral_gap

/-- Componentwise finite-spectrum residual gaps feed the convergence
certificate through the common minimum residual gap. -/
theorem microscopicGate3RatesGaps_of_convergenceCertificate_componentGaps
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (C : PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase)
    (G : MicroscopicGate3ComponentResidualGaps
      countWindow curvatureBias spectralLocality
      countGap curvatureGap spectralGap) :
    MicroscopicGate3RatesGaps w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      (weightBase * sourceBase) stepFloor
      (commonResidualGap countGap curvatureGap spectralGap) := by
  exact
    microscopicGate3RatesGaps_of_convergenceCertificate C
      (commonResidualGap_pos G)
      (componentResidualGaps_common_count_gap G)
      (componentResidualGaps_common_curvature_gap G)
      (componentResidualGaps_common_spectral_gap G)

/-- Quantized residual observables feed the convergence certificate through the
component-gap route. -/
theorem microscopicGate3RatesGaps_of_convergenceCertificate_quantizedResiduals
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (C : PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase)
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap) :
    MicroscopicGate3RatesGaps w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      (weightBase * sourceBase) stepFloor
      (commonResidualGap countGap curvatureGap spectralGap) := by
  exact
    microscopicGate3RatesGaps_of_convergenceCertificate_componentGaps
      C (quantizedGate3Residuals_componentResidualGaps Q)

/-- Raw repair/floor/descent data with quantized residuals directly supplies
the aggregate-rate and residual-gap package. -/
theorem microscopicGate3RatesGaps_of_quantizedConvergenceData
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (R : PhysicalGrowthRepairRefinement w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate)
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap)
    (hstep_pos : 0 < stepFloor)
    (hweight_pos : 0 < weightBase)
    (hsource_pos : 0 < sourceBase)
    (htotal_eq :
      ∀ n,
        total n =
          physicalHauptvermutungTotalDistortion
            (countWindow n) (curvatureBias n) (spectralLocality n)
            (scale n) (edge n) (candidate n))
    (hstep_floor : ∀ n, stepFloor ≤ step n)
    (hweight_floor : ∀ n i, weightBase ≤ w n i)
    (hsource_floor :
      ∀ n i, sourceBase ≤ -centeredSource (w n) (source n) i)
    (hdescent_eq :
      ∀ n,
        descentRate n =
          -linearResponse (w n) (source n)
            (physicalHauptvermutungDistortion
              (countWindow n) (curvatureBias n) (spectralLocality n)
              (scale n) (edge n) (candidate n))) :
    MicroscopicGate3RatesGaps w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      (weightBase * sourceBase) stepFloor
      (commonResidualGap countGap curvatureGap spectralGap) := by
  exact
    microscopicGate3RatesGaps_of_convergenceCertificate_quantizedResiduals
      (physicalHauptvermutungConvergenceCertificate_of_quantizedResiduals
        R Q hstep_pos hweight_pos hsource_pos htotal_eq
        hstep_floor hweight_floor hsource_floor hdescent_eq)
      Q

/-- Named raw Gate 3 target for microscopic dynamics with quantized residuals.

Supplying this structure is now enough to build the convergence certificate,
the aggregate-rate package, the residual-gap package, and the existing Gate 3
exact-recovery certificate. -/
structure MicroscopicGate3QuantizedConvergenceData
    {ι : Type*} [Fintype ι]
    (w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (scale c step descentRate remainder total : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction)
    (countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ)
    (stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ) :
    Prop where
  refinement :
    PhysicalGrowthRepairRefinement w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
  quantizedResiduals :
    QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap
  stepFloor_pos : 0 < stepFloor
  weightBase_pos : 0 < weightBase
  sourceBase_pos : 0 < sourceBase
  total_eq :
    ∀ n,
      total n =
        physicalHauptvermutungTotalDistortion
          (countWindow n) (curvatureBias n) (spectralLocality n)
          (scale n) (edge n) (candidate n)
  step_floor : ∀ n, stepFloor ≤ step n
  weight_floor : ∀ n i, weightBase ≤ w n i
  centered_source_floor :
    ∀ n i, sourceBase ≤ -centeredSource (w n) (source n) i
  descent_eq :
    ∀ n,
      descentRate n =
        -linearResponse (w n) (source n)
          (physicalHauptvermutungDistortion
            (countWindow n) (curvatureBias n) (spectralLocality n)
            (scale n) (edge n) (candidate n))

/-- The named raw Gate 3 target builds the strong convergence certificate. -/
theorem microscopicGate3QuantizedConvergenceData_convergenceCertificate
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase := by
  exact
    physicalHauptvermutungConvergenceCertificate_of_quantizedResiduals
      D.refinement D.quantizedResiduals D.stepFloor_pos D.weightBase_pos
      D.sourceBase_pos D.total_eq D.step_floor D.weight_floor
      D.centered_source_floor D.descent_eq

/-- For the named quantized Gate 3 target, base residual distortion is zero
exactly when the three natural residual occupation families vanish. -/
theorem microscopicGate3QuantizedConvergenceData_baseDistortion_eq_zero_iff_quantum_zero
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (n : ℕ) :
    physicalHauptvermutungBaseDistortion
        (countWindow n) (curvatureBias n) (spectralLocality n) = 0 ↔
      (∀ i, countQuantum n i = 0) ∧
        (∀ i, curvatureQuantum n i = 0) ∧
          (∀ i, spectralQuantum n i = 0) := by
  exact
    quantizedGate3Residuals_baseDistortion_eq_zero_iff_quantum_zero
      D.quantizedResiduals n

/-- For the named quantized Gate 3 target, physical total distortion is zero
exactly when all natural residual occupations vanish and bridge transport is
canonical. -/
theorem microscopicGate3QuantizedConvergenceData_totalDistortion_eq_zero_iff_quantum_zero_and_canonical
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (n : ℕ) :
    physicalHauptvermutungTotalDistortion
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (edge n) (candidate n) = 0 ↔
      (∀ i, countQuantum n i = 0) ∧
        (∀ i, curvatureQuantum n i = 0) ∧
          (∀ i, spectralQuantum n i = 0) ∧
            candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  exact
    quantizedGate3Residuals_totalDistortion_eq_zero_iff_quantum_zero_and_canonical
      D.quantizedResiduals scale edge candidate n

/-- The named quantized Gate 3 target closes Gate 2's finite-spectrum semantic
zero-set target for count, curvature, and spectral/locality residuals. -/
theorem microscopicGate3QuantizedConvergenceData_gate2HauptvermutungSemantic_closed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    Gate2HauptvermutungSemanticClosed
      (gate2QuantizedResidualSemanticTargets
        countWindow curvatureBias spectralLocality
        countQuantum curvatureQuantum spectralQuantum) := by
  exact
    quantizedGate3Residuals_gate2HauptvermutungSemantic_closed
      D.quantizedResiduals

/-- The scalar `total` used by the convergence proof is a complete detector
for quantized residual vacuum plus canonical bridge transport. -/
theorem microscopicGate3QuantizedConvergenceData_total_eq_zero_iff_quantum_zero_and_canonical
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (n : ℕ) :
    total n = 0 ↔
      (∀ i, countQuantum n i = 0) ∧
        (∀ i, curvatureQuantum n i = 0) ∧
          (∀ i, spectralQuantum n i = 0) ∧
            candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  rw [D.total_eq n]
  exact
    microscopicGate3QuantizedConvergenceData_totalDistortion_eq_zero_iff_quantum_zero_and_canonical
      D n

/-- In the named quantized Gate 3 target, scalar zero at a stage already
constructs the recovered physical-Hauptvermutung stage at that same stage. -/
theorem microscopicGate3QuantizedConvergenceData_recoveredStage_of_total_zero
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    {n : ℕ}
    (htotal : total n = 0) :
    PhysicalHauptvermutungRecoveredStage
      (countWindow n) (curvatureBias n) (spectralLocality n)
      (scale n) (total n) (edge n) (candidate n) := by
  rcases
    (microscopicGate3QuantizedConvergenceData_total_eq_zero_iff_quantum_zero_and_canonical
      D n).1 htotal with
    ⟨hcountQuantum, hcurvatureQuantum, hspectralQuantum, hcandidate⟩
  rcases
    (quantizedGate3Residuals_residuals_zero_iff_quantum_zero
      D.quantizedResiduals n).2
      ⟨hcountQuantum, hcurvatureQuantum, hspectralQuantum⟩ with
    ⟨hcount, hcurvature, hspectral⟩
  have hbridge :
      cSpecBridgeTotalDistortion
        (scale n) (edge n) (candidate n) = 0 :=
    (cSpecBridgeTotalDistortion_eq_zero_iff_candidate_eq_canonical
      (scale n) (edge n) (candidate n)).2 hcandidate
  refine
    { total_zero := htotal
      local_distortion_zero := ?_
      bridge_total_zero := hbridge
      order_recovered :=
        cSpecBridgeTotalDistortion_zero_orderRecovered
          (scale n) (edge n) (candidate n) hbridge }
  intro i
  have hcandidate_i :
      candidate n i = fourState.perm (edge n i) := by
    simpa [canonicalCSpecBridgeCandidate] using congrFun hcandidate i
  exact
    (physicalHauptvermutungDistortion_zero_iff
      (countWindow n) (curvatureBias n) (spectralLocality n)
      (scale n) (edge n) (candidate n) i
      (quantizedGate3Residuals_count_nonneg D.quantizedResiduals n i)
      (quantizedGate3Residuals_curvature_nonneg D.quantizedResiduals n i)
      (quantizedGate3Residuals_spectral_nonneg D.quantizedResiduals n i)).2
      ⟨hcount i, hcurvature i, hspectral i, hcandidate_i⟩

/-- For the named quantized Gate 3 target, recovered-stage status at a stage
is equivalent to scalar zero at that stage. -/
theorem microscopicGate3QuantizedConvergenceData_recoveredStage_iff_total_zero
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (n : ℕ) :
    PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) ↔
      total n = 0 := by
  constructor
  · intro R
    exact R.total_zero
  · intro htotal
    exact
      microscopicGate3QuantizedConvergenceData_recoveredStage_of_total_zero
        D htotal

/-- Eventual scalar zero is exactly eventual quantized residual vacuum plus
canonical bridge transport. -/
theorem microscopicGate3QuantizedConvergenceData_eventually_total_zero_iff_quantum_zero_and_canonical
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    (∀ᶠ n in atTop, total n = 0) ↔
      ∀ᶠ n in atTop,
        (∀ i, countQuantum n i = 0) ∧
          (∀ i, curvatureQuantum n i = 0) ∧
            (∀ i, spectralQuantum n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  constructor
  · intro htotal
    filter_upwards [htotal] with n hzero
    exact
      (microscopicGate3QuantizedConvergenceData_total_eq_zero_iff_quantum_zero_and_canonical
        D n).1 hzero
  · intro hquantum
    filter_upwards [hquantum] with n hn
    exact
      (microscopicGate3QuantizedConvergenceData_total_eq_zero_iff_quantum_zero_and_canonical
        D n).2 hn

/-- Eventual recovered-stage status is exactly eventual scalar zero. -/
theorem microscopicGate3QuantizedConvergenceData_eventually_recoveredStage_iff_total_zero
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    (∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)) ↔
      ∀ᶠ n in atTop, total n = 0 := by
  constructor
  · intro hstage
    filter_upwards [hstage] with n R
    exact R.total_zero
  · intro htotal
    filter_upwards [htotal] with n hzero
    exact
      microscopicGate3QuantizedConvergenceData_recoveredStage_of_total_zero
        D hzero

/-- A finite scalar-zero tail is exactly a finite tail of quantized residual
vacuum plus canonical bridge transport. -/
theorem microscopicGate3QuantizedConvergenceData_exists_total_zero_after_iff_quantum_zero_and_canonical_after
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    (∃ N, ∀ n, N ≤ n → total n = 0) ↔
      ∃ N, ∀ n, N ≤ n →
        (∀ i, countQuantum n i = 0) ∧
          (∀ i, curvatureQuantum n i = 0) ∧
            (∀ i, spectralQuantum n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  constructor
  · rintro ⟨N, hN⟩
    exact
      ⟨N, fun n hn =>
        (microscopicGate3QuantizedConvergenceData_total_eq_zero_iff_quantum_zero_and_canonical
          D n).1 (hN n hn)⟩
  · rintro ⟨N, hN⟩
    exact
      ⟨N, fun n hn =>
        (microscopicGate3QuantizedConvergenceData_total_eq_zero_iff_quantum_zero_and_canonical
          D n).2 (hN n hn)⟩

/-- A finite recovered-stage tail is exactly a finite scalar-zero tail. -/
theorem microscopicGate3QuantizedConvergenceData_exists_recovered_after_iff_total_zero_after
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    (∃ N, ∀ n, N ≤ n →
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)) ↔
      ∃ N, ∀ n, N ≤ n → total n = 0 := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun n hn => (hN n hn).total_zero⟩
  · rintro ⟨N, hN⟩
    exact
      ⟨N, fun n hn =>
        microscopicGate3QuantizedConvergenceData_recoveredStage_of_total_zero
          D (hN n hn)⟩

/-- In the named quantized Gate 3 target, scalar zero at a stage also kills
the finite RSS/Poisson horizon-error budget at that same stage. -/
theorem microscopicGate3QuantizedConvergenceData_rssPoissonError_zero_of_total_zero
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    {n : ℕ}
    (htotal : total n = 0)
    (errorScale : ℝ) :
    ∀ i,
      rssPoissonError (countWindow n i) (curvatureBias n i) errorScale = 0 := by
  intro i
  exact
    (microscopicGate3QuantizedConvergenceData_recoveredStage_of_total_zero
      D htotal).rssPoissonError_zero
      (quantizedGate3Residuals_count_nonneg D.quantizedResiduals n)
      (quantizedGate3Residuals_curvature_nonneg D.quantizedResiduals n)
      (quantizedGate3Residuals_spectral_nonneg D.quantizedResiduals n)
      i

/-- Eventual scalar zero directly kills the finite RSS/Poisson horizon-error
budget, without unpacking the exact-recovery certificate. -/
theorem microscopicGate3QuantizedConvergenceData_eventually_rssPoissonError_zero_of_eventually_total_zero
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (errorScale : ℝ)
    (htotal : ∀ᶠ n in atTop, total n = 0) :
    ∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0 := by
  filter_upwards [htotal] with n hzero
  exact
    microscopicGate3QuantizedConvergenceData_rssPoissonError_zero_of_total_zero
      D hzero errorScale

/-- A finite scalar-zero tail directly kills the finite RSS/Poisson
horizon-error budget after the same threshold. -/
theorem microscopicGate3QuantizedConvergenceData_exists_rssPoissonError_zero_after_of_exists_total_zero_after
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (errorScale : ℝ)
    (htotal : ∃ N, ∀ n, N ≤ n → total n = 0) :
    ∃ N, ∀ n, N ≤ n →
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0 := by
  rcases htotal with ⟨N, hN⟩
  exact
    ⟨N, fun n hn =>
      microscopicGate3QuantizedConvergenceData_rssPoissonError_zero_of_total_zero
        D (hN n hn) errorScale⟩

/-- Full microscopic Gate 3 supplier: the direct rate/gap package together
with the stronger convergence certificate needed by the existing exact-recovery
API.  In future instantiations, the same microscopic causal growth law should
construct both fields from its one-step Lyapunov drift and finite-spectrum
residual observables. -/
structure MicroscopicGate3ExactRecoverySupplier
    {ι : Type*} [Fintype ι]
    (w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (scale c step descentRate remainder total : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction)
    (rateBase stepFloor weightBase sourceBase residualGap : ℝ) : Prop where
  ratesGaps :
    MicroscopicGate3RatesGaps w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      rateBase stepFloor residualGap
  convergence :
    PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase

/-- A convergence certificate plus finite-spectrum residual gaps is already a
full exact-recovery supplier.  This is the current Lean endpoint for Gate 3:
microscopic dynamics can now focus on constructing the convergence certificate
and the three residual-gap hypotheses. -/
theorem microscopicGate3ExactRecoverySupplier_of_convergenceCertificate
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase residualGap : ℝ}
    (C : PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase)
    (hgap_pos : 0 < residualGap)
    (hcount_gap :
      ∀ n i, countWindow n i ≠ 0 → residualGap ≤ countWindow n i)
    (hcurvature_gap :
      ∀ n i, curvatureBias n i ≠ 0 → residualGap ≤ curvatureBias n i)
    (hspectral_gap :
      ∀ n i, spectralLocality n i ≠ 0 → residualGap ≤ spectralLocality n i) :
    MicroscopicGate3ExactRecoverySupplier w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      (weightBase * sourceBase) stepFloor weightBase sourceBase residualGap := by
  exact
    ⟨microscopicGate3RatesGaps_of_convergenceCertificate C
        hgap_pos hcount_gap hcurvature_gap hspectral_gap,
      C⟩

/-- Componentwise finite-spectrum residual gaps plus a convergence certificate
are already a full exact-recovery supplier, with the residual gap chosen as the
minimum of the three component gaps. -/
theorem microscopicGate3ExactRecoverySupplier_of_convergenceCertificate_componentGaps
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (C : PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase)
    (G : MicroscopicGate3ComponentResidualGaps
      countWindow curvatureBias spectralLocality
      countGap curvatureGap spectralGap) :
    MicroscopicGate3ExactRecoverySupplier w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      (weightBase * sourceBase) stepFloor weightBase sourceBase
      (commonResidualGap countGap curvatureGap spectralGap) := by
  exact
    ⟨microscopicGate3RatesGaps_of_convergenceCertificate_componentGaps C G,
      C⟩

/-- Quantized residual observables plus a convergence certificate are already a
full exact-recovery supplier. -/
theorem microscopicGate3ExactRecoverySupplier_of_convergenceCertificate_quantizedResiduals
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (C : PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase)
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap) :
    MicroscopicGate3ExactRecoverySupplier w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      (weightBase * sourceBase) stepFloor weightBase sourceBase
      (commonResidualGap countGap curvatureGap spectralGap) := by
  exact
    ⟨microscopicGate3RatesGaps_of_convergenceCertificate_quantizedResiduals
        C Q,
      C⟩

/-- Raw repair/floor/descent data with quantized residuals directly supplies
the full Gate 3 exact-recovery supplier.  This is the narrowest current formal
target for microscopic dynamics. -/
theorem microscopicGate3ExactRecoverySupplier_of_quantizedConvergenceData
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (R : PhysicalGrowthRepairRefinement w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate)
    (Q : QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap)
    (hstep_pos : 0 < stepFloor)
    (hweight_pos : 0 < weightBase)
    (hsource_pos : 0 < sourceBase)
    (htotal_eq :
      ∀ n,
        total n =
          physicalHauptvermutungTotalDistortion
            (countWindow n) (curvatureBias n) (spectralLocality n)
            (scale n) (edge n) (candidate n))
    (hstep_floor : ∀ n, stepFloor ≤ step n)
    (hweight_floor : ∀ n i, weightBase ≤ w n i)
    (hsource_floor :
      ∀ n i, sourceBase ≤ -centeredSource (w n) (source n) i)
    (hdescent_eq :
      ∀ n,
        descentRate n =
          -linearResponse (w n) (source n)
            (physicalHauptvermutungDistortion
              (countWindow n) (curvatureBias n) (spectralLocality n)
              (scale n) (edge n) (candidate n))) :
    MicroscopicGate3ExactRecoverySupplier w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      (weightBase * sourceBase) stepFloor weightBase sourceBase
      (commonResidualGap countGap curvatureGap spectralGap) := by
  exact
    microscopicGate3ExactRecoverySupplier_of_convergenceCertificate_quantizedResiduals
      (physicalHauptvermutungConvergenceCertificate_of_quantizedResiduals
        R Q hstep_pos hweight_pos hsource_pos htotal_eq
        hstep_floor hweight_floor hsource_floor hdescent_eq)
      Q

/-- The named raw Gate 3 target directly supplies the full exact-recovery
supplier. -/
theorem microscopicGate3QuantizedConvergenceData_exactRecoverySupplier
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    MicroscopicGate3ExactRecoverySupplier w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      (weightBase * sourceBase) stepFloor weightBase sourceBase
      (commonResidualGap countGap curvatureGap spectralGap) := by
  exact
    microscopicGate3ExactRecoverySupplier_of_quantizedConvergenceData
      D.refinement D.quantizedResiduals D.stepFloor_pos D.weightBase_pos
      D.sourceBase_pos D.total_eq D.step_floor D.weight_floor
      D.centered_source_floor D.descent_eq

/-- The exact-recovery certificate induced directly by the named raw quantized
Gate 3 target. -/
def microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    PhysicalHauptvermutungExactRecoveryCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase
      (commonResidualGap countGap curvatureGap spectralGap) where
  convergence :=
    (microscopicGate3QuantizedConvergenceData_exactRecoverySupplier D).convergence
  residualGap_pos :=
    (microscopicGate3QuantizedConvergenceData_exactRecoverySupplier D).ratesGaps.residualGap_pos
  count_gap :=
    (microscopicGate3QuantizedConvergenceData_exactRecoverySupplier D).ratesGaps.count_gap
  curvature_gap :=
    (microscopicGate3QuantizedConvergenceData_exactRecoverySupplier D).ratesGaps.curvature_gap
  spectral_gap :=
    (microscopicGate3QuantizedConvergenceData_exactRecoverySupplier D).ratesGaps.spectral_gap

/-- The exact-recovery certificate induced by a full microscopic Gate 3
supplier. -/
def microscopicGate3ExactRecoveryCertificate
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {rateBase stepFloor weightBase sourceBase residualGap : ℝ}
    (S : MicroscopicGate3ExactRecoverySupplier w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      rateBase stepFloor weightBase sourceBase residualGap) :
    PhysicalHauptvermutungExactRecoveryCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase residualGap where
  convergence := S.convergence
  residualGap_pos := S.ratesGaps.residualGap_pos
  count_gap := S.ratesGaps.count_gap
  curvature_gap := S.ratesGaps.curvature_gap
  spectral_gap := S.ratesGaps.spectral_gap

/-- A full microscopic Gate 3 supplier closes the direct aggregate-rate
subcertificate. -/
theorem microscopicGate3ExactRecoverySupplier_aggregateRateContraction_closed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {rateBase stepFloor weightBase sourceBase residualGap : ℝ}
    (S : MicroscopicGate3ExactRecoverySupplier w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      rateBase stepFloor weightBase sourceBase residualGap) :
    Gate3AggregateRateContractionClosed
      S.ratesGaps.refinement rateBase stepFloor := by
  exact microscopicGate3RatesGaps_aggregateRateContraction_closed S.ratesGaps

/-- A full microscopic Gate 3 supplier closes the residual exact-zero
subcertificate. -/
theorem microscopicGate3ExactRecoverySupplier_residualGapExactZero_closed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {rateBase stepFloor weightBase sourceBase residualGap : ℝ}
    (S : MicroscopicGate3ExactRecoverySupplier w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      rateBase stepFloor weightBase sourceBase residualGap) :
    Gate3ResidualGapExactZeroClosed S.convergence residualGap := by
  exact
    microscopicGate3RatesGaps_residualGapExactZero_closed
      S.ratesGaps S.convergence

/-- A full microscopic Gate 3 supplier closes the existing Gate 3 exact-recovery
certificate hook. -/
theorem microscopicGate3ExactRecoverySupplier_gate3ExactRecovery_closed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {rateBase stepFloor weightBase sourceBase residualGap : ℝ}
    (S : MicroscopicGate3ExactRecoverySupplier w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      rateBase stepFloor weightBase sourceBase residualGap) :
    Gate3ExactRecoveryCertificateClosed
      (microscopicGate3ExactRecoveryCertificate S) := by
  exact gate3_exactRecoveryCertificate_closed
    (microscopicGate3ExactRecoveryCertificate S)

/-- Combined Gate 3 output of the microscopic supplier. -/
theorem microscopicGate3ExactRecoverySupplier_closed_outputs
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {rateBase stepFloor weightBase sourceBase residualGap : ℝ}
    (S : MicroscopicGate3ExactRecoverySupplier w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      rateBase stepFloor weightBase sourceBase residualGap) :
    Gate3AggregateRateContractionClosed
        S.ratesGaps.refinement rateBase stepFloor ∧
      Gate3ResidualGapExactZeroClosed S.convergence residualGap ∧
        Gate3ExactRecoveryCertificateClosed
          (microscopicGate3ExactRecoveryCertificate S) := by
  exact
    ⟨microscopicGate3ExactRecoverySupplier_aggregateRateContraction_closed S,
      microscopicGate3ExactRecoverySupplier_residualGapExactZero_closed S,
      microscopicGate3ExactRecoverySupplier_gate3ExactRecovery_closed S⟩

/-- Combined Gate 3 output directly from the named raw quantized target. -/
theorem microscopicGate3QuantizedConvergenceData_closed_outputs
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    Gate3AggregateRateContractionClosed
        (microscopicGate3QuantizedConvergenceData_exactRecoverySupplier
          D).ratesGaps.refinement
        (weightBase * sourceBase) stepFloor ∧
      Gate3ResidualGapExactZeroClosed
        (microscopicGate3QuantizedConvergenceData_exactRecoverySupplier
          D).convergence
        (commonResidualGap countGap curvatureGap spectralGap) ∧
        Gate3ExactRecoveryCertificateClosed
          (microscopicGate3ExactRecoveryCertificate
            (microscopicGate3QuantizedConvergenceData_exactRecoverySupplier
              D)) := by
  exact
    microscopicGate3ExactRecoverySupplier_closed_outputs
      (microscopicGate3QuantizedConvergenceData_exactRecoverySupplier D)

/-- Direct eventual exact-zero output from the named raw quantized Gate 3
target. -/
theorem microscopicGate3QuantizedConvergenceData_eventually_exact_zero
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    ∀ᶠ n in atTop,
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  exact
    physicalHauptvermutungExactRecoveryCertificate_eventually_exact_zero
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate D)

/-- Direct eventual recovered-stage output from the named raw quantized Gate 3
target. -/
theorem microscopicGate3QuantizedConvergenceData_eventually_recoveredStage
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  exact
    physicalHauptvermutungExactRecoveryCertificate_eventually_recoveredStage
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate D)

/-- Direct eventual full operational recovery from the named raw quantized
Gate 3 target. -/
theorem microscopicGate3QuantizedConvergenceData_eventually_full_operational_recovery
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    ∀ᶠ n in atTop,
      total n = 0 ∧
        (∀ i,
          physicalHauptvermutungDistortion
            (countWindow n) (curvatureBias n) (spectralLocality n)
            (scale n) (edge n) (candidate n) i = 0) ∧
          cSpecBridgeTotalDistortion (scale n) (edge n) (candidate n) = 0 ∧
            (∀ i a b,
              Cov fourState (GPoint.atom (fourState.dst (edge n i)) b)
                  (GPoint.bridge (edge n i) a) →
                b = candidate n i a) := by
  exact
    physicalHauptvermutungExactRecoveryCertificate_eventually_full_operational_recovery
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate D)

/-- Direct finite-threshold exact-zero output from the named raw quantized
Gate 3 target. -/
theorem microscopicGate3QuantizedConvergenceData_exists_exact_zero_after
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    ∃ N, ∀ n, N ≤ n →
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  have hexact :
      ∀ᶠ n in atTop,
        total n = 0 ∧
          (∀ i, countWindow n i = 0) ∧
            (∀ i, curvatureBias n i = 0) ∧
              (∀ i, spectralLocality n i = 0) ∧
                candidate n = canonicalCSpecBridgeCandidate (edge n) :=
    microscopicGate3QuantizedConvergenceData_eventually_exact_zero D
  rw [eventually_atTop] at hexact
  exact hexact

/-- Direct eventual zero of the natural quantized residual occupations from
the named raw quantized Gate 3 target. -/
theorem microscopicGate3QuantizedConvergenceData_eventually_quantum_zero
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    ∀ᶠ n in atTop,
      (∀ i, countQuantum n i = 0) ∧
        (∀ i, curvatureQuantum n i = 0) ∧
          (∀ i, spectralQuantum n i = 0) := by
  have hexact :
      ∀ᶠ n in atTop,
        total n = 0 ∧
          (∀ i, countWindow n i = 0) ∧
            (∀ i, curvatureBias n i = 0) ∧
              (∀ i, spectralLocality n i = 0) ∧
                candidate n = canonicalCSpecBridgeCandidate (edge n) :=
    microscopicGate3QuantizedConvergenceData_eventually_exact_zero D
  filter_upwards [hexact] with n hn
  rcases hn with ⟨_htotal, hcount, hcurvature, hspectral, _hcandidate⟩
  exact
    ⟨fun i =>
        quantizedGate3Residuals_countQuantum_eq_zero_of_count_zero
          D.quantizedResiduals n i (hcount i),
      fun i =>
        quantizedGate3Residuals_curvatureQuantum_eq_zero_of_curvature_zero
          D.quantizedResiduals n i (hcurvature i),
      fun i =>
        quantizedGate3Residuals_spectralQuantum_eq_zero_of_spectral_zero
          D.quantizedResiduals n i (hspectral i)⟩

/-- Direct finite-threshold zero of the natural quantized residual occupations
from the named raw quantized Gate 3 target. -/
theorem microscopicGate3QuantizedConvergenceData_exists_quantum_zero_after
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    ∃ N, ∀ n, N ≤ n →
      (∀ i, countQuantum n i = 0) ∧
        (∀ i, curvatureQuantum n i = 0) ∧
          (∀ i, spectralQuantum n i = 0) := by
  have hquantum :
      ∀ᶠ n in atTop,
        (∀ i, countQuantum n i = 0) ∧
          (∀ i, curvatureQuantum n i = 0) ∧
            (∀ i, spectralQuantum n i = 0) :=
    microscopicGate3QuantizedConvergenceData_eventually_quantum_zero D
  rw [eventually_atTop] at hquantum
  exact hquantum

/-- Direct eventual simultaneous zero of real residuals and natural quantized
residual occupations from the named raw quantized Gate 3 target. -/
theorem microscopicGate3QuantizedConvergenceData_eventually_exact_and_quantum_zero
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    ∀ᶠ n in atTop,
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) ∧
                (∀ i, countQuantum n i = 0) ∧
                  (∀ i, curvatureQuantum n i = 0) ∧
                    (∀ i, spectralQuantum n i = 0) := by
  have hexact :=
    microscopicGate3QuantizedConvergenceData_eventually_exact_zero D
  have hquantum :=
    microscopicGate3QuantizedConvergenceData_eventually_quantum_zero D
  filter_upwards [hexact, hquantum] with n hexact_n hquantum_n
  rcases hexact_n with
    ⟨htotal, hcount, hcurvature, hspectral, hcandidate⟩
  rcases hquantum_n with
    ⟨hcountQuantum, hcurvatureQuantum, hspectralQuantum⟩
  exact
    ⟨htotal, hcount, hcurvature, hspectral, hcandidate,
      hcountQuantum, hcurvatureQuantum, hspectralQuantum⟩

/-- Direct finite-threshold simultaneous zero of real residuals and natural
quantized residual occupations from the named raw quantized Gate 3 target. -/
theorem microscopicGate3QuantizedConvergenceData_exists_exact_and_quantum_zero_after
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    ∃ N, ∀ n, N ≤ n →
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n) ∧
                (∀ i, countQuantum n i = 0) ∧
                  (∀ i, curvatureQuantum n i = 0) ∧
                    (∀ i, spectralQuantum n i = 0) := by
  have hcombined :
      ∀ᶠ n in atTop,
        total n = 0 ∧
          (∀ i, countWindow n i = 0) ∧
            (∀ i, curvatureBias n i = 0) ∧
              (∀ i, spectralLocality n i = 0) ∧
                candidate n = canonicalCSpecBridgeCandidate (edge n) ∧
                  (∀ i, countQuantum n i = 0) ∧
                    (∀ i, curvatureQuantum n i = 0) ∧
                      (∀ i, spectralQuantum n i = 0) :=
    microscopicGate3QuantizedConvergenceData_eventually_exact_and_quantum_zero
      D
  rw [eventually_atTop] at hcombined
  exact hcombined

/-- Direct finite-threshold recovered-stage output from the named raw
quantized Gate 3 target. -/
theorem microscopicGate3QuantizedConvergenceData_exists_recovered_after
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    ∃ N, ∀ n, N ≤ n →
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n) := by
  exact
    physicalHauptvermutungExactRecoveryCertificate_exists_recovered_after
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate D)

/-- Direct finite-threshold observable-zero output from the named raw quantized
Gate 3 target. -/
theorem microscopicGate3QuantizedConvergenceData_exists_observable_zero_after
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    ∃ N, ∀ n, N ≤ n →
      total n = 0 ∧
        physicalHauptvermutungTotalDistortion
          (countWindow n) (curvatureBias n) (spectralLocality n)
          (scale n) (edge n) (candidate n) = 0 ∧
        physicalHauptvermutungBaseDistortion
          (countWindow n) (curvatureBias n) (spectralLocality n) = 0 ∧
        cSpecBridgeTotalDistortion (scale n) (edge n) (candidate n) = 0 ∧
        candidate n = canonicalCSpecBridgeCandidate (edge n) ∧
        (∀ i, countWindow n i = 0) ∧
        (∀ i, curvatureBias n i = 0) ∧
        (∀ i, spectralLocality n i = 0) ∧
        (∀ i a b,
          Cov fourState (GPoint.atom (fourState.dst (edge n i)) b)
              (GPoint.bridge (edge n i) a) →
            b = candidate n i a) := by
  exact
    physicalHauptvermutungExactRecoveryCertificate_exists_observable_zero_after
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate D)

/-- Direct horizon-protection plus eventual exact-zero output from the named
raw quantized Gate 3 target. -/
theorem microscopicGate3QuantizedConvergenceData_horizonProtection_and_eventually_exact_zero
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    (∀ n,
      linearResponse (w n) (source n) (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse (w n) (source n)
          (finiteAreaChange (c n) (J n)) = 0) ∧
      ∀ᶠ n in atTop,
        total n = 0 ∧
          (∀ i, countWindow n i = 0) ∧
            (∀ i, curvatureBias n i = 0) ∧
              (∀ i, spectralLocality n i = 0) ∧
                candidate n = canonicalCSpecBridgeCandidate (edge n) := by
  exact
    ⟨(physicalHauptvermutungConvergenceCertificate_horizon_protection_and_total_tendsto_zero
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate
        D).convergence).1,
      microscopicGate3QuantizedConvergenceData_eventually_exact_zero D⟩

/-- Direct horizon-protection plus eventual full operational recovery from the
named raw quantized Gate 3 target. -/
theorem microscopicGate3QuantizedConvergenceData_horizonProtection_and_eventually_full_recovery
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    (∀ n,
      linearResponse (w n) (source n) (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse (w n) (source n)
          (finiteAreaChange (c n) (J n)) = 0) ∧
      ∀ᶠ n in atTop,
        total n = 0 ∧
          (∀ i,
            physicalHauptvermutungDistortion
              (countWindow n) (curvatureBias n) (spectralLocality n)
              (scale n) (edge n) (candidate n) i = 0) ∧
            cSpecBridgeTotalDistortion (scale n) (edge n) (candidate n) = 0 ∧
              (∀ i a b,
                Cov fourState (GPoint.atom (fourState.dst (edge n i)) b)
                    (GPoint.bridge (edge n i) a) →
                  b = candidate n i a) := by
  exact
    physicalHauptvermutungExactRecoveryCertificate_horizon_protection_and_eventually_full_recovery
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate D)

/-- Direct horizon-protection plus finite recovered-stage threshold from the
named raw quantized Gate 3 target. -/
theorem microscopicGate3QuantizedConvergenceData_horizonProtection_and_recovered_after
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    (∀ n,
      linearResponse (w n) (source n) (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse (w n) (source n)
          (finiteAreaChange (c n) (J n)) = 0) ∧
      ∃ N, ∀ n, N ≤ n →
        PhysicalHauptvermutungRecoveredStage
          (countWindow n) (curvatureBias n) (spectralLocality n)
          (scale n) (total n) (edge n) (candidate n) := by
  exact
    physicalHauptvermutungExactRecoveryCertificate_horizon_protection_and_recovered_after
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate D)

/-- Direct Gate 3-to-Gate 4 RSS/Poisson handoff from the named raw quantized
Gate 3 target. -/
theorem microscopicGate3QuantizedConvergenceData_gate4ExactRecoveryRSSPoisson_closed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (errorScale : ℝ) :
    Gate4ExactRecoveryRSSPoissonClosed
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate D)
      errorScale := by
  exact
    gate4_exactRecoveryRSSPoisson_closed
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate D)
      errorScale

/-- Direct eventual Gate 4 RSS/Poisson zero from the named raw quantized Gate
3 target. -/
theorem microscopicGate3QuantizedConvergenceData_eventually_rssPoissonError_zero
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (errorScale : ℝ) :
    ∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0 := by
  exact
    (microscopicGate3QuantizedConvergenceData_gate4ExactRecoveryRSSPoisson_closed
      D errorScale).eventuallyRSSPoissonErrorZero

/-- Direct finite-threshold Gate 4 RSS/Poisson zero from the named raw
quantized Gate 3 target. -/
theorem microscopicGate3QuantizedConvergenceData_exists_rssPoissonError_zero_after
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (errorScale : ℝ) :
    ∃ N, ∀ n, N ≤ n →
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0 := by
  exact
    (microscopicGate3QuantizedConvergenceData_gate4ExactRecoveryRSSPoisson_closed
      D errorScale).rssPoissonErrorZeroAfter

/-- Package a named quantized Gate 3 target as the exact recovered finite CSpec
sequence consumed by the Gate 4 chart interfaces. -/
def microscopicGate3QuantizedConvergenceData_toRecoveredStageExactCSpecSequence
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap) :
    RecoveredStageExactCSpecSequence ι where
  cSpecWeight := w
  horizonSource := J
  repairSource := source
  countWindow := countWindow
  curvatureBias := curvatureBias
  spectralLocality := spectralLocality
  scale := scale
  areaCoeff := c
  step := step
  descentRate := descentRate
  remainder := remainder
  total := total
  edge := edge
  candidate := candidate
  stepFloor := stepFloor
  weightBase := weightBase
  sourceBase := sourceBase
  residualGap := commonResidualGap countGap curvatureGap spectralGap
  exact_recovery :=
    microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate D

/-- Package a named quantized Gate 3 target plus recovered 4D chart data into
the recovered-stage chart interface consumed by Gate 4. -/
def microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DChartInterface
    {ι chart point : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (chartData : RecoveredStageBDG4DChartData ι chart point) :
    RecoveredStageBDG4DChartInterface ι chart point where
  recovered :=
    microscopicGate3QuantizedConvergenceData_toRecoveredStageExactCSpecSequence
      D
  chartData := chartData

/-- Direct chart-level recovered-stage and sampled 4D operator-limit output
from quantized Gate 3 data plus recovered chart data. -/
theorem microscopicGate3QuantizedConvergenceData_recoveredStage_and_chart_operator_tendsto
    {ι chart point : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (chartData : RecoveredStageBDG4DChartData ι chart point) :
    (∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            chartData.operatorData (chartData.density n))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target chartData.operatorData)) := by
  simpa
    [microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DChartInterface,
      microscopicGate3QuantizedConvergenceData_toRecoveredStageExactCSpecSequence]
    using
      RecoveredStageBDG4DChartInterface.recoveredStage_and_chart_operator_tendsto
        (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DChartInterface
          D chartData)

/-- Direct chart-level RSS/Poisson zero and sampled 4D operator-limit output
from quantized Gate 3 data plus recovered chart data. -/
theorem microscopicGate3QuantizedConvergenceData_rssPoissonError_zero_and_chart_operator_tendsto
    {ι chart point : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (chartData : RecoveredStageBDG4DChartData ι chart point)
    (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            chartData.operatorData (chartData.density n))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target chartData.operatorData)) := by
  simpa
    [microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DChartInterface,
      microscopicGate3QuantizedConvergenceData_toRecoveredStageExactCSpecSequence]
    using
      RecoveredStageBDG4DChartInterface.rssPoissonError_zero_and_chart_operator_tendsto
        (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DChartInterface
          D chartData)
        errorScale

/-- Package a named quantized Gate 3 target together with analytic 4D BDG
operator-profile data into the recovered-stage BDG operator interface consumed
by Gate 4.  The microscopic contribution is exactly the induced exact-recovery
certificate; the remaining inputs are the analytic density and operator profile
data. -/
def microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DOperatorInterface
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (density : ℕ → ℝ)
    (hdensity : Tendsto density atTop atTop)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorData : BDG4DOperatorProfileData) :
    RecoveredStageBDG4DOperatorInterface ι where
  cSpecWeight := w
  horizonSource := J
  repairSource := source
  countWindow := countWindow
  curvatureBias := curvatureBias
  spectralLocality := spectralLocality
  scale := scale
  areaCoeff := c
  step := step
  descentRate := descentRate
  remainder := remainder
  total := total
  edge := edge
  candidate := candidate
  stepFloor := stepFloor
  weightBase := weightBase
  sourceBase := sourceBase
  residualGap := commonResidualGap countGap curvatureGap spectralGap
  density := density
  density_tendsto_atTop := hdensity
  phiAtPoint := phiAtPoint
  curvaturePhi := curvaturePhi
  operatorData := operatorData
  exact_recovery :=
    microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate D

/-- The quantized Gate 3 target plus analytic 4D operator-profile data closes
the recovered-stage BDG operator bridge sublayer. -/
theorem microscopicGate3QuantizedConvergenceData_recoveredBDGOperatorBridge_closed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (density : ℕ → ℝ)
    (hdensity : Tendsto density atTop atTop)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorData : BDG4DOperatorProfileData) :
    Gate4RecoveredBDGOperatorBridgeClosed
      (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DOperatorInterface
        D density hdensity phiAtPoint curvaturePhi operatorData) := by
  exact
    gate4_recoveredBDGOperatorBridge_closed
      (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DOperatorInterface
        D density hdensity phiAtPoint curvaturePhi operatorData)

/-- Direct Gate 3-to-Gate 4 recovered-stage and sampled 4D operator-limit
output from quantized microscopic data plus analytic operator-profile data. -/
theorem microscopicGate3QuantizedConvergenceData_recoveredStage_and_bdg4d_operator_tendsto
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (density : ℕ → ℝ)
    (hdensity : Tendsto density atTop atTop)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorData : BDG4DOperatorProfileData) :
    (∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)) ∧
      Tendsto
        (fun n => BDG4DOperatorProfileData.mean operatorData (density n))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target operatorData)) := by
  simpa
    [microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DOperatorInterface]
    using
      gate4_recoveredStage_bdg4d_operator_limit_of_interface
        (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DOperatorInterface
          D density hdensity phiAtPoint curvaturePhi operatorData)

/-- The quantized Gate 3 target plus analytic 4D operator-profile data also
closes Gate 4's recovered-stage/RSS-Poisson/operator bridge sublayer. -/
theorem microscopicGate3QuantizedConvergenceData_recoveredBDGPoissonOperatorBridge_closed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (density : ℕ → ℝ)
    (hdensity : Tendsto density atTop atTop)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorData : BDG4DOperatorProfileData)
    (errorScale : ℝ) :
    Gate4RecoveredBDGPoissonOperatorBridgeClosed
      (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DOperatorInterface
        D density hdensity phiAtPoint curvaturePhi operatorData)
      errorScale := by
  exact
    gate4_recoveredBDGPoissonOperatorBridge_closed
      (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DOperatorInterface
        D density hdensity phiAtPoint curvaturePhi operatorData)
      errorScale

/-- Direct Gate 3-to-Gate 4 RSS/Poisson zero and sampled 4D operator-limit
output from quantized microscopic data plus analytic operator-profile data. -/
theorem microscopicGate3QuantizedConvergenceData_rssPoissonError_zero_and_bdg4d_operator_tendsto
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (density : ℕ → ℝ)
    (hdensity : Tendsto density atTop atTop)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorData : BDG4DOperatorProfileData)
    (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0) ∧
      Tendsto
        (fun n => BDG4DOperatorProfileData.mean operatorData (density n))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target operatorData)) := by
  simpa
    [microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DOperatorInterface]
    using
      RecoveredStageBDG4DOperatorInterface.rssPoissonError_zero_and_operator_tendsto
        (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DOperatorInterface
          D density hdensity phiAtPoint curvaturePhi operatorData)
        errorScale

/-- Package quantized Gate 3 data plus matched physical chart certificates into
the matched physical-chart interface.  The matched residual identities are now
the exact remaining physical-chart connection between the microscopic CSpec
residuals and the chart-certificate scalar channels. -/
noncomputable def microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DMatchedPhysicalChartInterface
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (fixedScale : ℝ)
    (scale_eq : ∀ n, (chartCertificate n).scale = fixedScale)
    (countWindow_eq_sum :
      ∀ n, (chartCertificate n).countWindow = ∑ i, countWindow n i)
    (curvatureBias_eq_sum :
      ∀ n, (chartCertificate n).curvatureBias = ∑ i, curvatureBias n i)
    (pairConsistency_eq_spectral_sum :
      ∀ n, (chartCertificate n).pairConsistency =
        ∑ i, spectralLocality n i)
    (density_tendsto_atTop :
      Tendsto (fun n => (chartCertificate n).density) atTop atTop)
    (coord : Y → Fin 4 → ℝ)
    (chartOfCell : ι → chart)
    (sampleEvent : ℕ → ι → X)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorData : BDG4DOperatorProfileData) :
    RecoveredStageBDG4DMatchedPhysicalChartInterface ι X Y chart where
  recovered :=
    microscopicGate3QuantizedConvergenceData_toRecoveredStageExactCSpecSequence
      D
  chartCertificate := chartCertificate
  fixedScale := fixedScale
  scale_eq := scale_eq
  countWindow_eq_sum := countWindow_eq_sum
  curvatureBias_eq_sum := curvatureBias_eq_sum
  pairConsistency_eq_spectral_sum := pairConsistency_eq_spectral_sum
  density_tendsto_atTop := density_tendsto_atTop
  coord := coord
  chartOfCell := chartOfCell
  sampleEvent := sampleEvent
  phiAtPoint := phiAtPoint
  curvaturePhi := curvaturePhi
  operatorData := operatorData

/-- Quantized Gate 3 data plus matched physical chart certificates gives the
Gate 4 chart package: RSS/Poisson zero, sampled 4D operator convergence, and
physical chart-distortion collapse. -/
theorem microscopicGate3QuantizedConvergenceData_matchedPhysicalChart_rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (fixedScale : ℝ)
    (scale_eq : ∀ n, (chartCertificate n).scale = fixedScale)
    (countWindow_eq_sum :
      ∀ n, (chartCertificate n).countWindow = ∑ i, countWindow n i)
    (curvatureBias_eq_sum :
      ∀ n, (chartCertificate n).curvatureBias = ∑ i, curvatureBias n i)
    (pairConsistency_eq_spectral_sum :
      ∀ n, (chartCertificate n).pairConsistency =
        ∑ i, spectralLocality n i)
    (density_tendsto_atTop :
      Tendsto (fun n => (chartCertificate n).density) atTop atTop)
    (coord : Y → Fin 4 → ℝ)
    (chartOfCell : ι → chart)
    (sampleEvent : ℕ → ι → X)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorData : BDG4DOperatorProfileData)
    (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            operatorData ((chartCertificate n).density))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target operatorData)) ∧
      Tendsto (fun n => (chartCertificate n).distortionBound)
        atTop (𝓝 0) := by
  simpa
    [microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DMatchedPhysicalChartInterface,
      microscopicGate3QuantizedConvergenceData_toRecoveredStageExactCSpecSequence]
    using
      RecoveredStageBDG4DMatchedPhysicalChartInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
        (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DMatchedPhysicalChartInterface
          D chartCertificate fixedScale scale_eq
          countWindow_eq_sum curvatureBias_eq_sum
          pairConsistency_eq_spectral_sum density_tendsto_atTop
          coord chartOfCell sampleEvent phiAtPoint curvaturePhi operatorData)
        errorScale

/-- Quantized Gate 3 data plus matched physical chart certificates also gives
the recovered-stage/4D-operator/distortion-collapse Gate 4 chart package. -/
theorem microscopicGate3QuantizedConvergenceData_matchedPhysicalChart_recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (fixedScale : ℝ)
    (scale_eq : ∀ n, (chartCertificate n).scale = fixedScale)
    (countWindow_eq_sum :
      ∀ n, (chartCertificate n).countWindow = ∑ i, countWindow n i)
    (curvatureBias_eq_sum :
      ∀ n, (chartCertificate n).curvatureBias = ∑ i, curvatureBias n i)
    (pairConsistency_eq_spectral_sum :
      ∀ n, (chartCertificate n).pairConsistency =
        ∑ i, spectralLocality n i)
    (density_tendsto_atTop :
      Tendsto (fun n => (chartCertificate n).density) atTop atTop)
    (coord : Y → Fin 4 → ℝ)
    (chartOfCell : ι → chart)
    (sampleEvent : ℕ → ι → X)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorData : BDG4DOperatorProfileData) :
    (∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            operatorData ((chartCertificate n).density))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target operatorData)) ∧
      Tendsto (fun n => (chartCertificate n).distortionBound)
        atTop (𝓝 0) := by
  simpa
    [microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DMatchedPhysicalChartInterface,
      microscopicGate3QuantizedConvergenceData_toRecoveredStageExactCSpecSequence]
    using
      RecoveredStageBDG4DMatchedPhysicalChartInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
        (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DMatchedPhysicalChartInterface
          D chartCertificate fixedScale scale_eq
          countWindow_eq_sum curvatureBias_eq_sum
          pairConsistency_eq_spectral_sum density_tendsto_atTop
          coord chartOfCell sampleEvent phiAtPoint curvaturePhi operatorData)

/-- Package quantized Gate 3 data plus matched physical chart certificates and
a positive affine density schedule into the scheduled-density Gate 4 chart
interface. -/
noncomputable def microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DScheduledDensityInterface
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (fixedScale : ℝ)
    (scale_eq : ∀ n, (chartCertificate n).scale = fixedScale)
    (countWindow_eq_sum :
      ∀ n, (chartCertificate n).countWindow = ∑ i, countWindow n i)
    (curvatureBias_eq_sum :
      ∀ n, (chartCertificate n).curvatureBias = ∑ i, curvatureBias n i)
    (pairConsistency_eq_spectral_sum :
      ∀ n, (chartCertificate n).pairConsistency =
        ∑ i, spectralLocality n i)
    (densityBase densityStep : ℝ)
    (densityStep_pos : 0 < densityStep)
    (density_eq_affine :
      ∀ n, (chartCertificate n).density =
        densityBase + densityStep * (n : ℝ))
    (coord : Y → Fin 4 → ℝ)
    (chartOfCell : ι → chart)
    (sampleEvent : ℕ → ι → X)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorData : BDG4DOperatorProfileData) :
    RecoveredStageBDG4DScheduledDensityInterface ι X Y chart where
  recovered :=
    microscopicGate3QuantizedConvergenceData_toRecoveredStageExactCSpecSequence
      D
  chartCertificate := chartCertificate
  fixedScale := fixedScale
  scale_eq := scale_eq
  countWindow_eq_sum := countWindow_eq_sum
  curvatureBias_eq_sum := curvatureBias_eq_sum
  pairConsistency_eq_spectral_sum := pairConsistency_eq_spectral_sum
  densityBase := densityBase
  densityStep := densityStep
  densityStep_pos := densityStep_pos
  density_eq_affine := density_eq_affine
  coord := coord
  chartOfCell := chartOfCell
  sampleEvent := sampleEvent
  phiAtPoint := phiAtPoint
  curvaturePhi := curvaturePhi
  operatorData := operatorData

/-- Quantized Gate 3 data plus scheduled physical chart certificates gives
RSS/Poisson zero, sampled 4D operator convergence, and chart-distortion
collapse, with density divergence derived from the affine schedule. -/
theorem microscopicGate3QuantizedConvergenceData_scheduledDensity_rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (fixedScale : ℝ)
    (scale_eq : ∀ n, (chartCertificate n).scale = fixedScale)
    (countWindow_eq_sum :
      ∀ n, (chartCertificate n).countWindow = ∑ i, countWindow n i)
    (curvatureBias_eq_sum :
      ∀ n, (chartCertificate n).curvatureBias = ∑ i, curvatureBias n i)
    (pairConsistency_eq_spectral_sum :
      ∀ n, (chartCertificate n).pairConsistency =
        ∑ i, spectralLocality n i)
    (densityBase densityStep : ℝ)
    (densityStep_pos : 0 < densityStep)
    (density_eq_affine :
      ∀ n, (chartCertificate n).density =
        densityBase + densityStep * (n : ℝ))
    (coord : Y → Fin 4 → ℝ)
    (chartOfCell : ι → chart)
    (sampleEvent : ℕ → ι → X)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorData : BDG4DOperatorProfileData)
    (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            operatorData ((chartCertificate n).density))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target operatorData)) ∧
      Tendsto (fun n => (chartCertificate n).distortionBound)
        atTop (𝓝 0) := by
  simpa
    [microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DScheduledDensityInterface,
      microscopicGate3QuantizedConvergenceData_toRecoveredStageExactCSpecSequence]
    using
      RecoveredStageBDG4DScheduledDensityInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
        (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DScheduledDensityInterface
          D chartCertificate fixedScale scale_eq
          countWindow_eq_sum curvatureBias_eq_sum
          pairConsistency_eq_spectral_sum densityBase densityStep
          densityStep_pos density_eq_affine coord chartOfCell sampleEvent
          phiAtPoint curvaturePhi operatorData)
        errorScale

/-- Quantized Gate 3 data plus scheduled physical chart certificates also gives
the recovered-stage/4D-operator/distortion-collapse Gate 4 chart package. -/
theorem microscopicGate3QuantizedConvergenceData_scheduledDensity_recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (fixedScale : ℝ)
    (scale_eq : ∀ n, (chartCertificate n).scale = fixedScale)
    (countWindow_eq_sum :
      ∀ n, (chartCertificate n).countWindow = ∑ i, countWindow n i)
    (curvatureBias_eq_sum :
      ∀ n, (chartCertificate n).curvatureBias = ∑ i, curvatureBias n i)
    (pairConsistency_eq_spectral_sum :
      ∀ n, (chartCertificate n).pairConsistency =
        ∑ i, spectralLocality n i)
    (densityBase densityStep : ℝ)
    (densityStep_pos : 0 < densityStep)
    (density_eq_affine :
      ∀ n, (chartCertificate n).density =
        densityBase + densityStep * (n : ℝ))
    (coord : Y → Fin 4 → ℝ)
    (chartOfCell : ι → chart)
    (sampleEvent : ℕ → ι → X)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorData : BDG4DOperatorProfileData) :
    (∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            operatorData ((chartCertificate n).density))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target operatorData)) ∧
      Tendsto (fun n => (chartCertificate n).distortionBound)
        atTop (𝓝 0) := by
  simpa
    [microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DScheduledDensityInterface,
      microscopicGate3QuantizedConvergenceData_toRecoveredStageExactCSpecSequence]
    using
      RecoveredStageBDG4DScheduledDensityInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
        (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DScheduledDensityInterface
          D chartCertificate fixedScale scale_eq
          countWindow_eq_sum curvatureBias_eq_sum
          pairConsistency_eq_spectral_sum densityBase densityStep
          densityStep_pos density_eq_affine coord chartOfCell sampleEvent
          phiAtPoint curvaturePhi operatorData)

/-- Package quantized Gate 3 data plus scheduled chart certificates and split
operator-profile data into the scheduled-density split-operator interface. -/
noncomputable def microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DScheduledDensitySplitOperatorInterface
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (fixedScale : ℝ)
    (scale_eq : ∀ n, (chartCertificate n).scale = fixedScale)
    (countWindow_eq_sum :
      ∀ n, (chartCertificate n).countWindow = ∑ i, countWindow n i)
    (curvatureBias_eq_sum :
      ∀ n, (chartCertificate n).curvatureBias = ∑ i, curvatureBias n i)
    (pairConsistency_eq_spectral_sum :
      ∀ n, (chartCertificate n).pairConsistency =
        ∑ i, spectralLocality n i)
    (densityBase densityStep : ℝ)
    (densityStep_pos : 0 < densityStep)
    (density_eq_affine :
      ∀ n, (chartCertificate n).density =
        densityBase + densityStep * (n : ℝ))
    (coord : Y → Fin 4 → ℝ)
    (chartOfCell : ι → chart)
    (sampleEvent : ℕ → ι → X)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorSplitData : BDG4DOperatorProfileSplitData) :
    RecoveredStageBDG4DScheduledDensitySplitOperatorInterface ι X Y chart where
  recovered :=
    microscopicGate3QuantizedConvergenceData_toRecoveredStageExactCSpecSequence
      D
  chartCertificate := chartCertificate
  fixedScale := fixedScale
  scale_eq := scale_eq
  countWindow_eq_sum := countWindow_eq_sum
  curvatureBias_eq_sum := curvatureBias_eq_sum
  pairConsistency_eq_spectral_sum := pairConsistency_eq_spectral_sum
  densityBase := densityBase
  densityStep := densityStep
  densityStep_pos := densityStep_pos
  density_eq_affine := density_eq_affine
  coord := coord
  chartOfCell := chartOfCell
  sampleEvent := sampleEvent
  phiAtPoint := phiAtPoint
  curvaturePhi := curvaturePhi
  operatorSplitData := operatorSplitData

/-- Quantized Gate 3 data plus scheduled chart certificates and split operator
data gives RSS/Poisson zero, sampled 4D operator convergence, and
chart-distortion collapse. -/
theorem microscopicGate3QuantizedConvergenceData_scheduledSplitOperator_rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (fixedScale : ℝ)
    (scale_eq : ∀ n, (chartCertificate n).scale = fixedScale)
    (countWindow_eq_sum :
      ∀ n, (chartCertificate n).countWindow = ∑ i, countWindow n i)
    (curvatureBias_eq_sum :
      ∀ n, (chartCertificate n).curvatureBias = ∑ i, curvatureBias n i)
    (pairConsistency_eq_spectral_sum :
      ∀ n, (chartCertificate n).pairConsistency =
        ∑ i, spectralLocality n i)
    (densityBase densityStep : ℝ)
    (densityStep_pos : 0 < densityStep)
    (density_eq_affine :
      ∀ n, (chartCertificate n).density =
        densityBase + densityStep * (n : ℝ))
    (coord : Y → Fin 4 → ℝ)
    (chartOfCell : ι → chart)
    (sampleEvent : ℕ → ι → X)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorSplitData : BDG4DOperatorProfileSplitData)
    (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (countWindow n i) (curvatureBias n i) errorScale = 0) ∧
      Tendsto
        (fun n =>
          BDG4DOperatorProfileData.mean
            operatorSplitData.toProfileData ((chartCertificate n).density))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target operatorSplitData.toProfileData)) ∧
      Tendsto (fun n => (chartCertificate n).distortionBound)
        atTop (𝓝 0) := by
  simpa
    [microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DScheduledDensitySplitOperatorInterface,
      microscopicGate3QuantizedConvergenceData_toRecoveredStageExactCSpecSequence]
    using
      RecoveredStageBDG4DScheduledDensitySplitOperatorInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
        (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DScheduledDensitySplitOperatorInterface
          D chartCertificate fixedScale scale_eq
          countWindow_eq_sum curvatureBias_eq_sum
          pairConsistency_eq_spectral_sum densityBase densityStep
          densityStep_pos density_eq_affine coord chartOfCell sampleEvent
          phiAtPoint curvaturePhi operatorSplitData)
        errorScale

/-- Package quantized Gate 3 data plus scheduled chart certificates and
kernel/profile split data into the strongest scheduled kernel-operator Gate 4
interface. -/
noncomputable def microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DScheduledDensityKernelOperatorInterface
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (fixedScale : ℝ)
    (scale_eq : ∀ n, (chartCertificate n).scale = fixedScale)
    (countWindow_eq_sum :
      ∀ n, (chartCertificate n).countWindow = ∑ i, countWindow n i)
    (curvatureBias_eq_sum :
      ∀ n, (chartCertificate n).curvatureBias = ∑ i, curvatureBias n i)
    (pairConsistency_eq_spectral_sum :
      ∀ n, (chartCertificate n).pairConsistency =
        ∑ i, spectralLocality n i)
    (densityBase densityStep : ℝ)
    (densityStep_pos : 0 < densityStep)
    (density_eq_affine :
      ∀ n, (chartCertificate n).density =
        densityBase + densityStep * (n : ℝ))
    (coord : Y → Fin 4 → ℝ)
    (chartOfCell : ι → chart)
    (sampleEvent : ℕ → ι → X)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorKernelData : BDG4DOperatorProfileKernelSplitData) :
    RecoveredStageBDG4DScheduledDensityKernelOperatorInterface ι X Y chart where
  recovered :=
    microscopicGate3QuantizedConvergenceData_toRecoveredStageExactCSpecSequence
      D
  chartCertificate := chartCertificate
  fixedScale := fixedScale
  scale_eq := scale_eq
  countWindow_eq_sum := countWindow_eq_sum
  curvatureBias_eq_sum := curvatureBias_eq_sum
  pairConsistency_eq_spectral_sum := pairConsistency_eq_spectral_sum
  densityBase := densityBase
  densityStep := densityStep
  densityStep_pos := densityStep_pos
  density_eq_affine := density_eq_affine
  coord := coord
  chartOfCell := chartOfCell
  sampleEvent := sampleEvent
  phiAtPoint := phiAtPoint
  curvaturePhi := curvaturePhi
  operatorKernelData := operatorKernelData

/-- Quantized Gate 3 data plus scheduled physical chart certificates and
kernel/profile split data closes the strongest current Gate 4 scheduled-kernel
operator bridge. -/
theorem microscopicGate3QuantizedConvergenceData_scheduledKernelOperatorBridge_closed
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (fixedScale : ℝ)
    (scale_eq : ∀ n, (chartCertificate n).scale = fixedScale)
    (countWindow_eq_sum :
      ∀ n, (chartCertificate n).countWindow = ∑ i, countWindow n i)
    (curvatureBias_eq_sum :
      ∀ n, (chartCertificate n).curvatureBias = ∑ i, curvatureBias n i)
    (pairConsistency_eq_spectral_sum :
      ∀ n, (chartCertificate n).pairConsistency =
        ∑ i, spectralLocality n i)
    (densityBase densityStep : ℝ)
    (densityStep_pos : 0 < densityStep)
    (density_eq_affine :
      ∀ n, (chartCertificate n).density =
        densityBase + densityStep * (n : ℝ))
    (coord : Y → Fin 4 → ℝ)
    (chartOfCell : ι → chart)
    (sampleEvent : ℕ → ι → X)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorKernelData : BDG4DOperatorProfileKernelSplitData)
    (errorScale : ℝ) :
    Gate4ScheduledKernelOperatorBridgeClosed
      (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DScheduledDensityKernelOperatorInterface
        D chartCertificate fixedScale scale_eq
        countWindow_eq_sum curvatureBias_eq_sum
        pairConsistency_eq_spectral_sum densityBase densityStep
        densityStep_pos density_eq_affine coord chartOfCell sampleEvent
        phiAtPoint curvaturePhi operatorKernelData)
      errorScale := by
  exact
    gate4_scheduledKernelOperatorBridge_closed
      (microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DScheduledDensityKernelOperatorInterface
        D chartCertificate fixedScale scale_eq
        countWindow_eq_sum curvatureBias_eq_sum
        pairConsistency_eq_spectral_sum densityBase densityStep
        densityStep_pos density_eq_affine coord chartOfCell sampleEvent
        phiAtPoint curvaturePhi operatorKernelData)
      errorScale

/-- Direct strongest current Gate 4 output from quantized Gate 3 data plus
scheduled physical chart certificates and kernel/profile split data:
RSS/Poisson zero, sampled 4D operator convergence, physical chart-distortion
collapse, and affine density divergence. -/
theorem microscopicGate3QuantizedConvergenceData_scheduledKernelOperatorBridge_outputs
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    (D : MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap)
    (chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (fixedScale : ℝ)
    (scale_eq : ∀ n, (chartCertificate n).scale = fixedScale)
    (countWindow_eq_sum :
      ∀ n, (chartCertificate n).countWindow = ∑ i, countWindow n i)
    (curvatureBias_eq_sum :
      ∀ n, (chartCertificate n).curvatureBias = ∑ i, curvatureBias n i)
    (pairConsistency_eq_spectral_sum :
      ∀ n, (chartCertificate n).pairConsistency =
        ∑ i, spectralLocality n i)
    (densityBase densityStep : ℝ)
    (densityStep_pos : 0 < densityStep)
    (density_eq_affine :
      ∀ n, (chartCertificate n).density =
        densityBase + densityStep * (n : ℝ))
    (coord : Y → Fin 4 → ℝ)
    (chartOfCell : ι → chart)
    (sampleEvent : ℕ → ι → X)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorKernelData : BDG4DOperatorProfileKernelSplitData)
    (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)) ∧
      (∀ᶠ n in atTop,
        ∀ i,
          rssPoissonError
            (countWindow n i) (curvatureBias n i) errorScale = 0) ∧
        Tendsto
          (fun n =>
            BDG4DOperatorProfileData.mean
              operatorKernelData.toProfileData ((chartCertificate n).density))
          atTop
          (𝓝 (BDG4DOperatorProfileData.target operatorKernelData.toProfileData)) ∧
          Tendsto (fun n => (chartCertificate n).distortionBound)
            atTop (𝓝 0) ∧
            Tendsto (fun n => (chartCertificate n).density) atTop atTop := by
  let I :=
    microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DScheduledDensityKernelOperatorInterface
      D chartCertificate fixedScale scale_eq
      countWindow_eq_sum curvatureBias_eq_sum pairConsistency_eq_spectral_sum
      densityBase densityStep densityStep_pos density_eq_affine coord
      chartOfCell sampleEvent phiAtPoint curvaturePhi operatorKernelData
  have H : Gate4ScheduledKernelOperatorBridgeClosed I errorScale :=
    microscopicGate3QuantizedConvergenceData_scheduledKernelOperatorBridge_closed
      D chartCertificate fixedScale scale_eq
      countWindow_eq_sum curvatureBias_eq_sum pairConsistency_eq_spectral_sum
      densityBase densityStep densityStep_pos density_eq_affine coord
      chartOfCell sampleEvent phiAtPoint curvaturePhi operatorKernelData
      errorScale
  simpa
    [I,
      microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DScheduledDensityKernelOperatorInterface,
      microscopicGate3QuantizedConvergenceData_toRecoveredStageExactCSpecSequence]
    using
      ⟨H.eventualRecoveredStage, H.rssPoissonErrorZero,
        H.chartOperatorLimit, H.chartDistortionTendsToZero,
        H.scheduledDensityTendsToInfinity⟩

/-- Named Gate 4 supplier target over the raw quantized Gate 3 data.

This is the strongest current microscopic-to-Gate-4 input package: quantized
Gate 3 convergence data, physical chart certificates with matched residual
sums, an affine density law, chart/coordinate sampling data, and the active
kernel/profile split supplier.  It deliberately leaves the full
horizon-to-Einstein analytic target separate. -/
structure MicroscopicGate4ScheduledKernelData
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ)
    (scale c step descentRate remainder total : ℕ → ℝ)
    (edge : ℕ → ι → E4)
    (candidate : ℕ → ι → Equiv.Perm Direction)
    (countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ)
    (stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ)
    (chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (fixedScale densityBase densityStep : ℝ)
    (coord : Y → Fin 4 → ℝ)
    (chartOfCell : ι → chart)
    (sampleEvent : ℕ → ι → X)
    (phiAtPoint curvaturePhi : ℝ)
    (operatorKernelData : BDG4DOperatorProfileKernelSplitData)
    (errorScale : ℝ) : Prop where
  gate3 :
    MicroscopicGate3QuantizedConvergenceData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
  scale_eq : ∀ n, (chartCertificate n).scale = fixedScale
  countWindow_eq_sum :
    ∀ n, (chartCertificate n).countWindow = ∑ i, countWindow n i
  curvatureBias_eq_sum :
    ∀ n, (chartCertificate n).curvatureBias = ∑ i, curvatureBias n i
  pairConsistency_eq_spectral_sum :
    ∀ n, (chartCertificate n).pairConsistency =
      ∑ i, spectralLocality n i
  densityStep_pos : 0 < densityStep
  density_eq_affine :
    ∀ n, (chartCertificate n).density =
      densityBase + densityStep * (n : ℝ)

/-- The named Gate 4 scheduled-kernel supplier builds the concrete interface
consumed by the Gate 4 bridge ledger. -/
noncomputable def microscopicGate4ScheduledKernelData_toRecoveredStageBDG4DScheduledDensityKernelOperatorInterface
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    {chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart}
    {fixedScale densityBase densityStep : ℝ}
    {coord : Y → Fin 4 → ℝ}
    {chartOfCell : ι → chart}
    {sampleEvent : ℕ → ι → X}
    {phiAtPoint curvaturePhi : ℝ}
    {operatorKernelData : BDG4DOperatorProfileKernelSplitData}
    {errorScale : ℝ}
    (G : MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale) :
    RecoveredStageBDG4DScheduledDensityKernelOperatorInterface
      ι X Y chart :=
  microscopicGate3QuantizedConvergenceData_toRecoveredStageBDG4DScheduledDensityKernelOperatorInterface
    G.gate3 chartCertificate fixedScale G.scale_eq
    G.countWindow_eq_sum G.curvatureBias_eq_sum
    G.pairConsistency_eq_spectral_sum densityBase densityStep
    G.densityStep_pos G.density_eq_affine coord chartOfCell sampleEvent
    phiAtPoint curvaturePhi operatorKernelData

/-- The named Gate 4 scheduled-kernel supplier closes the strongest current
Gate 4 scheduled-kernel/operator bridge. -/
theorem microscopicGate4ScheduledKernelData_bridge_closed
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    {chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart}
    {fixedScale densityBase densityStep : ℝ}
    {coord : Y → Fin 4 → ℝ}
    {chartOfCell : ι → chart}
    {sampleEvent : ℕ → ι → X}
    {phiAtPoint curvaturePhi : ℝ}
    {operatorKernelData : BDG4DOperatorProfileKernelSplitData}
    {errorScale : ℝ}
    (G : MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale) :
    Gate4ScheduledKernelOperatorBridgeClosed
      (microscopicGate4ScheduledKernelData_toRecoveredStageBDG4DScheduledDensityKernelOperatorInterface
        G)
      errorScale := by
  simpa
    [microscopicGate4ScheduledKernelData_toRecoveredStageBDG4DScheduledDensityKernelOperatorInterface]
    using
      microscopicGate3QuantizedConvergenceData_scheduledKernelOperatorBridge_closed
        G.gate3 chartCertificate fixedScale G.scale_eq
        G.countWindow_eq_sum G.curvatureBias_eq_sum
        G.pairConsistency_eq_spectral_sum densityBase densityStep
        G.densityStep_pos G.density_eq_affine coord chartOfCell sampleEvent
        phiAtPoint curvaturePhi operatorKernelData errorScale

/-- Direct output projections from the named Gate 4 scheduled-kernel supplier:
eventual recovered stages, zero RSS/Poisson horizon error, sampled 4D operator
convergence, chart-distortion collapse, and density divergence. -/
theorem microscopicGate4ScheduledKernelData_outputs
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    {chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart}
    {fixedScale densityBase densityStep : ℝ}
    {coord : Y → Fin 4 → ℝ}
    {chartOfCell : ι → chart}
    {sampleEvent : ℕ → ι → X}
    {phiAtPoint curvaturePhi : ℝ}
    {operatorKernelData : BDG4DOperatorProfileKernelSplitData}
    {errorScale : ℝ}
    (G : MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale) :
    (∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)) ∧
      (∀ᶠ n in atTop,
        ∀ i,
          rssPoissonError
            (countWindow n i) (curvatureBias n i) errorScale = 0) ∧
        Tendsto
          (fun n =>
            BDG4DOperatorProfileData.mean
              operatorKernelData.toProfileData ((chartCertificate n).density))
          atTop
          (𝓝 (BDG4DOperatorProfileData.target operatorKernelData.toProfileData)) ∧
          Tendsto (fun n => (chartCertificate n).distortionBound)
            atTop (𝓝 0) ∧
            Tendsto (fun n => (chartCertificate n).density) atTop atTop := by
  exact
    microscopicGate3QuantizedConvergenceData_scheduledKernelOperatorBridge_outputs
      G.gate3 chartCertificate fixedScale G.scale_eq
      G.countWindow_eq_sum G.curvatureBias_eq_sum
      G.pairConsistency_eq_spectral_sum densityBase densityStep
      G.densityStep_pos G.density_eq_affine coord chartOfCell sampleEvent
      phiAtPoint curvaturePhi operatorKernelData errorScale

/-- Convert the named scheduled-kernel supplier into the abstract Gate 4
analytic target record, leaving exactly the still-external horizon estimator,
scheduled-density physics, kernel-profile certificate, and null-balance
dynamics as named assumptions. -/
noncomputable def microscopicGate4ScheduledKernelData_toGate4HorizonEinsteinAnalyticTargets
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    {chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart}
    {fixedScale densityBase densityStep : ℝ}
    {coord : Y → Fin 4 → ℝ}
    {chartOfCell : ι → chart}
    {sampleEvent : ℕ → ι → X}
    {phiAtPoint curvaturePhi : ℝ}
    {operatorKernelData : BDG4DOperatorProfileKernelSplitData}
    {errorScale : ℝ}
    (G : MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale)
    (horizonEstimatorConvergence physicalScheduledDensity
      bdgKernelProfileCertificate nullBalanceFromDynamics : Prop) :
    Gate4HorizonEinsteinAnalyticTargets where
  horizonEstimatorConvergence := horizonEstimatorConvergence
  physicalScheduledDensity := physicalScheduledDensity
  bdgKernelProfileCertificate := bdgKernelProfileCertificate
  nullBalanceFromDynamics := nullBalanceFromDynamics
  recoveredBDGInterfaceSupplied :=
    Gate4ScheduledKernelOperatorBridgeClosed
      (microscopicGate4ScheduledKernelData_toRecoveredStageBDG4DScheduledDensityKernelOperatorInterface
        G)
      errorScale

/-- Closing the abstract Gate 4 analytic target now reduces to the four
explicit analytic/physical assumptions plus the named scheduled-kernel
microscopic supplier. -/
theorem microscopicGate4ScheduledKernelData_horizonEinsteinAnalytic_closed
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    {chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart}
    {fixedScale densityBase densityStep : ℝ}
    {coord : Y → Fin 4 → ℝ}
    {chartOfCell : ι → chart}
    {sampleEvent : ℕ → ι → X}
    {phiAtPoint curvaturePhi : ℝ}
    {operatorKernelData : BDG4DOperatorProfileKernelSplitData}
    {errorScale : ℝ}
    (G : MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale)
    {horizonEstimatorConvergence physicalScheduledDensity
      bdgKernelProfileCertificate nullBalanceFromDynamics : Prop}
    (hhorizon : horizonEstimatorConvergence)
    (hscheduled : physicalScheduledDensity)
    (hkernel : bdgKernelProfileCertificate)
    (hnull : nullBalanceFromDynamics) :
    Gate4HorizonEinsteinAnalyticClosed
      (microscopicGate4ScheduledKernelData_toGate4HorizonEinsteinAnalyticTargets
        G horizonEstimatorConvergence physicalScheduledDensity
        bdgKernelProfileCertificate nullBalanceFromDynamics) := by
  exact
    ⟨hhorizon, hscheduled, hkernel, hnull,
      microscopicGate4ScheduledKernelData_bridge_closed G⟩

/-- The named Gate 4 scheduled-kernel supplier also closes Gate 2's
finite-spectrum semantic zero-set target, because it contains the named
quantized Gate 3 supplier. -/
theorem microscopicGate4ScheduledKernelData_gate2HauptvermutungSemantic_closed
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    {chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart}
    {fixedScale densityBase densityStep : ℝ}
    {coord : Y → Fin 4 → ℝ}
    {chartOfCell : ι → chart}
    {sampleEvent : ℕ → ι → X}
    {phiAtPoint curvaturePhi : ℝ}
    {operatorKernelData : BDG4DOperatorProfileKernelSplitData}
    {errorScale : ℝ}
    (G : MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale) :
    Gate2HauptvermutungSemanticClosed
      (gate2QuantizedResidualSemanticTargets
        countWindow curvatureBias spectralLocality
        countQuantum curvatureQuantum spectralQuantum) := by
  exact
    microscopicGate3QuantizedConvergenceData_gate2HauptvermutungSemantic_closed
      G.gate3

end UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3Supplier
