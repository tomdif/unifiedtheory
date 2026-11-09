/- Exact ordinary two-point hierarchy dictionary for a fixed real Schwartz test. -/
import UnifiedTheory.Clay.YangMills.WilsonLogarithmicMomentObstruction
import UnifiedTheory.Clay.YangMills.WilsonTensorProduct
import UnifiedTheory.Clay.YangMills.TunedRenormalizedLimit
import UnifiedTheory.Clay.YangMills.WilsonEnergyDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPhysicalSecondMoment
noncomputable section
open MeasureTheory Filter LocalFields ContinuumControl PeriodicLattice4
open WilsonSingleLinkStaples
open scoped NNReal Topology

local instance complexRealNormedSpace : NormedSpace ℝ ℂ :=
  InnerProductSpace.toNormedSpace

def oneIndex : (Fin 1 × Fin 4) ≃ Fin 4 := Equiv.uniqueProd (Fin 4) (Fin 1)

def onePoint : Configuration 1 ≃L[ℝ] Spacetime :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ oneIndex).toContinuousLinearEquiv

@[simp] theorem onePoint_apply (x : Configuration 1) :
    onePoint x = PeriodicCellSampling.point 1 0 x := rfl

theorem onePoint_preserves_volume : MeasurePreserving onePoint := by
  have hp := (PiLp.volume_preserving_toLp (Fin 4)).comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ) oneIndex).comp
      (PiLp.volume_preserving_ofLp (Fin 1 × Fin 4)))
  convert hp using 1

def oneTest (f : TestFunction) : CorrelationTest 1 :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ onePoint f

@[simp] theorem oneTest_apply (f : TestFunction) (x : Configuration 1) :
    oneTest f x = f (onePoint x) := rfl

theorem oneTest_integral (f : TestFunction) : (∫ x, oneTest f x) = ∫ x, f x :=
  onePoint_preserves_volume.integral_comp onePoint.toHomeomorph.measurableEmbedding f

def squareTest (f : TestFunction) : CorrelationTest 2 :=
  SchwartzConfigurationTensor.tensor 1 1 (oneTest f) (oneTest f)

variable (n : ℕ) [NeZero n]

theorem one_observable_integral (a : ℝ) (plane : Plane) (χ : Q → ℂ)
    (f : TestFunction) (U : RegulatedGauge.Configuration (Vertex n) Q) :
    WilsonSmearedObservable.observable Q n a plane χ 1 (oneTest f) U =
      ∫ x, WilsonMomentBounds.loopObservable (Vertex n) Q χ
        (loops n (PeriodicCellSampling.sample n a plane x)) U * f x := by
  rw [WilsonSmearedObservable.observable_integral]
  have hp := onePoint_preserves_volume.integral_comp
    onePoint.toHomeomorph.measurableEmbedding
      (fun x => WilsonMomentBounds.loopObservable (Vertex n) Q χ
        (loops n (PeriodicCellSampling.sample n a plane x)) U * f x)
  convert hp using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [WilsonSmearedObservable.word, Fin.prod_univ_one,
    PeriodicCellSampling.sampleConfiguration, oneTest_apply, onePoint_apply])

theorem coefficient_real (a : ℝ) (plane : Plane) (f : TestFunction)
    (hf : ∀ x, (f x).im = 0) (p : PlaquetteIndex n) :
    FiniteCellSmearing.coefficient volume (PeriodicCellSampling.sample n a plane) p f =
      (WilsonPhysicalCellWeights.weight n a plane f p : ℂ) := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    have hi := FiniteCellSmearing.cellFunction_integrable volume
      (PeriodicCellSampling.sample n a plane)
      (PeriodicCellSampling.sample_measurable n a plane) p f f.integrable
    let L : ℂ →L[ℝ] ℝ :=
      { toFun := Complex.im
        map_add' := Complex.add_im
        map_smul' := by intro r z; simp
        cont := Complex.continuous_im }
    have hh := L.integral_comp_comm hi
    have hz (x : Spacetime) :
        (FiniteCellSmearing.cellFunction (PeriodicCellSampling.sample n a plane) p f x).im = 0 := by
      unfold FiniteCellSmearing.cellFunction
      split_ifs
      · exact hf x
      · rfl
    change (∫ x, (FiniteCellSmearing.cellFunction
      (PeriodicCellSampling.sample n a plane) p f x).im) = _ at hh
    simp only [hz, integral_zero] at hh
    exact hh.symm

theorem one_real_observable (a : ℝ) (plane : Plane) (χ : Q → ℂ)
    (f : TestFunction) (hf : ∀ x, (f x).im = 0) (hI : (∫ x, f x) = 1)
    (U : RegulatedGauge.Configuration (Vertex n) Q) :
    WilsonSmearedObservable.observable Q n a plane
      (CellReflectionCovariance.realPartCharacter Q χ) 1 (oneTest f) U =
      ((2 - WilsonBlockIntegration.source n Q χ 2
        (WilsonPhysicalCellWeights.weight n a plane f) U : ℝ) : ℂ) := by
  rw [one_observable_integral, FiniteCellSmearing.integral_decomposition volume _
    (PeriodicCellSampling.sample_measurable n a plane)
      (fun p => WilsonMomentBounds.loopObservable (Vertex n) Q
        (CellReflectionCovariance.realPartCharacter Q χ) (loops n p) U) f f.integrable]
  simp_rw [coefficient_real n a plane f hf]
  have hw := WilsonPhysicalCellWeights.weight_sum n a plane f
  rw [hI] at hw
  simp only [Complex.one_re] at hw
  simp only [WilsonMomentBounds.loopObservable, RegulatedGauge.wilson,
    CellReflectionCovariance.realPartCharacter]
  unfold WilsonBlockIntegration.source WilsonIndependentBlocks.plaquetteTerm
  push_cast
  simp only [WilsonMomentBounds.loopObservable, RegulatedGauge.wilson]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hwc := congrArg Complex.ofReal hw
  simp only [Complex.ofReal_sum, Complex.ofReal_one] at hwc
  rw [hwc]
  simp only [mul_comm]
  ring

/-- The sign converts the trace convention to the positive plaquette-defect source. -/
theorem one_affine_observable (a : ℝ) (plane : Plane) (χ : Q → ℂ)
    (f : TestFunction) (hf : ∀ x, (f x).im = 0) (hI : (∫ x, f x) = 1)
    (center scale : ℝ) (U : RegulatedGauge.Configuration (Vertex n) Q) :
    WilsonSmearedObservable.observable Q n a plane
      (CellReflectionCovariance.realPartCharacter Q
        (AffineWilsonSmearing.affineCharacter χ center scale)) 1 (oneTest f) U =
      (-(scale * WilsonBlockIntegration.source n Q χ 2
        (WilsonPhysicalCellWeights.weight n a plane f) U - scale * (2-center)) : ℝ) := by
  rw [RenormalizedWilsonHierarchy.realPart_affine,
    AffineWilsonSmearing.affine_smearing, one_real_observable n a plane χ f hf hI,
    oneTest_integral, hI]
  push_cast
  ring

/-- Exact ordinary tensor moment, with an arbitrary deterministic identity subtraction. -/
theorem hierarchy_square (a : ℝ) (plane : Plane) (f : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hI : (∫ x, f x) = 1) (center scale β : ℝ)
    (B : ℝ≥0)
    (hB : ∀ g, ‖AffineWilsonSmearing.affineCharacter character center scale g‖ ≤ B) :
    (RenormalizedWilsonHierarchy.realHierarchy Q n a plane
      (AffineWilsonSmearing.affineCharacter character center scale) character
      character_continuous B hB β 2).correlation 2 (squareTest f) =
      ((∫ U, (scale * WilsonBlockIntegration.source n Q character 2
        (WilsonPhysicalCellWeights.weight n a plane f) U - scale*(2-center))^2
          ∂wilsonLaw n Q character β 2 : ℝ) : ℂ) := by
  unfold RenormalizedWilsonHierarchy.realHierarchy
  rw [← RenormalizedWilsonHierarchy.expectation_eq_hierarchy Q n a plane _ character
    (WilsonReflectedTensor.realPart_continuous Q _
      (RenormalizedWilsonHierarchy.affine_continuous Q character
        character_continuous center scale))]
  change (∫ U, WilsonSmearedObservable.observable Q n a plane
    (CellReflectionCovariance.realPartCharacter Q
      (AffineWilsonSmearing.affineCharacter character center scale)) (1+1)
      (SchwartzConfigurationTensor.tensor 1 1 (oneTest f) (oneTest f)) U
    ∂wilsonLaw n Q character β 2) = _
  simp_rw [← WilsonTensorProduct.observable_mul, one_affine_observable n a plane character f hf hI]
  simp only [← pow_two, Complex.ofReal_neg, neg_sq, ← Complex.ofReal_pow]
  exact integral_complex_ofReal

omit [NeZero n] in
/-- Binding to the literal sequence used by both existing coupling-selection theorems. -/
theorem proposedSequence_square (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (a : ℕ → ℝ) (plane : Plane) (center : ℕ → ℝ → ℝ) (beta : ℕ → ℝ)
    (f : TestFunction) (hf : ∀ x, (f x).im = 0) (hI : (∫ x, f x) = 1) (k : ℕ) :
    (TunedRenormalizedLimit.proposedSequence (Fin 2) Q period a plane
      WilsonEnergyDensity.representation WilsonEnergyDensity.representation_continuous
      center beta k).correlation 2 (squareTest f) =
      ((∫ U, (((a k)^4)⁻¹ * WilsonBlockIntegration.source (2 * period k) Q character 2
        (WilsonPhysicalCellWeights.weight (2 * period k) (a k) plane f) U -
          ((a k)^4)⁻¹ * (2-center k (beta k)))^2
        ∂wilsonLaw (2 * period k) Q character (beta k) 2 : ℝ) : ℂ) := by
  unfold TunedRenormalizedLimit.proposedSequence
    RenormalizedWilsonUltrafilter.affineSequence RenormalizedOSWitness.sequence
  exact hierarchy_square (2 * period k) (a k) plane f hf hI
    (center k (beta k)) ((a k)^4)⁻¹ (beta k) _ _

local instance doubledPeriodFact (period : ℕ → ℕ) [∀ k, NeZero (period k)] (k : ℕ) :
    Fact (1 < 2 * period k) := ⟨by
  have h := Nat.pos_of_ne_zero (NeZero.ne (period k))
  omega⟩

omit [NeZero n] in
/-- The exact second moment of the fixed witness is a literal existing hierarchy evaluation. -/
theorem proposedSequence_witness_moment (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (a : ℕ → ℝ) (plane : Plane) (center : ℕ → ℝ → ℝ) (beta : ℕ → ℝ) (k : ℕ) :
    (TunedRenormalizedLimit.proposedSequence (Fin 2) Q period a plane
      WilsonEnergyDensity.representation WilsonEnergyDensity.representation_continuous
      center beta k).correlation 2 (squareTest WilsonCellWeightLower.witnessTest) =
      (WilsonLogarithmicMomentObstruction.moment (fun j => 2 * period j) a beta
        (fun j => ((a j)^4)⁻¹ * (2-center j (beta j))) plane k : ℂ) :=
  proposedSequence_square period a plane center beta WilsonCellWeightLower.witnessTest
    WilsonCellWeightLower.witnessTest_real WilsonCellWeightLower.witnessTest_integral k

omit [NeZero n] in
/-- No ordinary full-hierarchy bound survives this logarithmic regime, at any volume.
This is not a statement about separated reflected tensors or contact-renormalized moments. -/
theorem proposed_norm_tendsto (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (a beta : ℕ → ℝ) (plane : Plane) (center : ℕ → ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (ha : ∀ᶠ k in atTop, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hbeta : Tendsto beta atTop atTop)
    (hupper : ∀ᶠ k in atTop, beta k ≤ b * Real.log (a k)⁻¹) :
    Tendsto (fun k => ‖(TunedRenormalizedLimit.proposedSequence (Fin 2) Q period a plane
      WilsonEnergyDensity.representation WilsonEnergyDensity.representation_continuous
      center beta k).correlation 2 (squareTest WilsonCellWeightLower.witnessTest)‖)
      atTop atTop := by
  have h := WilsonLogarithmicMomentObstruction.moment_tendsto (fun j => 2 * period j)
    a beta (fun j => ((a j)^4)⁻¹ * (2-center j (beta j))) plane
    (fun j => dvd_mul_right 2 (period j)) b hb ha ha0 hbeta hupper
  have he (k : ℕ) :
      ‖(TunedRenormalizedLimit.proposedSequence (Fin 2) Q period a plane
        WilsonEnergyDensity.representation WilsonEnergyDensity.representation_continuous
        center beta k).correlation 2 (squareTest WilsonCellWeightLower.witnessTest)‖ =
      WilsonLogarithmicMomentObstruction.moment (fun j => 2 * period j) a beta
        (fun j => ((a j)^4)⁻¹ * (2-center j (beta j))) plane k := by
    rw [proposedSequence_witness_moment, Complex.norm_real, Real.norm_eq_abs]
    apply abs_of_nonneg
    exact integral_nonneg (fun _ => sq_nonneg _)
  simpa only [he] using h

omit [NeZero n] in
/-- The all-order common-seminorm premise fails already at order two for the
actual identity-subtracted sequence, even without requiring seminorm continuity. -/
theorem no_common_second_seminorm (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (a beta : ℕ → ℝ) (plane : Plane) (center : ℕ → ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (ha : ∀ᶠ k in atTop, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hbeta : Tendsto beta atTop atTop)
    (hupper : ∀ᶠ k in atTop, beta k ≤ b * Real.log (a k)⁻¹) :
    ¬ ∃ p : Seminorm ℂ (CorrelationTest 2), ∀ k (g : CorrelationTest 2),
      ‖(TunedRenormalizedLimit.proposedSequence (Fin 2) Q period a plane
        WilsonEnergyDensity.representation WilsonEnergyDensity.representation_continuous
        center beta k).correlation 2 g‖ ≤ p g := by
  rintro ⟨p, hp⟩
  have h := (proposed_norm_tendsto period a beta plane center b hb ha ha0
    hbeta hupper).eventually_gt_atTop (p (squareTest WilsonCellWeightLower.witnessTest))
  obtain ⟨k, hk⟩ := h.exists
  exact (not_lt_of_ge (hp k (squareTest WilsonCellWeightLower.witnessTest))) hk

end
end UnifiedTheory.Clay.YangMills.WilsonPhysicalSecondMoment
