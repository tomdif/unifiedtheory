/-
Quantitative covariance loss under actual one-link Wilson elimination.
The original-minus-retained connected covariance is exactly the Gram matrix
of discarded fluctuations. The previously proved annealed variance supplies
an explicit loss budget. Finite-family bounds use the combined plaquette
coefficients, preserving all cross terms and coefficient cancellation.

The retained probability is the actual interacting marginal. No positive
continuum witness, next-step loss bound, or repeated-elimination contraction
is assumed or asserted.
-/
import UnifiedTheory.Clay.YangMills.SU2AnnealedVariance
import UnifiedTheory.Clay.YangMills.SU2WilsonMarginalTransport
import UnifiedTheory.Clay.YangMills.GibbsCrossCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2RetainedCovariance
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples SU2HaarTilt SU2WilsonConditionalSource
open SU2WilsonSourceApproximation SU2WilsonMarginalTransport
open GibbsMarginalTower GibbsCrossCovariance

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The actual original plaquette source. -/
def source (f : PlaquetteIndex n → ℝ) : Configuration (Vertex n) Q → ℝ :=
  WilsonBlockIntegration.source n Q character 2 f

/-- The fluctuation actually removed by one-link conditional integration. -/
def noise (x : Vertex n) (μ : Fin 4) (β : ℝ) (f : PlaquetteIndex n → ℝ)
    (U : Configuration (Vertex n) Q) : ℝ :=
  source n f U - conditionalSource n x μ β f (exteriorProjection n x μ U)

/-- Connected covariance lost between the original Wilson law and its true marginal. -/
def defect (x : Vertex n) (μ : Fin 4) (β : ℝ) (f g : PlaquetteIndex n → ℝ) : ℝ :=
  covariance (wilsonLaw n Q character β 2) (source n f) (source n g) -
    covariance (retainedLaw n x μ β) (conditionalSource n x μ β f)
      (conditionalSource n x μ β g)

/-- The fully explicit one-link loss budget, retaining coefficient variation. -/
def budget (x : Vertex n) (μ : Fin 4) (β c r₀ : ℝ) (f : PlaquetteIndex n → ℝ) : ℝ :=
  15 * c ^ 2 / (2 * β ^ 2) +
    (12 / (β * r₀) + 144 * WilsonEnergyDensity.energyEnvelope β / (6 - r₀)) *
      (SU2AnnealedVariance.weightVariation n x μ f c) ^ 2

omit [Fact (1 < n)] in
theorem source_continuous (f : PlaquetteIndex n → ℝ) : Continuous (source n f) :=
  WilsonBlockIntegration.source_continuous n Q character character_continuous 2 f

omit [Fact (1 < n)] in
theorem noise_continuous (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) : Continuous (noise n x μ β f) :=
  (source_continuous n f).sub
    ((conditionalSource_continuous n x μ β f).comp (exteriorProjection_continuous n x μ))

omit [Fact (1 < n)] in
theorem integral_coordinates (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (H : Configuration (Vertex n) Q → ℝ) :
    (∫ U, H U ∂wilsonLaw n Q character β 2) =
      ∫ z, H (SingleCoordinateProduct.assemble (selectedLink n x μ) z)
        ∂CompactGibbsContinuity.law ((exteriorMeasure n Q x μ).prod haar)
          (splitAction n x μ β) := by
  have h := (wilson_coordinates_preserving n x μ β).integral_comp'
    (fun z => H (SingleCoordinateProduct.assemble (selectedLink n x μ) z))
  simpa only [MeasurableEquiv.apply_symm_apply] using h

omit [Fact (1 < n)] in
theorem noise_assemble (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) (z : Exterior n Q x μ × Q) :
    noise n x μ β f (SingleCoordinateProduct.assemble (selectedLink n x μ) z) =
      GibbsCrossCovariance.removed haar (splitAction n x μ β) (splitSource n x μ f) z := by
  simp only [noise, exteriorProjection_assemble]
  rfl

omit [Fact (1 < n)] in
theorem covariance_coordinates (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f g : PlaquetteIndex n → ℝ) :
    covariance (wilsonLaw n Q character β 2) (source n f) (source n g) =
      covariance (CompactGibbsContinuity.law ((exteriorMeasure n Q x μ).prod haar)
        (splitAction n x μ β)) (splitSource n x μ f) (splitSource n x μ g) := by
  unfold covariance
  rw [integral_coordinates n x μ β, integral_coordinates n x μ β,
    integral_coordinates n x μ β]
  rfl

omit [Fact (1 < n)] in
theorem defect_eq_conditional (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f g : PlaquetteIndex n → ℝ) :
    defect n x μ β f g =
      ∫ r, conditionalCovariance haar (splitAction n x μ β)
        (splitSource n x μ f) (splitSource n x μ g) r ∂retainedLaw n x μ β := by
  have h := total_covariance (exteriorMeasure n Q x μ) haar (splitAction n x μ β)
    (splitSource n x μ f) (splitSource n x μ g) (splitAction_continuous n x μ β)
    (splitSource_continuous n x μ f) (splitSource_continuous n x μ g)
  unfold defect
  rw [covariance_coordinates n x μ β f g]
  change covariance (CompactGibbsContinuity.law ((exteriorMeasure n Q x μ).prod haar)
    (splitAction n x μ β)) (splitSource n x μ f) (splitSource n x μ g) =
      (∫ r, conditionalCovariance haar (splitAction n x μ β)
        (splitSource n x μ f) (splitSource n x μ g) r ∂retainedLaw n x μ β) +
      covariance (retainedLaw n x μ β) (conditionalSource n x μ β f)
        (conditionalSource n x μ β g) at h
  linarith

omit [Fact (1 < n)] in
/-- The full covariance defect is the Gram matrix of actual discarded fluctuations. -/
theorem defect_eq_noise_gram (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f g : PlaquetteIndex n → ℝ) :
    defect n x μ β f g =
      ∫ U, noise n x μ β f U * noise n x μ β g U ∂wilsonLaw n Q character β 2 := by
  rw [defect_eq_conditional, integral_coordinates n x μ β]
  simp only [noise_assemble]
  have h := response_expectation (exteriorMeasure n Q x μ) haar (splitAction n x μ β)
    (fun z => removed haar (splitAction n x μ β) (splitSource n x μ f) z *
      removed haar (splitAction n x μ β) (splitSource n x μ g) z)
    (splitAction_continuous n x μ β)
    ((GibbsCrossCovariance.removed_continuous haar _ _ (splitAction_continuous n x μ β)
      (splitSource_continuous n x μ f)).mul
      (GibbsCrossCovariance.removed_continuous haar _ _ (splitAction_continuous n x μ β)
        (splitSource_continuous n x μ g)))
  simp_rw [conditional_removed_product haar _ _ _ (splitAction_continuous n x μ β)
    (splitSource_continuous n x μ f) (splitSource_continuous n x μ g)] at h
  exact h

omit [Fact (1 < n)] in
theorem defect_self_eq_annealed (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (f : PlaquetteIndex n → ℝ) :
    defect n x μ β f f =
      ∫ U, SU2AnnealedVariance.originalVariance n x μ β f U
        ∂wilsonLaw n Q character β 2 := by
  rw [defect_eq_conditional]
  have he (r : Exterior n Q x μ) :
      conditionalCovariance haar (splitAction n x μ β) (splitSource n x μ f)
        (splitSource n x μ f) r = SU2AnnealedVariance.fiberVariance n x μ β f r := by
    rw [SU2AnnealedVariance.fiberVariance_eq_moments]
    unfold conditionalCovariance conditionalSource
    simp only [← pow_two]
  simp_rw [he]
  exact retained_integral_eq_wilson n x μ β _
    (SU2AnnealedVariance.fiberVariance_continuous n x μ β f)

/-- The actual loss is nonnegative and has a proved finite-cutoff budget. -/
theorem defect_self_bounds (x : Vertex n) (μ : Fin 4) (β c r₀ : ℝ)
    (f : PlaquetteIndex n → ℝ) (hβ : 0 < β) (hr₀ : 0 < r₀) (hr₆ : r₀ < 6) :
    0 ≤ defect n x μ β f f ∧ defect n x μ β f f ≤ budget n x μ β c r₀ f := by
  rw [defect_self_eq_annealed]
  constructor
  · exact integral_nonneg (SU2AnnealedVariance.originalVariance_nonneg n x μ β f)
  · exact SU2AnnealedVariance.annealed_variance_explicit n x μ β c r₀ f hβ hr₀ hr₆

/-- An explicit lower bound for the true retained covariance relative to the original signal. -/
theorem retained_variance_bounds (x : Vertex n) (μ : Fin 4) (β c r₀ : ℝ)
    (f : PlaquetteIndex n → ℝ) (hβ : 0 < β) (hr₀ : 0 < r₀) (hr₆ : r₀ < 6) :
    covariance (wilsonLaw n Q character β 2) (source n f) (source n f) -
      budget n x μ β c r₀ f ≤
        covariance (retainedLaw n x μ β) (conditionalSource n x μ β f)
          (conditionalSource n x μ β f) ∧
    covariance (retainedLaw n x μ β) (conditionalSource n x μ β f)
      (conditionalSource n x μ β f) ≤
        covariance (wilsonLaw n Q character β 2) (source n f) (source n f) := by
  have h := defect_self_bounds n x μ β c r₀ f hβ hr₀ hr₆
  unfold defect at h
  constructor <;> linarith


section FiniteSources
variable {I : Type*} [Fintype I]

/-- A finite linear combination retains all cross terms in its actual plaquette weights. -/
def combine (a : I → ℝ) (f : I → PlaquetteIndex n → ℝ) (p : PlaquetteIndex n) : ℝ :=
  ∑ i, a i * f i p

omit [Fact (1 < n)] in
theorem source_combine (a : I → ℝ) (f : I → PlaquetteIndex n → ℝ)
    (U : Configuration (Vertex n) Q) :
    source n (combine n a f) U = ∑ i, a i * source n (f i) U := by
  unfold source WilsonBlockIntegration.source combine
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

omit [Fact (1 < n)] in
theorem conditionalSource_combine (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (a : I → ℝ) (f : I → PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) :
    conditionalSource n x μ β (combine n a f) r =
      ∑ i, a i * conditionalSource n x μ β (f i) r := by
  letI := conditionalLaw_probability n x μ β r
  rw [conditionalSource_eq_integral]
  have he (q : Q) : splitSource n x μ (combine n a f) (r, q) =
      ∑ i, a i * splitSource n x μ (f i) (r, q) :=
    source_combine n a f (SingleCoordinateProduct.assemble (selectedLink n x μ) (r, q))
  simp_rw [he]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul, ← conditionalSource_eq_integral]
  · intro i _
    exact Continuous.integrable_of_hasCompactSupport
      ((continuous_const.mul (splitSource_continuous n x μ (f i))).comp
        (continuous_const.prodMk continuous_id)) (HasCompactSupport.of_compactSpace _)

omit [Fact (1 < n)] in
theorem noise_combine (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (a : I → ℝ) (f : I → PlaquetteIndex n → ℝ) (U : Configuration (Vertex n) Q) :
    noise n x μ β (combine n a f) U = ∑ i, a i * noise n x μ β (f i) U := by
  unfold noise
  rw [source_combine, conditionalSource_combine, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fact (1 < n)] in
/-- The complete defect matrix is the Gram form of the combined actual discarded source. -/
theorem quadratic_defect_identity (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (a : I → ℝ) (f : I → PlaquetteIndex n → ℝ) :
    (∑ i, ∑ j, a i * a j * defect n x μ β (f i) (f j)) =
      defect n x μ β (combine n a f) (combine n a f) := by
  let ν := wilsonLaw n Q character β 2
  letI : IsProbabilityMeasure ν := wilsonLaw_probability n Q character character_continuous β 2
  have hi (i j : I) : Integrable (fun U =>
      (a i * a j) * (noise n x μ β (f i) U * noise n x μ β (f j) U)) ν :=
    Continuous.integrable_of_hasCompactSupport
      (continuous_const.mul ((noise_continuous n x μ β (f i)).mul
        (noise_continuous n x μ β (f j)))) (HasCompactSupport.of_compactSpace _)
  have he : (∫ U, ∑ i, ∑ j,
      (a i * a j) * (noise n x μ β (f i) U * noise n x μ β (f j) U) ∂ν) =
      ∑ i, ∑ j, a i * a j *
        (∫ U, noise n x μ β (f i) U * noise n x μ β (f j) U ∂ν) := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum]
      · simp_rw [integral_const_mul]
      · intro j _
        exact hi i j
    · intro i _
      exact integrable_finset_sum _ (fun j _ => hi i j)
  have hp (U : Configuration (Vertex n) Q) :
      (∑ i, ∑ j, (a i * a j) *
        (noise n x μ β (f i) U * noise n x μ β (f j) U)) =
      (∑ i, a i * noise n x μ β (f i) U) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [defect_eq_noise_gram]
  change (∑ i, ∑ j, a i * a j *
    (∫ U, noise n x μ β (f i) U * noise n x μ β (f j) U ∂ν)) = _
  rw [← he]
  apply integral_congr_ae
  filter_upwards with U
  rw [hp, noise_combine]
  ring

omit [Fact (1 < n)] in
theorem quadratic_defect_nonneg (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (a : I → ℝ) (f : I → PlaquetteIndex n → ℝ) :
    0 ≤ ∑ i, ∑ j, a i * a j * defect n x μ β (f i) (f j) := by
  rw [quadratic_defect_identity, defect_eq_noise_gram]
  exact integral_nonneg (fun _ => mul_self_nonneg _)

/-- The matrix loss budget uses the variation of combined coefficients, including cancellation. -/
theorem quadratic_defect_bound (x : Vertex n) (μ : Fin 4) (β c r₀ : ℝ)
    (a : I → ℝ) (f : I → PlaquetteIndex n → ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hr₆ : r₀ < 6) :
    (∑ i, ∑ j, a i * a j * defect n x μ β (f i) (f j)) ≤
      budget n x μ β c r₀ (combine n a f) := by
  rw [quadratic_defect_identity]
  exact (defect_self_bounds n x μ β c r₀ (combine n a f) hβ hr₀ hr₆).2

end FiniteSources

end
end UnifiedTheory.Clay.YangMills.SU2RetainedCovariance
