/- The completed finite-cutoff SU(2) one-link source approximation.
The actual Haar coordinate formula discharges the geometric premise of the
intermediate scalar bridge. The varying-lattice convergence theorem concerns
only the approximation residual; its coupling slope and weight bound are
explicit assumptions. It does not control the exact retained source or
construct a nonzero continuum field. -/
import UnifiedTheory.Clay.YangMills.SU2SemicircleSlice
import UnifiedTheory.Clay.YangMills.SU2WilsonSourceApproximation
import UnifiedTheory.Clay.YangMills.SU2WilsonMarginalTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2WilsonSourceTheorem
noncomputable section
open MeasureTheory Filter Topology RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples SU2WilsonConditionalSource SU2WilsonSourceApproximation

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

/-- The actual one-link source has the proved scalar expansion on the good region. -/
theorem good_region_error (x : Vertex n) (μ : Fin 4) (β r₀ : ℝ)
    (hr₀ : 0 < r₀) (hβr : 3 / 4 ≤ β * r₀) (f : PlaquetteIndex n → ℝ)
    (r : Exterior n Q x μ) (hr : r₀ ≤ radius n x μ r) :
    |conditionalSource n x μ β f r - approximation n x μ β r₀ f r| ≤
      errorEnvelope n x μ β r₀ f :=
  SU2WilsonSourceApproximation.good_region_error n SU2SemicircleSlice.firstCoordinateFormula
    x μ β r₀ hr₀ hβr f r hr

/-- A uniform actual-Wilson bound with no assumed density or remainder estimate. -/
theorem hybrid_error_bound (x : Vertex n) (μ : Fin 4) (β r₀ r₁ : ℝ)
    (hr₀ : 0 < r₀) (hcut : r₀ < r₁) (hβr : 3 / 4 ≤ β * r₀)
    (f : PlaquetteIndex n → ℝ) (r : Exterior n Q x μ) :
    |conditionalSource n x μ β f r - hybridSource n x μ β r₀ r₁ f r| ≤
      errorEnvelope n x μ β r₀ f :=
  SU2WilsonSourceApproximation.hybrid_error_bound n SU2SemicircleSlice.firstCoordinateFormula
    x μ β r₀ r₁ hr₀ hcut hβr f r

/-- The corresponding mean-square estimate uses the actual retained Gibbs law. -/
theorem retained_error_l2_bound (x : Vertex n) (μ : Fin 4) (β r₀ r₁ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hcut : r₀ < r₁) (hβr : 3 / 4 ≤ β * r₀)
    (f : PlaquetteIndex n → ℝ) :
    (∫ r, (conditionalSource n x μ β f r - hybridSource n x μ β r₀ r₁ f r)^2
      ∂retainedLaw n x μ β) ≤ (errorEnvelope n x μ β r₀ f)^2 :=
  SU2WilsonSourceApproximation.retained_error_l2_bound n
    SU2SemicircleSlice.firstCoordinateFormula x μ β r₀ r₁ hβ hr₀ hcut hβr f

/-- The same residual estimate under the original interacting Wilson law.
The removed single-link fluctuation is not included in this residual. -/
theorem wilson_retained_error_l2_bound (x : Vertex n) (μ : Fin 4) (β r₀ r₁ : ℝ)
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hcut : r₀ < r₁) (hβr : 3 / 4 ≤ β * r₀)
    (f : PlaquetteIndex n → ℝ) :
    (∫ U, (conditionalSource n x μ β f
      (SU2WilsonMarginalTransport.exteriorProjection n x μ U) -
      hybridSource n x μ β r₀ r₁ f
        (SU2WilsonMarginalTransport.exteriorProjection n x μ U))^2
      ∂wilsonLaw n Q character β 2) ≤ (errorEnvelope n x μ β r₀ f)^2 :=
  SU2WilsonMarginalTransport.wilson_error_l2_bound n
    SU2SemicircleSlice.firstCoordinateFormula x μ β r₀ r₁ hβ hr₀ hcut hβr f

omit n [NeZero n] [Fact (1 < n)] in
/-- Cutoff-rescaled approximation error vanishes even when the lattice size,
selected link, exterior configuration and weights vary. The affected weight
sum must be uniformly bounded; block aggregation is not hidden in this input. -/
theorem rescaled_hybrid_error_tendsto {ι : Type*} {l : Filter ι}
    (period : ι → ℕ) [∀ i, NeZero (period i)] [∀ i, Fact (1 < period i)]
    (x : ∀ i, Vertex (period i)) (direction : ι → Fin 4)
    (a β : ι → ℝ) (b r₀ r₁ M : ℝ)
    (f : ∀ i, PlaquetteIndex (period i) → ℝ)
    (exterior : ∀ i, Exterior (period i) Q (x i) (direction i))
    (ha : Tendsto a l (𝓝[>] 0))
    (hβ : Tendsto (fun i => β i / Real.log (a i)⁻¹) l (𝓝 b))
    (hr₀ : 0 < r₀) (hcut : r₀ < r₁) (hmargin : 1 < b * r₀)
    (hweights : ∀ᶠ i in l,
      (∑ p ∈ SingleLinkWilsonOscillation.affected (period i) (x i) (direction i), |f i p|) ≤ M) :
    Tendsto (fun i => (a i ^ 4)⁻¹ •
      (conditionalSource (period i) (x i) (direction i) (β i) (f i) (exterior i) -
        hybridSource (period i) (x i) (direction i) (β i) r₀ r₁ (f i) (exterior i)))
      l (𝓝 0) := by
  have hb : 0 < b := by
    by_contra hn
    have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hr₀.le
    linarith
  have hbt := CouplingTrajectoryRobustness.coupling_tendsto_atTop a β b hb ha hβ
  have hβr : ∀ᶠ i in l, 3 / 4 ≤ β i * r₀ := by
    filter_upwards [hbt.eventually_ge_atTop ((3 / 4) / r₀)] with i hi
    exact (div_le_iff₀ hr₀).mp hi
  apply CouplingTrajectoryRobustness.cutoff_norm_error_tendsto a β b r₀
    (1280 * Real.exp 2 * r₀^2 * M) _ ha hβ hmargin
  filter_upwards [hβr, hweights] with i hi hw
  have hs : 0 ≤ (a i ^ 4)⁻¹ := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  calc
    _ ≤ (a i ^ 4)⁻¹ * errorEnvelope (period i) (x i) (direction i) (β i) r₀ (f i) :=
      mul_le_mul_of_nonneg_left
        (hybrid_error_bound (period i) (x i) (direction i) (β i) r₀ r₁
          hr₀ hcut hi (f i) (exterior i)) hs
    _ ≤ (a i ^ 4)⁻¹ *
        (1280 * Real.exp 2 * r₀^2 * β i^2 * Real.exp (-4 * β i * r₀) * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (by positivity)) hs
    _ = _ := by ring

end
end UnifiedTheory.Clay.YangMills.SU2WilsonSourceTheorem
