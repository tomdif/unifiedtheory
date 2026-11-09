/- All-order quadratic counterterm jets under the actual interacting Wilson
law. The source is an actual smeared plaquette defect and is centered under
that same law. Local contact subtraction is identified exactly at second
order. No physical coefficient or cutoff-uniform hierarchy bound is chosen. -/
import UnifiedTheory.Clay.YangMills.CompactQuadraticJets
import UnifiedTheory.Clay.YangMills.WilsonSmearedObservable
import UnifiedTheory.Clay.YangMills.GibbsCrossCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonQuadraticJets
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 SchwartzConfigurationTensor
open DiagonalContactTerms LocalCountertermReflection CompactQuadraticJets

/-- Exact identification with the existing diagonal contact distribution. -/
theorem contact_tensor (f : CorrelationTest 1) :
    contact (tensor 1 1 f f) = localSquare f := by
  rw [contact_apply]
  unfold localSquare
  apply integral_congr_ae
  filter_upwards with x
  exact (SchwartzConfigurationTensor.tensor_concat 1 1 f f x x).trans (pow_two (f x)).symm

theorem localSquare_smul (z : ℂ) (f : CorrelationTest 1) :
    localSquare (z • f) = z ^ 2 * localSquare f := by
  unfold localSquare
  simp only [SchwartzMap.smul_apply, smul_eq_mul, mul_pow]
  rw [integral_const_mul]

/-- Physical real sources have a real local quadratic counterterm. -/
theorem localSquare_im_zero (f : CorrelationTest 1) (hf : ∀ x, (f x).im = 0) :
    (localSquare f).im = 0 := by
  change RCLike.im (∫ x, (f x)^2) = 0
  rw [← integral_im (square_integrable f)]
  simp [pow_two, hf]

theorem sourceFactor_real_ray (κ t : ℝ) (f : CorrelationTest 1)
    (hf : ∀ x, (f x).im = 0) :
    sourceFactor κ ((t : ℂ) • f) =
      (Real.exp (-(κ * (localSquare f).re) * t ^ 2) : ℂ) := by
  have hq : ((localSquare f).re : ℂ) = localSquare f := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (localSquare_im_zero f hf).symm
  rw [sourceFactor, localSquare_smul, Complex.ofReal_exp, ← hq]
  congr 1
  push_cast
  simp only [Complex.ofReal_re]
  ring

/-- The real-axis jet construction is exactly the earlier holomorphic local
source factor on real Schwartz tests. -/
theorem real_ray_identification {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ) (κ t : ℝ) (f : CorrelationTest 1)
    (hf : ∀ x, (f x).im = 0) :
    (CompactQuadraticJets.renormalized μ F (κ * (localSquare f).re) t : ℂ) =
      sourceFactor κ ((t : ℂ) • f) * (sourcePartition μ F t : ℂ) := by
  rw [CompactQuadraticJets.renormalized, Complex.ofReal_mul, sourceFactor_real_ray κ t f hf]

variable (n : ℕ) [NeZero n] (G : Type*) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Smeared plaquette defect with the original Wilson action left unchanged. -/
def source (a : ℝ) (plane : Plane) (χ : G → ℂ) (c : ℝ) (f : CorrelationTest 1)
    (U : RegulatedGauge.Configuration (Vertex n) G) : ℝ :=
  (WilsonSmearedObservable.observable G n a plane
    (fun g => ((c - (χ g).re : ℝ) : ℂ)) 1 f U).re

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
theorem defectCharacter_continuous (χ : G → ℂ) (hχ : Continuous χ) (c : ℝ) :
    Continuous (fun g => ((c - (χ g).re : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (continuous_const.sub (Complex.continuous_re.comp hχ))

theorem source_continuous (a : ℝ) (plane : Plane) (χ : G → ℂ) (hχ : Continuous χ)
    (c : ℝ) (f : CorrelationTest 1) : Continuous (source n G a plane χ c f) :=
  Complex.continuous_re.comp (WilsonSmearedObservable.observable_continuous G n a plane _
    (defectCharacter_continuous G χ hχ c) 1 f)

/-- Centering is taken under the actual interacting law, not a substitute measure. -/
def centeredSource (a : ℝ) (plane : Plane) (χ : G → ℂ) (β c : ℝ) (f : CorrelationTest 1)
    (U : RegulatedGauge.Configuration (Vertex n) G) : ℝ :=
  source n G a plane χ c f U - ∫ V, source n G a plane χ c f V ∂wilsonLaw n G χ β c

theorem centeredSource_continuous (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hχ : Continuous χ) (β c : ℝ) (f : CorrelationTest 1) :
    Continuous (centeredSource n G a plane χ β c f) :=
  (source_continuous n G a plane χ hχ c f).sub continuous_const

theorem centeredSource_mean (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hχ : Continuous χ) (β c : ℝ) (f : CorrelationTest 1) :
    (∫ U, centeredSource n G a plane χ β c f U ∂wilsonLaw n G χ β c) = 0 := by
  letI := wilsonLaw_probability n G χ hχ β c
  unfold centeredSource
  rw [integral_sub ((source_continuous n G a plane χ hχ c f).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (integrable_const _)]
  simp

def generating (a : ℝ) (plane : Plane) (χ : G → ℂ) (β c κ : ℝ) (f : CorrelationTest 1)
    (t : ℝ) : ℝ :=
  CompactQuadraticJets.renormalized (wilsonLaw n G χ β c)
    (centeredSource n G a plane χ β c f) (κ * (localSquare f).re) t

/-- All derivative orders are derived, with the actual law and centered source. -/
theorem all_order_jets (a : ℝ) (plane : Plane) (χ : G → ℂ) (hχ : Continuous χ)
    (β c κ : ℝ) (f : CorrelationTest 1) (m : ℕ) :
    iteratedDeriv m (generating n G a plane χ β c κ f) 0 =
      ∫ U, (wickPolynomial (κ * (localSquare f).re) m).eval
        (centeredSource n G a plane χ β c f U) ∂wilsonLaw n G χ β c := by
  letI := wilsonLaw_probability n G χ hχ β c
  exact iteratedDeriv_zero_source (wilsonLaw n G χ β c) _
    (centeredSource_continuous n G a plane χ hχ β c f) _ m

theorem normalized (a : ℝ) (plane : Plane) (χ : G → ℂ) (hχ : Continuous χ)
    (β c κ : ℝ) (f : CorrelationTest 1) : generating n G a plane χ β c κ f 0 = 1 := by
  letI := wilsonLaw_probability n G χ hχ β c
  exact renormalized_normalized _ _ _

theorem first_jet_zero (a : ℝ) (plane : Plane) (χ : G → ℂ) (hχ : Continuous χ)
    (β c κ : ℝ) (f : CorrelationTest 1) :
    iteratedDeriv 1 (generating n G a plane χ β c κ f) 0 = 0 := by
  rw [all_order_jets n G a plane χ hχ β c κ f 1]
  simp only [wickPolynomial_one]
  exact centeredSource_mean n G a plane χ hχ β c f

/-- The second jet subtracts the actual diagonal contact from the actual
connected covariance, with the coefficient dictated by the source exponential. -/
theorem second_jet_contact (a : ℝ) (plane : Plane) (χ : G → ℂ) (hχ : Continuous χ)
    (β c κ : ℝ) (f : CorrelationTest 1) :
    iteratedDeriv 2 (generating n G a plane χ β c κ f) 0 =
      GibbsCrossCovariance.covariance (wilsonLaw n G χ β c)
        (source n G a plane χ c f) (source n G a plane χ c f) -
      2 * κ * (contact (tensor 1 1 f f)).re := by
  letI := wilsonLaw_probability n G χ hχ β c
  have h := second_derivative (wilsonLaw n G χ β c) _
    (centeredSource_continuous n G a plane χ hχ β c f) (κ * (localSquare f).re)
  rw [GibbsCrossCovariance.covariance_eq_centered _ _ _
    (source_continuous n G a plane χ hχ c f) (source_continuous n G a plane χ hχ c f),
    contact_tensor]
  change iteratedDeriv 2 (generating n G a plane χ β c κ f) 0 =
    (∫ U, centeredSource n G a plane χ β c f U * centeredSource n G a plane χ β c f U
      ∂wilsonLaw n G χ β c) - 2 * κ * (localSquare f).re
  simpa only [generating, pow_two, mul_assoc] using h

/-- Fourth order already forces both the lower-moment subtraction and the
quadratic counterterm-square contribution; neither is freely discarded. -/
theorem fourth_jet (a : ℝ) (plane : Plane) (χ : G → ℂ) (hχ : Continuous χ)
    (β c κ : ℝ) (f : CorrelationTest 1) :
    iteratedDeriv 4 (generating n G a plane χ β c κ f) 0 =
      (∫ U, (centeredSource n G a plane χ β c f U)^4 ∂wilsonLaw n G χ β c) -
      12 * (κ * (localSquare f).re) *
        (∫ U, (centeredSource n G a plane χ β c f U)^2 ∂wilsonLaw n G χ β c) +
      12 * (κ * (localSquare f).re)^2 := by
  letI := wilsonLaw_probability n G χ hχ β c
  exact fourth_derivative (wilsonLaw n G χ β c) _
    (centeredSource_continuous n G a plane χ hχ β c f) _

end
end UnifiedTheory.Clay.YangMills.WilsonQuadraticJets
