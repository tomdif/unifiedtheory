/- Derive the Schwartz-curve norm hypotheses from a smooth compactly
supported spacetime function, then construct localized tensor approximants. -/
import UnifiedTheory.Audit.KFCausalSmoothSpacetimeTests
import UnifiedTheory.Audit.KFCausalSchwartzCurveApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSmoothTestApproximation
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology
open UnifiedTheory.Audit.KFCausalSmoothSpacetimeTests (Test)
open UnifiedTheory.Audit.KFCausalSpacetimeUniformTests (slice expectation)
open UnifiedTheory.Audit.KFCausalSpacetimeSliceRegularity
open UnifiedTheory.Audit.KFCausalMomentumPairTests
open UnifiedTheory.Audit.KFCausalTensorTestClosure
open UnifiedTheory.Audit.KFCausalCompactTimeLocalization
open UnifiedTheory.Audit.KFCausalSchwartzCurveApproximation
open UnifiedTheory.Audit.KFCausalSpacetimeTriangularIntegral (timeWeight)

theorem schwartz_pair_eq (φ : Test) (t : ℝ) :
    spatialPair (φ.schwartz t) = (slice t φ.toBCF,slice t φ.dp.toBCF) := by
  rw [spatialPair,φ.schwartz_toBCF,φ.schwartz_deriv_toBCF]

theorem schwartz_pair_continuous (φ : Test) :
    Continuous (fun t => spatialPair (φ.schwartz t)) := by
  simp only [schwartz_pair_eq]
  exact (slice_uniformContinuous φ.toBCF φ.uniformContinuous).continuous.prodMk
    (slice_uniformContinuous φ.dp.toBCF φ.dp.uniformContinuous).continuous

theorem schwartz_pair_derivative (φ : Test) (t : ℝ) :
    HasDerivAt (fun u => spatialPair (φ.schwartz u)) (spatialPair (φ.dt.schwartz t)) t := by
  simp only [schwartz_pair_eq]
  apply slice_pair_hasDerivAt φ.toBCF φ.dt.toBCF φ.dp.toBCF φ.dt.dp.toBCF
    φ.dt.uniformContinuous φ.dt.dp.uniformContinuous φ.time_derivative
  intro u p
  have hd := φ.dp.time_derivative u p
  rw [φ.mixed_partials] at hd
  exact hd

def localizedValue (χ : Cutoff) (φ : Test) : (ℝ × ℝ) →ᵇ ℂ :=
  timeWeight (complexify χ.value) φ.toBCF

def localizedTimeDerivative (χ : Cutoff) (φ : Test) : (ℝ × ℝ) →ᵇ ℂ :=
  timeWeight (complexify χ.derivative) φ.toBCF + timeWeight (complexify χ.value) φ.dt.toBCF

def localizedMomentumDerivative (χ : Cutoff) (φ : Test) : (ℝ × ℝ) →ᵇ ℂ :=
  timeWeight (complexify χ.value) φ.dp.toBCF

theorem localized_approximable (χ : Cutoff) (φ : Test) :
    Approximable (localizedValue χ φ) (localizedTimeDerivative χ φ)
      (localizedMomentumDerivative χ φ) := by
  have h := schwartz_curve_approximable χ φ.schwartz φ.dt.schwartz
    (schwartz_pair_continuous φ.dt) (schwartz_pair_derivative φ)
  convert h using 1
  · ext ⟨t,p⟩
    change (χ.value t : ℂ)*φ.dp.value (t,p) =
      χ.value t • (SchwartzMap.derivCLM ℂ ℂ (φ.schwartz t)) p
    rw [φ.schwartz_deriv,Complex.real_smul]

theorem identify_derivatives (φ : Test) (q r s : (ℝ × ℝ) →ᵇ ℂ)
    (ha : Approximable q r s) (hq : q = φ.toBCF) :
    Approximable φ.toBCF φ.dt.toBCF φ.dp.toBCF := by
  have hr : r = φ.dt.toBCF := by
    ext ⟨t,p⟩
    have hd := limit_time_derivative q r s ha t p
    rw [hq] at hd
    exact hd.unique (φ.time_derivative t p)
  have hs : s = φ.dp.toBCF := by
    ext ⟨t,p⟩
    have hd := limit_momentum_derivative q r s ha t p
    rw [hq] at hd
    exact hd.unique (φ.momentum_derivative t p)
  rwa [hq,hr,hs] at ha

theorem approximable_of_cutoff_one (χ : Cutoff) (φ : Test)
    (hχ : ∀ z, φ.value z ≠ 0 → χ.value z.1 = 1) :
    Approximable φ.toBCF φ.dt.toBCF φ.dp.toBCF := by
  apply identify_derivatives φ _ _ _ (localized_approximable χ φ)
  ext z
  change (χ.value z.1 : ℂ)*φ.value z = φ.value z
  by_cases hz : φ.value z = 0
  · simp only [hz,mul_zero]
  · rw [hχ z hz,Complex.ofReal_one,one_mul]

#print axioms schwartz_pair_eq
#print axioms schwartz_pair_continuous
#print axioms schwartz_pair_derivative
#print axioms localized_approximable
#print axioms identify_derivatives
#print axioms approximable_of_cutoff_one
end
end UnifiedTheory.Audit.KFCausalSmoothTestApproximation
