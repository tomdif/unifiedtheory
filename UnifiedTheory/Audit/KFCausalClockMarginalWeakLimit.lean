/- Canonical characteristic limits identify the actual clock Born marginal
with the clock marginal of the represented phase-space probability. Weak
convergence then identifies the bounded clock-defect expectation. -/
import UnifiedTheory.Audit.KFCausalClockMarginalIdentification
import UnifiedTheory.Audit.KFCausalClockFloorClockMomentLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockMarginalWeakLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockMarginalIdentification
open UnifiedTheory.Audit.KFCausalTenPhaseProjection
open UnifiedTheory.Audit.KFCausalCanonicalTenCoordinates (Coefficients encode)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (characteristic)
open UnifiedTheory.Audit.KFCausalClockPositionLaw
open UnifiedTheory.Audit.KFCausalClockFloorCountableCharacteristics (ClassicalKernel)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorClockMomentLaw (defect_continuous defect_strict_bounds)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def bornProbability (f : Hilbert) (hf : ‖f‖ = 1) : ProbabilityMeasure ℝ :=
  ⟨clockPositionLaw f,clockPositionLaw_probability f hf⟩

theorem born_weak_limit (h : ℕ → ℝ) (f : ℕ → Hilbert) (hf : ∀ n, ‖f n‖ = 1)
    (χ : ClassicalKernel) (ν : ProbabilityMeasure TenSpace)
    (hν : ∀ z, charFun (ν : Measure TenSpace) (coefficientVector z) = χ.value z)
    (hc : ∀ z, Tendsto (fun n => characteristic volume (h n) (f n) (encode z)) atTop (𝓝 (χ.value z))) :
    Tendsto (fun n => bornProbability (f n) (hf n)) atTop (𝓝 (marginal ν)) := by
  apply KFCausalCharacteristicRepresentation.weak_convergence
    (fun n => bornProbability (f n) (hf n)) (fun u => χ.value (axis u))
    (χ.continuous_value.comp axis.continuous) (by simp only [map_zero,χ.value_zero])
  · intro u
    simpa only [bornProbability,ProbabilityMeasure.coe_mk,← born_characteristic] using hc (axis u)
  · intro u
    rw [marginal_characteristic,hν]

def defectTest (ε : ℝ) (hε : 0 < ε) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨defect ε,defect_continuous ε hε⟩ 1
    (fun x y => by
      change dist (defect ε x) (defect ε y) ≤ 1
      rw [Real.dist_eq,abs_le]
      constructor <;> linarith [(defect_strict_bounds ε hε x).1,
        (defect_strict_bounds ε hε x).2,(defect_strict_bounds ε hε y).1,
        (defect_strict_bounds ε hε y).2])

theorem defect_expectation (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    (∫ u, defect ε u ∂clockPositionLaw f) = (inner ℂ f (defectOperator ε hε f)).re := by
  have hi : (∫ u, (defect ε u : ℂ) ∂clockPositionLaw f) = inner ℂ f (defectOperator ε hε f) := by
    rw [clockPositionLaw,integral_map (f := fun u : ℝ => (defect ε u : ℂ)) measurable_fst.aemeasurable
      (Complex.continuous_ofReal.comp (defect_continuous ε hε)).aestronglyMeasurable]
    exact KFCausalL2BornLaw.integral_eq_inner volume f (defectOperator ε hε f)
      (fun x : Configuration => (defect ε x.1 : ℂ)) (defectOperator_coe ε hε f)
  rw [integral_complex_ofReal] at hi
  exact congrArg Complex.re hi

theorem defect_mean_limit (ε : ℝ) (hε : 0 < ε)
    (h : ℕ → ℝ) (f : ℕ → Hilbert) (hf : ∀ n, ‖f n‖ = 1)
    (χ : ClassicalKernel) (ν : ProbabilityMeasure TenSpace)
    (hν : ∀ z, charFun (ν : Measure TenSpace) (coefficientVector z) = χ.value z)
    (hc : ∀ z, Tendsto (fun n => characteristic volume (h n) (f n) (encode z)) atTop (𝓝 (χ.value z))) :
    Tendsto (fun n => (inner ℂ (f n) (defectOperator ε hε (f n))).re) atTop
      (𝓝 (∫ x, defect ε (clockProjection x) ∂(ν : Measure TenSpace))) := by
  have hw := born_weak_limit h f hf χ ν hν hc
  have hi := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hw (defectTest ε hε)
  change Tendsto (fun n => ∫ u, defect ε u ∂clockPositionLaw (f n)) atTop
    (𝓝 (∫ u, defect ε u ∂(ν : Measure TenSpace).map clockProjection)) at hi
  rw [integral_map clockProjection.continuous.measurable.aemeasurable
    (defect_continuous ε hε).measurable.aestronglyMeasurable] at hi
  simpa only [defect_expectation ε hε] using hi

#print axioms born_weak_limit
#print axioms defect_expectation
#print axioms defect_mean_limit

end
end UnifiedTheory.Audit.KFCausalClockMarginalWeakLimit
