/- The represented eleven-coordinate law retains the actual clock Born
marginal and clock-defect mean. A zero limiting defect is not inferred. -/
import UnifiedTheory.Audit.KFCausalElevenMarginals
import UnifiedTheory.Audit.KFCausalClockMarginalWeakLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalElevenClockCompatibility
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalElevenPhaseProjection
open UnifiedTheory.Audit.KFCausalElevenMarginals
open UnifiedTheory.Audit.KFCausalElevenCountableCharacteristics (ClassicalKernel)
open UnifiedTheory.Audit.KFCausalCanonicalElevenCoordinates (Coefficients encode)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorClockMomentLaw (defect_continuous)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def clockProjection : ElevenSpace →L[ℝ] ℝ :=
  KFCausalClockMarginalIdentification.clockProjection.comp tenProjection

def clockMarginal (ν : ProbabilityMeasure ElevenSpace) : ProbabilityMeasure ℝ :=
  KFCausalClockMarginalIdentification.marginal (tenMarginal ν)

theorem born_weak_limit (h : ℕ → ℝ) (f : ℕ → Hilbert) (hf : ∀ n, ‖f n‖ = 1)
    (χ : ClassicalKernel) (ν : ProbabilityMeasure ElevenSpace)
    (hν : ∀ z, charFun (ν : Measure ElevenSpace) (coefficientVector z) = χ.value z)
    (hc : ∀ z, Tendsto (fun n => characteristic volume (h n) (f n) (encode z)) atTop (𝓝 (χ.value z))) :
    Tendsto (fun n => KFCausalClockMarginalWeakLimit.bornProbability (f n) (hf n))
      atTop (𝓝 (clockMarginal ν)) := by
  apply KFCausalClockMarginalWeakLimit.born_weak_limit h f hf (restrictKernel χ) (tenMarginal ν)
    (ten_marginal_represents ν χ hν)
  intro z
  simpa only [ten_encode] using hc (z,0)

theorem defect_mean_limit (ε : ℝ) (hε : 0 < ε)
    (h : ℕ → ℝ) (f : ℕ → Hilbert) (hf : ∀ n, ‖f n‖ = 1)
    (χ : ClassicalKernel) (ν : ProbabilityMeasure ElevenSpace)
    (hν : ∀ z, charFun (ν : Measure ElevenSpace) (coefficientVector z) = χ.value z)
    (hc : ∀ z, Tendsto (fun n => characteristic volume (h n) (f n) (encode z)) atTop (𝓝 (χ.value z))) :
    Tendsto (fun n => (inner ℂ (f n) (defectOperator ε hε (f n))).re) atTop
      (𝓝 (∫ x, defect ε (clockProjection x) ∂(ν : Measure ElevenSpace))) := by
  have ht := KFCausalClockMarginalWeakLimit.defect_mean_limit ε hε h f hf
    (restrictKernel χ) (tenMarginal ν) (ten_marginal_represents ν χ hν)
    (fun z => by simpa only [ten_encode] using hc (z,0))
  change Tendsto _ atTop (𝓝 (∫ x, defect ε (KFCausalClockMarginalIdentification.clockProjection x)
    ∂(ν : Measure ElevenSpace).map tenProjection)) at ht
  have he : (∫ x, defect ε (KFCausalClockMarginalIdentification.clockProjection x)
      ∂(ν : Measure ElevenSpace).map tenProjection) =
      ∫ x, defect ε (clockProjection x) ∂(ν : Measure ElevenSpace) :=
    integral_map tenProjection.continuous.measurable.aemeasurable
      ((defect_continuous ε hε).comp KFCausalClockMarginalIdentification.clockProjection.continuous).measurable.aestronglyMeasurable
  rw [he] at ht
  exact ht

#print axioms born_weak_limit
#print axioms defect_mean_limit

end
end UnifiedTheory.Audit.KFCausalElevenClockCompatibility
