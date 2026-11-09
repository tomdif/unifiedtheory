/- The positive windowed measure is constructed from the actual physical
configuration state. Every physical canonical test retains its exact
characteristic identity under the existing Euclidean coordinate map. -/
import UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceLaw
import UnifiedTheory.Audit.KFCausalPhysicalCanonicalCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (euclideanPullback)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block BlockHilbert)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
open UnifiedTheory.Audit.KFCausalPhysicalCanonicalCoordinates (frequency characteristic_coordinates)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def law (h : ℝ) (f : Hilbert) (g : BlockHilbert 6) : Measure (Block 6 × Block 6) :=
  KFCausalWindowedPhaseSpaceLaw.law 6 h (euclideanPullback f) g

def phase (z : Frequency (X := Configuration)) : Block 6 × Block 6 → ℂ :=
  KFCausalWindowedPhaseSpaceLaw.classicalPhase 6 (frequency z)

theorem law_probability (h : ℝ) (f : Hilbert) (g : BlockHilbert 6)
    (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) : IsProbabilityMeasure (law h f g) :=
  KFCausalWindowedPhaseSpaceLaw.law_probability 6 h (euclideanPullback f) g
    ((euclideanPullback.norm_map f).trans hf) hg

theorem law_characteristic (h : ℝ) (f : Hilbert) (g : BlockHilbert 6)
    (z : Frequency (X := Configuration)) :
    (∫ x, phase z x ∂law h f g) = characteristic volume h f z *
      characteristic volume h g (KFCausalWindowedCanonicalTests.reflected 6 (frequency z)) := by
  change (∫ x, KFCausalWindowedPhaseSpaceLaw.classicalPhase 6 (frequency z) x
    ∂KFCausalWindowedPhaseSpaceLaw.law 6 h (euclideanPullback f) g) = _
  rw [KFCausalWindowedPhaseSpaceLaw.law_characteristic,characteristic_coordinates]

theorem characteristic_error (h : ℝ) (f : Hilbert) (g : BlockHilbert 6)
    (z : Frequency (X := Configuration)) :
    ‖(∫ x, phase z x ∂law h f g)-characteristic volume h f z‖ ≤
      ‖f‖^2*‖characteristic volume h g (KFCausalWindowedCanonicalTests.reflected 6 (frequency z))-1‖ := by
  rw [law_characteristic,← mul_sub_one,norm_mul]
  exact mul_le_mul_of_nonneg_right (characteristic_bound volume h f z) (norm_nonneg _)

#print axioms law_probability
#print axioms law_characteristic
#print axioms characteristic_error

end
end UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw
