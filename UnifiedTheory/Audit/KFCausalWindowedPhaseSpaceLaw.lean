/- A genuine positive phase-space measure of the windowed quantum state.
Its classical characteristic is exactly the product of the original
canonical characteristic and the reflected window characteristic. -/
import UnifiedTheory.Audit.KFCausalWindowedCanonicalTests
import UnifiedTheory.Audit.KFCausalL2BornLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceLaw
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
open UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceState
open UnifiedTheory.Audit.KFCausalWindowedCanonicalTests

variable (n : ℕ)

def phaseCoordinates (h : ℝ) (x : Block n × Block n) : Block n × Block n :=
  (x.2,(2*Real.pi*h) • x.1)

theorem phaseCoordinates_measurable (h : ℝ) : Measurable (phaseCoordinates n h) := by
  unfold phaseCoordinates
  fun_prop

def classicalPhase (z : Frequency (X := Block n)) (x : Block n × Block n) : ℂ :=
  scalar (z.1 x.1+inner ℝ z.2 x.2)

theorem classicalPhase_measurable (z : Frequency (X := Block n)) : Measurable (classicalPhase n z) := by
  unfold classicalPhase scalar
  fun_prop

theorem classicalPhase_coordinates (h : ℝ) (z : Frequency (X := Block n)) (x : Block n × Block n) :
    classicalPhase n z (phaseCoordinates n h x) = phaseSymbol n h z x := by
  rw [classicalPhase,phaseCoordinates,scalar_add,phaseSymbol]
  congr 1
  simp only [scalar,KFCausalFourierTranslation.phase,Real.fourierChar_apply,
    inner_smul_right,inner_smul_left,conj_trivial,Complex.ofReal_mul,Complex.ofReal_ofNat]
  congr 1
  ring

def law (h : ℝ) (f g : BlockHilbert n) : Measure (Block n × Block n) :=
  (KFCausalL2BornLaw.law volume (state n f g)).map (phaseCoordinates n h)

theorem law_total (h : ℝ) (f g : BlockHilbert n) :
    law n h f g Set.univ = ENNReal.ofReal ((‖f‖*‖g‖)^2) := by
  rw [law,Measure.map_apply (phaseCoordinates_measurable n h) MeasurableSet.univ,
    Set.preimage_univ,KFCausalL2BornLaw.law_total,state_norm]

theorem law_probability (h : ℝ) (f g : BlockHilbert n) (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) :
    IsProbabilityMeasure (law n h f g) where
  measure_univ := by rw [law_total,hf,hg,one_mul,one_pow,ENNReal.ofReal_one]

theorem law_characteristic (h : ℝ) (f g : BlockHilbert n) (z : Frequency (X := Block n)) :
    (∫ x, classicalPhase n z x ∂law n h f g) =
      characteristic volume h f z * characteristic volume h g (reflected n z) := by
  rw [law,integral_map (phaseCoordinates_measurable n h).aemeasurable
    (classicalPhase_measurable n z).aestronglyMeasurable]
  simp only [classicalPhase_coordinates]
  rw [KFCausalL2BornLaw.integral_eq_inner volume (state n f g)
    (phaseTest n h z (state n f g)) (phaseSymbol n h z) (phaseTest_coe n h z (state n f g)),
    phase_expectation]

theorem characteristic_error (h : ℝ) (f g : BlockHilbert n) (z : Frequency (X := Block n)) :
    ‖(∫ x, classicalPhase n z x ∂law n h f g)-characteristic volume h f z‖ ≤
      ‖f‖^2*‖characteristic volume h g (reflected n z)-1‖ := by
  rw [law_characteristic,← mul_sub_one,norm_mul]
  exact mul_le_mul_of_nonneg_right (characteristic_bound volume h f z) (norm_nonneg _)

#print axioms phaseCoordinates_measurable
#print axioms classicalPhase_measurable
#print axioms classicalPhase_coordinates
#print axioms law_total
#print axioms law_probability
#print axioms law_characteristic
#print axioms characteristic_error

end
end UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceLaw
