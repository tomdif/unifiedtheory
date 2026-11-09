/- The commuting phase tests of the doubled positive construction pull
back to opposite position phases and equal translations in the two factors.
The identity holds for arbitrary L2 states and windows. -/
import UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceState
import UnifiedTheory.Audit.KFCausalPartialFourierTranslation
import UnifiedTheory.Audit.KFCausalPartialFourierMultiplier
import UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalWindowedCanonicalTests
noncomputable section
open MeasureTheory MeasureTheory.Measure
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalPartialFourier
open UnifiedTheory.Audit.KFCausalPartialFourierTranslation
open UnifiedTheory.Audit.KFCausalPartialFourierMultiplier
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
open UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceState

variable (n : ℕ)

def positionPhase (u : Block n →L[ℝ] ℝ) (q : Block n) : ℂ := scalar (u q)

theorem positionPhase_measurable (u : Block n →L[ℝ] ℝ) : Measurable (positionPhase n u) := by
  unfold positionPhase scalar
  fun_prop

def positionAction (u : Block n →L[ℝ] ℝ) : ProductHilbert n n →L[ℂ] ProductHilbert n n :=
  rightMultiplier n n (positionPhase n u) (positionPhase_measurable n u)
    (fun q => (scalar_norm (u q)).le)

theorem positionAction_coe (u : Block n →L[ℝ] ℝ) (f : ProductHilbert n n) :
    positionAction n u f =ᵐ[volume] fun z => scalar (u z.2)*f z :=
  rightMultiplier_coe n n _ _ _ f

def reflected (z : Frequency (X := Block n)) : Frequency (X := Block n) := (-z.1,z.2)

def phaseTest (h : ℝ) (z : Frequency (X := Block n)) : ProductHilbert n n →L[ℂ] ProductHilbert n n :=
  (positionAction n z.1).comp (leftPhase n n (h • z.2))

def phaseSymbol (h : ℝ) (z : Frequency (X := Block n)) (x : Block n × Block n) : ℂ :=
  scalar (z.1 x.2)*KFCausalFourierTranslation.phase (h • z.2) x.1

theorem phaseSymbol_measurable (h : ℝ) (z : Frequency (X := Block n)) : Measurable (phaseSymbol n h z) := by
  unfold phaseSymbol scalar KFCausalFourierTranslation.phase
  fun_prop

theorem phaseSymbol_norm (h : ℝ) (z : Frequency (X := Block n)) (x : Block n × Block n) :
    ‖phaseSymbol n h z x‖ = 1 := by
  rw [phaseSymbol,norm_mul,scalar_norm,KFCausalFourierTranslation.phase_norm,one_mul]

theorem phaseTest_coe (h : ℝ) (z : Frequency (X := Block n)) (f : ProductHilbert n n) :
    phaseTest n h z f =ᵐ[volume] fun x => phaseSymbol n h z x*f x := by
  filter_upwards [positionAction_coe n z.1 (leftPhase n n (h • z.2) f),
    leftPhase_coe n n (h • z.2) f] with x hp hl
  change positionAction n z.1 (leftPhase n n (h • z.2) f) x = _
  rw [hp,hl,phaseSymbol,mul_assoc]

theorem shear_tests (h : ℝ) (z : Frequency (X := Block n)) (f g : BlockHilbert n) :
    shearUnitary n (productState volume volume (operator volume h z f)
      (operator volume h (reflected n z) g)) =
      positionAction n z.1 (leftTranslation n n (h • z.2)
        (shearUnitary n (productState volume volume f g))) := by
  apply Lp.ext
  filter_upwards [shear_product_coe n (operator volume h z f) (operator volume h (reflected n z) g),
    (quasiMeasurePreserving_fst.comp (shear_preserves n).quasiMeasurePreserving).ae (operator_coe volume h z f),
    quasiMeasurePreserving_fst.ae (operator_coe volume h (reflected n z) g),
    positionAction_coe n z.1 (leftTranslation n n (h • z.2) (shearUnitary n (productState volume volume f g))),
    leftTranslation_coe n n (h • z.2) (shearUnitary n (productState volume volume f g)),
    (leftShift_preserves n n (h • z.2)).quasiMeasurePreserving.ae (shear_product_coe n f g)]
    with x hs hf hg hp ht hv
  change operator volume h z f (x.1+x.2) = _ at hf
  change operator volume h (reflected n z) g x.1 = _ at hg
  change shearUnitary n (productState volume volume f g) (x.1+h • z.2,x.2) = _ at hv
  rw [hs,hf,hg,hp,ht,hv]
  change scalar (z.1 (x.1+x.2))*f (x.1+x.2+h • z.2)*
    (scalar ((-z.1) x.1)*g (x.1+h • z.2)) =
      scalar (z.1 x.2)*(f (x.1+h • z.2+x.2)*g (x.1+h • z.2))
  have he : scalar (z.1 (x.1+x.2))*scalar ((-z.1) x.1) = scalar (z.1 x.2) := by
    rw [← scalar_add,map_add,ContinuousLinearMap.neg_apply]
    congr 1
    ring
  rw [show x.1+x.2+h • z.2 = x.1+h • z.2+x.2 by abel]
  calc
    _ = (scalar (z.1 (x.1+x.2))*scalar ((-z.1) x.1))*
        (f (x.1+h • z.2+x.2)*g (x.1+h • z.2)) := by ring
    _ = _ := by rw [he]

theorem state_tests (h : ℝ) (z : Frequency (X := Block n)) (f g : BlockHilbert n) :
    state n (operator volume h z f) (operator volume h (reflected n z) g) =
      phaseTest n h z (state n f g) := by
  change leftFourier n n (shearUnitary n (productState volume volume
    (operator volume h z f) (operator volume h (reflected n z) g))) = _
  rw [shear_tests]
  change leftFourier n n (rightMultiplier n n _ _ _
    (leftTranslation n n (h • z.2) (shearUnitary n (productState volume volume f g)))) = _
  rw [leftFourier_commutes,leftFourier_translation]
  rfl

theorem phase_expectation (h : ℝ) (z : Frequency (X := Block n)) (f g : BlockHilbert n) :
    inner ℂ (state n f g) (phaseTest n h z (state n f g)) =
      characteristic volume h f z * characteristic volume h g (reflected n z) := by
  rw [← state_tests,state_inner]
  rfl

#print axioms positionPhase_measurable
#print axioms positionAction_coe
#print axioms phaseSymbol_measurable
#print axioms phaseSymbol_norm
#print axioms phaseTest_coe
#print axioms shear_tests
#print axioms state_tests
#print axioms phase_expectation

end
end UnifiedTheory.Audit.KFCausalWindowedCanonicalTests
