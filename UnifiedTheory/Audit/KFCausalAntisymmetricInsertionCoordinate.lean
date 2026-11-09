/- The actual antisymmetric momentum insertion in normalized reciprocal
Gaussian coordinates. The physical momentum scale cancels exactly. -/
import UnifiedTheory.Audit.KFCausalClockMixedAntisymmetricGraph
import UnifiedTheory.Audit.KFCausalSymmetricInsertionCoordinate
import UnifiedTheory.Audit.KFCausalMixedStripTailAttachment

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalAntisymmetricInsertionCoordinate
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint Block split)
open KFCausalComplexClockInverse (complexInverse complexInverse_real)
open KFCausalPairedModeCoordinates (scale modeIsometry)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalSymmetricInsertionCoordinate (coordinateScale coordinateScale_positive)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector)
open KFCausalPhysicalReciprocalNormalization (normalize)
open KFCausalComplexShearPerturbation (flow)
open KFCausalClockMixedAntisymmetricGraph (mixedSymbol mixedSymbol_eq)
open KFCausalClockFloorPairedStraightening (dilation clockInverse)
open KFCausalRegularizedLongitudinalChart (chartIso)
open KFCausalMixedStripTailAttachment (tailPoint)
open KFCausalEuclideanClockSplit (tail)

def lowerIndex (i : Fin 2) : Fin 5 := ![0,1] i

def coefficient (ε h : ℝ) (i : Fin 2) (q : ℂ) (x : Joint 2 4) : ℂ :=
  ((2*Real.pi*h*(2*scale):ℝ):ℂ)*Complex.exp (-complexInverse ε q/2)*(x (.inl i):ℂ)

theorem coefficient_eq_baseline (ε h α w : ℝ) (i : Fin 2) (q : ℂ) (x : Joint 2 4)
    (hα : 0 < α) (hw : 0 < w) :
    coefficient ε h i q x = (2*scale:ℂ)*
      baselineVector ε α w (momentumScale h) q x (lowerIndex i)/(coordinateScale α w i:ℂ) := by
  have hn : (coordinateScale α w i:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (coordinateScale_positive α w hα hw i))
  apply (eq_div_iff hn).mpr
  fin_cases i <;> dsimp [coefficient,baselineVector,flow,KFCausalPhysicalReciprocalNormalization.normalize,lowerIndex,coordinateScale,momentumScale]
  all_goals push_cast; ring

theorem coefficient_real (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2)
    (x : Block 2 × Block 4) :
    coefficient ε h i (x.2 0:ℂ) ((split 2 4).symm x)=(mixedSymbol ε hε h i x:ℂ) := by
  rw [coefficient,complexInverse_real ε hε,mixedSymbol_eq]
  change ((2*Real.pi*h*(2*scale):ℝ):ℂ)*
    Complex.exp (-((chartIso ε hε).symm (x.2 0):ℂ)/2)*(x.1 i:ℂ)=_
  rw [show -((chartIso ε hε).symm (x.2 0):ℂ)/2=
    ((-((chartIso ε hε).symm (x.2 0)/2):ℝ):ℂ) by push_cast; ring]
  rw [← Complex.ofReal_exp]
  unfold dilation clockInverse
  rw [Real.exp_neg]
  push_cast
  ring

theorem coefficient_real_continuous (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) :
    Continuous (fun z : ℝ × Joint 2 4 => coefficient ε h i (z.1:ℂ) z.2) := by
  simp_rw [coefficient,complexInverse_real ε hε]
  have hs : Continuous (fun z : ℝ × Joint 2 4 => ((chartIso ε hε).symm z.1:ℂ)) :=
    Complex.continuous_ofReal.comp ((chartIso ε hε).symm.continuous.comp continuous_fst)
  have hx : Continuous (fun z : ℝ × Joint 2 4 => (z.2 (.inl i):ℂ)) :=
    Complex.continuous_ofReal.comp
    ((PiLp.continuous_apply 2 (fun _ : Fin 2 ⊕ Fin 4 => ℝ) (.inl i)).comp continuous_snd)
  exact (continuous_const.mul (hs.neg.div_const 2).cexp).mul hx

theorem coefficient_tail (ε h : ℝ) (i : Fin 2) (q : ℂ)
    (x : KFCausalEuclideanConfiguration.Space) :
    coefficient ε h i q (tailPoint (tail x))=coefficient ε h i q (modeIsometry x) := by
  fin_cases i <;> rfl

#print axioms coefficient_eq_baseline
#print axioms coefficient_real
#print axioms coefficient_real_continuous
#print axioms coefficient_tail
end
end UnifiedTheory.Audit.KFCausalAntisymmetricInsertionCoordinate
