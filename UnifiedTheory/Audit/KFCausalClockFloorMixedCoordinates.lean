/- Whole-L2 clock straightening in the actual partial Fourier coordinates.
The weighted coordinate formula follows from the integral calculation on
dense product tests and preservation of null sets, rather than being an
identification hypothesis. This is a real-coordinate theorem; the graph of
the longitudinal exponential and complex-strip continuation are separate. -/
import UnifiedTheory.Audit.KFCausalClockFloorMixedChart
import UnifiedTheory.Audit.KFCausalClockFloorMixedProduct
import UnifiedTheory.Audit.KFCausalWeightedTensorRepresentative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

namespace UnifiedTheory.Audit.KFCausalClockFloorMixedCoordinates
noncomputable section
open MeasureTheory
open scoped FourierTransform CompactlySupported
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block BlockHilbert ProductHilbert)
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding (productState)
open UnifiedTheory.Audit.KFCausalPartialFourier
open UnifiedTheory.Audit.KFCausalClockFloorPairedStraightening
open UnifiedTheory.Audit.KFCausalClockFloorMixedChart
open UnifiedTheory.Audit.KFCausalClockFloorMixedProduct
open UnifiedTheory.Audit.KFCausalWeightedTensorRepresentative

variable (ε : ℝ) (hε : 0 < ε)

def mixedStraighten : ProductHilbert 2 4 ≃ₗᵢ[ℂ] ProductHilbert 2 4 :=
  (leftFourier 2 4).symm.trans ((straighten ε hε).trans (leftFourier 2 4))

def mixedWeight (x : Block 2 × Block 4) : ℂ :=
  (Real.sqrt (Real.exp (clockInverse ε hε x.2)+ε):ℂ)⁻¹

def fourierTest (a : C_c(Block 2, ℂ)) : BlockHilbert 2 :=
  (Lp.fourierTransformₗᵢ (Block 2) ℂ) (testState 2 a)

theorem fourierTest_dense : DenseRange fourierTest :=
  (Lp.fourierTransformₗᵢ (Block 2) ℂ).surjective.denseRange.comp
    (testState_dense 2) (Lp.fourierTransformₗᵢ (Block 2) ℂ).continuous

theorem mixedStraighten_test (a : C_c(Block 2, ℂ)) (b : C_c(Block 4, ℂ)) :
    mixedStraighten ε hε (productState volume volume (fourierTest a) (testState 4 b)) =ᵐ[volume]
      fun x => mixedWeight ε hε x*
        (productState volume volume (fourierTest a) (testState 4 b)) (mixedMap ε hε x) := by
  have ha1 : Integrable (a : Block 2 → ℂ) := a.continuous.integrable_of_hasCompactSupport a.hasCompactSupport
  have ha2 : MemLp (a : Block 2 → ℂ) 2 := a.continuous.memLp_of_hasCompactSupport a.hasCompactSupport
  have hb2 : MemLp (b : Block 4 → ℂ) 2 := b.continuous.memLp_of_hasCompactSupport b.hasCompactSupport
  have hp : productState volume volume (fourierTest a) (testState 4 b) =ᵐ[volume]
      fun x => (𝓕 (a : Block 2 → ℂ)) x.1*b x.2 := by
    have he := leftFourier_functions_coe 2 4 (a : Block 2 → ℂ) (b : Block 4 → ℂ) ha1 ha2 hb2
    rw [leftFourier_product] at he
    exact he
  have hu : mixedStraighten ε hε (productState volume volume (fourierTest a) (testState 4 b)) =
      leftFourier 2 4 (straighten ε hε (pairedProduct a ha2 b b.continuous b.hasCompactSupport)) := by
    change leftFourier 2 4 (straighten ε hε
      ((leftFourier 2 4).symm (productState volume volume (fourierTest a) (testState 4 b)))) = _
    rw [leftFourier_inverse_product]
    change leftFourier 2 4 (straighten ε hε
      (productState volume volume ((Lp.fourierTransformₗᵢ (Block 2) ℂ).symm
        ((Lp.fourierTransformₗᵢ (Block 2) ℂ) (testState 2 a))) (testState 4 b))) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
    rfl
  rw [hu]
  filter_upwards [mixed_product_coe ε hε a a.continuous ha1 ha2 b b.continuous b.hasCompactSupport,
    (mixedMap_quasiMeasurePreserving ε hε).ae hp] with x hx hp'
  rw [hx,hp']
  unfold mixedMap mixedWeight
  rw [mul_assoc]

theorem mixedStraighten_coe (f : ProductHilbert 2 4) :
    mixedStraighten ε hε f =ᵐ[volume] fun x => mixedWeight ε hε x*f (mixedMap ε hε x) :=
  tensor_representative 2 4 (mixedStraighten ε hε).toContinuousLinearEquiv.toContinuousLinearMap
    (mixedMap ε hε) (mixedMap_quasiMeasurePreserving ε hε) (mixedWeight ε hε)
    fourierTest (testState 4) fourierTest_dense (testState_dense 4) (mixedStraighten_test ε hε) f

theorem mixedStraighten_leftFourier (f : ProductHilbert 2 4) :
    mixedStraighten ε hε (leftFourier 2 4 f) = leftFourier 2 4 (straighten ε hε f) :=
  congrArg (fun g => leftFourier 2 4 (straighten ε hε g)) ((leftFourier 2 4).symm_apply_apply f)

theorem leftFourier_straighten_coe (f : ProductHilbert 2 4) :
    leftFourier 2 4 (straighten ε hε f) =ᵐ[volume]
      fun x => mixedWeight ε hε x*(leftFourier 2 4 f) (mixedMap ε hε x) := by
  rw [← mixedStraighten_leftFourier]
  exact mixedStraighten_coe ε hε _

theorem mixedFunction_memLp (f : ProductHilbert 2 4) :
    MemLp (fun x => mixedWeight ε hε x*f (mixedMap ε hε x)) 2 :=
  (Lp.memLp (mixedStraighten ε hε f)).ae_eq (mixedStraighten_coe ε hε f)

theorem mixedFunction_toLp (f : ProductHilbert 2 4) :
    (mixedFunction_memLp ε hε f).toLp (fun x => mixedWeight ε hε x*f (mixedMap ε hε x)) =
      mixedStraighten ε hε f := by
  apply Lp.ext
  exact (mixedFunction_memLp ε hε f).coeFn_toLp.trans (mixedStraighten_coe ε hε f).symm

#print axioms fourierTest_dense
#print axioms mixedStraighten_test
#print axioms mixedStraighten_coe
#print axioms mixedStraighten_leftFourier
#print axioms leftFourier_straighten_coe
#print axioms mixedFunction_memLp
#print axioms mixedFunction_toLp

end
end UnifiedTheory.Audit.KFCausalClockFloorMixedCoordinates
