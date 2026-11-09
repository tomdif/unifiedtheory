/- The actual pure-clock unitary commutes with the partial Fourier
transform, proved on product states and extended by the proved L2 density.
No identification of the physical charge action is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockPairedCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockPartialFourier
noncomputable section
open MeasureTheory
open scoped CompactlySupported
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding (productState)
open UnifiedTheory.Audit.KFCausalPartialFourier
open UnifiedTheory.Audit.KFCausalEuclideanTensorUnitary (equal_on_products)
open UnifiedTheory.Audit.KFCausalWeightedTensorRepresentative
open UnifiedTheory.Audit.KFCausalClockFloorPureClockPairedCoordinates

variable (ε : ℝ) (hε : 0 < ε)

def rightState (b : C_c(Block 4, ℂ)) : BlockHilbert 4 :=
  ((weightedRight_continuous ε b b.continuous).memLp_of_hasCompactSupport
    (weightedRight_compact ε hε b b.hasCompactSupport)).toLp (weightedRight ε b)

theorem paired_product (a : BlockHilbert 2) (b : C_c(Block 4, ℂ)) :
    pairedUnitary ε hε (productState volume volume a (testState 4 b)) =
      productState volume volume a (rightState ε hε b) := by
  have hp : productState volume volume a (testState 4 b) =ᵐ[volume]
      fun x => a x.1*b x.2 := by
    simpa only [Lp.toLp_coeFn] using productState_functions_coe 2 4 a b (Lp.memLp a)
      (b.continuous.memLp_of_hasCompactSupport b.hasCompactSupport)
  have hq : productState volume volume a (rightState ε hε b) =ᵐ[volume]
      fun x => a x.1*weightedRight ε b x.2 := by
    simpa only [Lp.toLp_coeFn] using productState_functions_coe 2 4 a (weightedRight ε b) (Lp.memLp a)
      ((weightedRight_continuous ε b b.continuous).memLp_of_hasCompactSupport
        (weightedRight_compact ε hε b b.hasCompactSupport))
  apply Lp.ext
  filter_upwards [pairedUnitary_coe ε hε (productState volume volume a (testState 4 b)),
    (pairedMap_quasiMeasurePreserving ε hε).ae hp,hq] with x hu hp' hq'
  rw [hu,hp',hq',pairedMap_apply]
  simp only [weightedRight]
  ring

theorem partialFourier_commutes (f : ProductHilbert 2 4) :
    leftFourier 2 4 (pairedUnitary ε hε f) = pairedUnitary ε hε (leftFourier 2 4 f) := by
  let P : ProductHilbert 2 4 →L[ℂ] ProductHilbert 2 4 :=
    (leftFourier 2 4 : ProductHilbert 2 4 →L[ℂ] ProductHilbert 2 4).comp (pairedUnitary ε hε : ProductHilbert 2 4 →L[ℂ] ProductHilbert 2 4)
  let Q : ProductHilbert 2 4 →L[ℂ] ProductHilbert 2 4 :=
    (pairedUnitary ε hε : ProductHilbert 2 4 →L[ℂ] ProductHilbert 2 4).comp (leftFourier 2 4 : ProductHilbert 2 4 →L[ℂ] ProductHilbert 2 4)
  have he : P = Q := by
    apply equal_on_products 2 4
    intro a b
    have ht : (fun z : BlockHilbert 4 => P (productState volume volume a z)) =
        (fun z : BlockHilbert 4 => Q (productState volume volume a z)) := by
      apply (testState_dense 4).equalizer
        (P.continuous.comp (rightProduct 2 4 a).continuous)
        (Q.continuous.comp (rightProduct 2 4 a).continuous)
      funext z
      change leftFourier 2 4 (pairedUnitary ε hε (productState volume volume a (testState 4 z))) =
        pairedUnitary ε hε (leftFourier 2 4 (productState volume volume a (testState 4 z)))
      rw [paired_product,leftFourier_product,leftFourier_product,paired_product]
    exact congrFun ht b
  exact congrArg (fun A : ProductHilbert 2 4 →L[ℂ] ProductHilbert 2 4 => A f) he

#print axioms paired_product
#print axioms partialFourier_commutes
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockPartialFourier
