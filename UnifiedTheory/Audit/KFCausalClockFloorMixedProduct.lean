/- The actual clock straightening followed by partial Fourier transform
on coupled product test states. All L1/L2 and compact-support requirements
are proved from the input factors. The antisymmetric Fourier Jacobian
cancels the transverse clock weight, leaving the explicit clock half-weight. -/
import UnifiedTheory.Audit.KFCausalClockFloorPairedStraightening
import UnifiedTheory.Audit.KFCausalPartialFourierDilation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorMixedProduct
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block ProductHilbert productState_functions_coe)
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding (productState)
open UnifiedTheory.Audit.KFCausalPartialFourier (leftFourier)
open UnifiedTheory.Audit.KFCausalPartialFourierIntegral (leftFourier_toLp_coe)
open UnifiedTheory.Audit.KFCausalPartialFourierDilation
open UnifiedTheory.Audit.KFCausalClockFloorPairedStraightening
open UnifiedTheory.Audit.KFCausalClockFloorSpectatorChart (backward)

variable (ε : ℝ) (hε : 0 < ε)

def pairedProduct (a : Block 2 → ℂ) (ha : MemLp a 2)
    (b : Block 4 → ℂ) (hb : Continuous b) (hbc : HasCompactSupport b) : ProductHilbert 2 4 :=
  productState volume volume (ha.toLp a) ((hb.memLp_of_hasCompactSupport hbc).toLp b)

def straightenedFunction (a : Block 2 → ℂ) (b : Block 4 → ℂ) : Block 2 × Block 4 → ℂ :=
  scaledProduct 2 4 a (dilation ε hε) (weightedSpectator ε hε b)

theorem straighten_product_coe (a : Block 2 → ℂ) (ha : MemLp a 2)
    (b : Block 4 → ℂ) (hb : Continuous b) (hbc : HasCompactSupport b) :
    straighten ε hε (pairedProduct a ha b hb hbc) =ᵐ[volume] straightenedFunction ε hε a b := by
  filter_upwards [straighten_coe ε hε (pairedProduct a ha b hb hbc),
    (inverseMap_quasiMeasurePreserving ε hε).ae
      (productState_functions_coe 2 4 a b ha (hb.memLp_of_hasCompactSupport hbc))] with x hs hp
  change pairedProduct a ha b hb hbc (inverseMap ε hε x) = _ at hp
  rw [hs,hp,inverseMap_apply]
  unfold straightenedFunction scaledProduct weightedSpectator
  ring

theorem straightened_memLp (a : Block 2 → ℂ) (ha : MemLp a 2)
    (b : Block 4 → ℂ) (hb : Continuous b) (hbc : HasCompactSupport b) :
    MemLp (straightenedFunction ε hε a b) 2 :=
  (Lp.memLp (straighten ε hε (pairedProduct a ha b hb hbc))).ae_eq
    (straighten_product_coe ε hε a ha b hb hbc)

theorem straighten_product (a : Block 2 → ℂ) (ha : MemLp a 2)
    (b : Block 4 → ℂ) (hb : Continuous b) (hbc : HasCompactSupport b) :
    straighten ε hε (pairedProduct a ha b hb hbc) =
      (straightened_memLp ε hε a ha b hb hbc).toLp (straightenedFunction ε hε a b) := by
  apply Lp.ext
  exact (straighten_product_coe ε hε a ha b hb hbc).trans
    (straightened_memLp ε hε a ha b hb hbc).coeFn_toLp.symm

theorem straightened_continuous (a : Block 2 → ℂ) (ha : Continuous a)
    (b : Block 4 → ℂ) (hb : Continuous b) : Continuous (straightenedFunction ε hε a b) :=
  scaledProduct_continuous 2 4 a ha _ (dilation_continuous ε hε) _
    (weightedSpectator_continuous ε hε b hb)

theorem straightened_integrable (a : Block 2 → ℂ) (ha : Continuous a) (ha1 : Integrable a)
    (b : Block 4 → ℂ) (hb : Continuous b) (hbc : HasCompactSupport b) :
    Integrable (straightenedFunction ε hε a b) :=
  scaledProduct_integrable 2 4 a ha ha1 _ (dilation_continuous ε hε) (dilation_positive ε hε) _
    (weightedSpectator_continuous ε hε b hb) (weightedSpectator_compact ε hε b hbc)

theorem mixed_product_coe (a : Block 2 → ℂ) (ha : Continuous a) (ha1 : Integrable a) (ha2 : MemLp a 2)
    (b : Block 4 → ℂ) (hb : Continuous b) (hbc : HasCompactSupport b) :
    leftFourier 2 4 (straighten ε hε (pairedProduct a ha2 b hb hbc)) =ᵐ[volume] fun x =>
      (Real.sqrt (Real.exp (clockInverse ε hε x.2)+ε):ℂ)⁻¹*
        (𝓕 a) ((dilation ε hε x.2)⁻¹ • x.1)*b (backward ε hε x.2) := by
  rw [straighten_product]
  filter_upwards [leftFourier_toLp_coe 2 4 (straightenedFunction ε hε a b)
    (straightened_continuous ε hε a ha b hb) (straightened_integrable ε hε a ha ha1 b hb hbc)
    (straightened_memLp ε hε a ha2 b hb hbc)] with x hx
  rw [hx]
  change KFCausalPartialFourierSlices.leftIntegral 2 4
    (scaledProduct 2 4 a (dilation ε hε) (weightedSpectator ε hε b)) x = _
  rw [leftIntegral_scaledProduct 2 4 a _ (dilation_positive ε hε)]
  have hj := jacobian_cancel ε hε x.2
  simp only [Complex.real_smul] at hj ⊢
  unfold weightedSpectator
  calc
    _ = ((((dilation ε hε x.2)^2)⁻¹:ℝ):ℂ)*inverseWeight ε hε x.2*
        (𝓕 a) ((dilation ε hε x.2)⁻¹ • x.1)*b (backward ε hε x.2) := by ring
    _ = _ := by rw [hj]

#print axioms straighten_product_coe
#print axioms straightened_memLp
#print axioms straighten_product
#print axioms straightened_continuous
#print axioms straightened_integrable
#print axioms mixed_product_coe

end
end UnifiedTheory.Audit.KFCausalClockFloorMixedProduct
