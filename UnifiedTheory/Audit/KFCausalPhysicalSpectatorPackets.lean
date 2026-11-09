/- Physical charged packets with clock position and neutral Fourier frequency. -/
import UnifiedTheory.Audit.KFCausalFreeHamiltonianCoordinates
import UnifiedTheory.Audit.KFCausalCircularChargeTransform
import UnifiedTheory.Audit.KFCausalJoinedMultiplierSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalPhysicalSpectatorPackets
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates
open KFCausalL2TensorEmbedding
open KFCausalJoinedMultiplierSum (joinProduct)
open KFCausalChargedSpectatorCoordinates (physicalCoordinates)
open KFCausalFreeHamiltonianCoordinates (dualCoordinates)

def one (s : ℝ) : Block 1 := WithLp.toLp 2 ![s]

def triple (f : BlockHilbert 4) (u v : BlockHilbert 1) : ProductHilbert 4 2 :=
  productState volume volume f (joinProduct 1 1 u v)

theorem triple_coe (f : BlockHilbert 4) (u v : BlockHilbert 1) :
    triple f u v =ᵐ[volume] fun x => f x.1*u (one (x.2 0))*v (one (x.2 1)) := by
  filter_upwards [productState_coe volume volume f (joinProduct 1 1 u v),
    Measure.quasiMeasurePreserving_snd.ae
      (KFCausalJoinedFourierProduct.join_product_coe 1 1 u v)] with x h1 h2
  change (productState volume volume f (joinProduct 1 1 u v)) x = _
  rw [h1]
  unfold joinProduct
  rw [h2]
  have hs : KFCausalJoinedFourierProduct.separate 1 1 x.2 = (one (x.2 0),one (x.2 1)) := by
    apply Prod.ext <;> ext j <;> fin_cases j <;> rfl
  rw [hs]
  ring

def packet (f : BlockHilbert 4) (u v : BlockHilbert 1) : Hilbert :=
  physicalCoordinates.symm (triple f u ((Lp.fourierTransformₗᵢ (Block 1) ℂ).symm v))

theorem position_packet (f : BlockHilbert 4) (u v : BlockHilbert 1) :
    physicalCoordinates (packet f u v) =
      triple f u ((Lp.fourierTransformₗᵢ (Block 1) ℂ).symm v) :=
  physicalCoordinates.apply_symm_apply _

theorem dual_packet (f : BlockHilbert 4) (u v : BlockHilbert 1) :
    dualCoordinates (packet f u v) = triple ((Lp.fourierTransformₗᵢ (Block 4) ℂ) f) u v := by
  exact (KFCausalSpectatorFourierCoordinates.dual_physical_triple f u
    ((Lp.fourierTransformₗᵢ (Block 1) ℂ).symm v)).trans
      (by rw [LinearIsometryEquiv.apply_symm_apply]; rfl)

theorem packet_add_left (f g : BlockHilbert 4) (u v : BlockHilbert 1) :
    packet (f+g) u v = packet f u v+packet g u v := by
  simp only [packet, triple, productState_add_left, map_add]

theorem packet_smul_left (a : ℂ) (f : BlockHilbert 4) (u v : BlockHilbert 1) :
    packet (a • f) u v = a • packet f u v := by
  simp only [packet, triple, productState_smul_left, map_smul]

theorem circular_packet (h : ℝ) (hh : h ≠ 0) (b : ℝ) (hb : 0 < b)
    (i : KFCausalHermiteProductBasis.Index) (u v : BlockHilbert 1) :
    packet (KFCausalFourCircularChargeBasis.basis
      (KFCausalNormalizedChargeFlow.momentumScale h)
      (KFCausalNormalizedChargeFlow.momentumScale_ne_zero h hh) b hb i) u v =
      KFCausalCircularChargeTransform.packet h hh b hb i (joinProduct 1 1 u v) := by
  apply (KFCausalCircularChargeTransform.transform h hh b hb).injective
  rw [KFCausalCircularChargeTransform.transform_packet]
  unfold KFCausalCircularChargeTransform.transform
  simp only [LinearIsometryEquiv.trans_apply, position_packet]
  unfold triple
  rw [KFCausalJointHermiteFourierTransform.neutralFourier_product]
  have he : KFCausalJointHermiteFourierTransform.neutralFourierBlock
      (joinProduct 1 1 u ((Lp.fourierTransformₗᵢ (Block 1) ℂ).symm v)) = joinProduct 1 1 u v := by
    unfold KFCausalJointHermiteFourierTransform.neutralFourierBlock joinProduct
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply,
      KFCausalPartialFourier.rightFourier_product, LinearIsometryEquiv.apply_symm_apply]
  rw [he, KFCausalProductHilbertExpansion.partialTransform_column]

#print axioms dual_packet
#print axioms circular_packet
end
end UnifiedTheory.Audit.KFCausalPhysicalSpectatorPackets
