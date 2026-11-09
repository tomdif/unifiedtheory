/- Relate the five-transverse Fourier coordinates used by the actual static
Hamiltonian to four charged coordinates and clock/neutral spectators. -/
import UnifiedTheory.Audit.KFCausalJoinedFourierProduct
import UnifiedTheory.Audit.KFCausalChargedSpectatorCoordinates
import UnifiedTheory.Audit.KFCausalChargeTransverseSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalSpectatorFourierCoordinates
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalHermiteProductBasis (joinCoordinates)
open KFCausalMeasureUnitaryPullback
open KFCausalL2TensorEmbedding (productState productState_coe)
open KFCausalJoinedFourierProduct (separate separate_preserves join_product_coe)

def reorder : Block 5 ≃ₗᵢ[ℝ] Block 5 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (1:Fin 5) 2)

theorem reorder_apply (x : Block 5) : reorder x = WithLp.toLp 2 ![x 0,x 2,x 1,x 3,x 4] := by
  ext i
  fin_cases i <;> norm_num [reorder, LinearIsometryEquiv.piLpCongrLeft, Equiv.swap_apply_def]
  all_goals exact congrArg x (by decide)

def fiveState (f : BlockHilbert 4) (v : BlockHilbert 1) : BlockHilbert 5 :=
  KFCausalL2FourierIsometry.pullback reorder (joinCoordinates 4 1 (productState volume volume f v))

theorem fiveState_coe (f : BlockHilbert 4) (v : BlockHilbert 1) :
    fiveState f v =ᵐ[volume] fun x =>
      f (WithLp.toLp 2 ![x 0,x 2,x 1,x 3])*v (WithLp.toLp 2 ![x 4]) := by
  unfold fiveState
  filter_upwards [KFCausalL2FourierIsometry.pullback_coe reorder
      (joinCoordinates 4 1 (productState volume volume f v)),
    reorder.measurePreserving.quasiMeasurePreserving.ae (join_product_coe 4 1 f v)]
      with x hx hy
  rw [hx]
  change (joinCoordinates 4 1 (productState volume volume f v)) (reorder x) = _
  rw [hy]
  have h0 : (separate 4 1 (reorder x)).1 = WithLp.toLp 2 ![x 0,x 2,x 1,x 3] := by
    rw [reorder_apply]
    ext i
    fin_cases i <;> rfl
  have h1 : (separate 4 1 (reorder x)).2 = WithLp.toLp 2 ![x 4] := by
    rw [reorder_apply]
    ext i
    fin_cases i <;> rfl
  rw [h0, h1]

theorem fiveState_fourier (f : BlockHilbert 4) (v : BlockHilbert 1) :
    (Lp.fourierTransformₗᵢ (Block 5) ℂ) (fiveState f v) =
      fiveState ((Lp.fourierTransformₗᵢ (Block 4) ℂ) f)
        ((Lp.fourierTransformₗᵢ (Block 1) ℂ) v) := by
  unfold fiveState
  rw [KFCausalL2FourierIsometry.fourier_pullback,
    KFCausalJoinedFourierProduct.join_fourier_product 4 1 f v]

def regroup : (Block 4 × Block 2) ≃ᵐ (Block 5 × Block 1) :=
  KFCausalChargedSpectatorCoordinates.assemble.trans
    (KFCausalChargeTransverseSplit.repackIsometry.toMeasurableEquiv.trans (split 5 1))

theorem regroup_preserves : MeasurePreserving regroup :=
  ((split_preserves_volume 5 1).comp
    KFCausalChargeTransverseSplit.repackIsometry.measurePreserving).comp
      KFCausalChargedSpectatorCoordinates.assemble_preserves

theorem regroup_apply (x : Block 4 × Block 2) :
    regroup x = (WithLp.toLp 2 ![x.1 0,x.1 2,x.1 1,x.1 3,x.2 1],
      WithLp.toLp 2 ![x.2 0]) := by
  apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

def regroupPullback : ProductHilbert 5 1 ≃ₗᵢ[ℂ] ProductHilbert 4 2 :=
  unitaryPullback regroup regroup_preserves

theorem regroup_product (f : BlockHilbert 4) (u v : BlockHilbert 1) :
    regroupPullback (productState volume volume (fiveState f v) u) =
      productState volume volume f (joinCoordinates 1 1 (productState volume volume u v)) := by
  unfold regroupPullback
  apply Lp.ext
  filter_upwards [unitaryPullback_coe regroup regroup_preserves
      (productState volume volume (fiveState f v) u),
    regroup_preserves.quasiMeasurePreserving.ae (productState_coe volume volume (fiveState f v) u),
    (Measure.quasiMeasurePreserving_fst.comp regroup_preserves.quasiMeasurePreserving).ae
      (fiveState_coe f v),
    productState_coe volume volume f (joinCoordinates 1 1 (productState volume volume u v)),
    Measure.quasiMeasurePreserving_snd.ae (join_product_coe 1 1 u v)] with x hp hq hf hr hs
  rw [hp]
  change (productState volume volume (fiveState f v) u) (regroup x) = _
  simp only [Function.comp_apply] at hf
  rw [hq, hf, hr, hs]
  simp only [regroup_apply, WithLp.toLp_ofLp, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]
  have h4 : WithLp.toLp 2 ![x.1 0,x.1 1,x.1 2,x.1 3] = x.1 := by
    ext i
    fin_cases i <;> rfl
  have hu : (separate 1 1 x.2).1 = WithLp.toLp 2 ![x.2 0] := by
    ext i
    fin_cases i <;> rfl
  have hv : (separate 1 1 x.2).2 = WithLp.toLp 2 ![x.2 1] := by
    ext i
    fin_cases i <;> rfl
  rw [h4, hu, hv]
  ring

theorem regroup_coordinates (f : JointHilbert 2 4) :
    regroupPullback (KFCausalChargeTransverseSplit.transverseCoordinates f) =
      KFCausalChargedSpectatorCoordinates.mixedCoordinates f := by
  apply Lp.ext
  filter_upwards [unitaryPullback_coe regroup regroup_preserves
      (KFCausalChargeTransverseSplit.transverseCoordinates f),
    regroup_preserves.quasiMeasurePreserving.ae
      (unitaryPullback_symm_coe (split 5 1) (split_preserves_volume 5 1)
        (KFCausalChargeTransverseSplit.repackPullback.symm f)),
    ((split_preserves_volume 5 1).symm.comp regroup_preserves).quasiMeasurePreserving.ae
      (unitaryPullback_symm_coe KFCausalChargeTransverseSplit.repackIsometry.toMeasurableEquiv
        KFCausalChargeTransverseSplit.repackIsometry.measurePreserving f),
    KFCausalChargedSpectatorCoordinates.mixedCoordinates_coe f] with x h1 h2 h3 h4
  have he : KFCausalChargeTransverseSplit.repackIsometry.toMeasurableEquiv.symm
      ((split 5 1).symm (regroup x)) = KFCausalChargedSpectatorCoordinates.assemble x := by
    simp only [regroup, MeasurableEquiv.trans_apply, MeasurableEquiv.symm_apply_apply]
  exact (h1.trans (h2.trans (h3.trans (congrArg f he)))).trans h4.symm


theorem transverse_product (f : BlockHilbert 4) (u v : BlockHilbert 1) :
    KFCausalChargeTransverseSplit.transverseCoordinates
      (KFCausalChargedSpectatorCoordinates.mixedCoordinates.symm
        (productState volume volume f (joinCoordinates 1 1 (productState volume volume u v)))) =
      productState volume volume (fiveState f v) u := by
  apply regroupPullback.injective
  rw [regroup_coordinates, LinearIsometryEquiv.apply_symm_apply, regroup_product]

def spectralRepack : JointHilbert 5 1 ≃ₗᵢ[ℂ] ProductHilbert 4 2 :=
  (coordinates 5 1).symm.trans regroupPullback

theorem dual_triple (f : BlockHilbert 4) (u v : BlockHilbert 1) :
    spectralRepack (KFCausalChargeTransverseSplit.dualMixed
      (KFCausalChargedSpectatorCoordinates.mixedCoordinates.symm
        (productState volume volume f (joinCoordinates 1 1 (productState volume volume u v))))) =
      productState volume volume ((Lp.fourierTransformₗᵢ (Block 4) ℂ) f)
        (joinCoordinates 1 1 (productState volume volume u
          ((Lp.fourierTransformₗᵢ (Block 1) ℂ) v))) := by
  change regroupPullback ((coordinates 5 1).symm
    (coordinates 5 1 (KFCausalPartialFourier.leftFourier 5 1
      (KFCausalChargeTransverseSplit.transverseCoordinates _)))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, transverse_product,
    KFCausalPartialFourier.leftFourier_product, fiveState_fourier, regroup_product]

theorem dual_physical_triple (f : BlockHilbert 4) (u v : BlockHilbert 1) :
    spectralRepack (KFCausalChargeTransverseSplit.dualPhysical
      (KFCausalChargedSpectatorCoordinates.physicalCoordinates.symm
        (productState volume volume f (joinCoordinates 1 1 (productState volume volume u v))))) =
      productState volume volume ((Lp.fourierTransformₗᵢ (Block 4) ℂ) f)
        (joinCoordinates 1 1 (productState volume volume u
          ((Lp.fourierTransformₗᵢ (Block 1) ℂ) v))) := by
  simpa only [KFCausalChargedSpectatorCoordinates.physicalCoordinates,
    KFCausalChargeTransverseSplit.dualPhysical, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.apply_symm_apply] using
      dual_triple f u v

#print axioms fiveState_fourier
#print axioms regroup_product
#print axioms dual_physical_triple
end
end UnifiedTheory.Audit.KFCausalSpectatorFourierCoordinates
