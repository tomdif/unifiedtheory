/- General representatives of the physical paired chart, followed by exact
inverse-half-clock commutation for its antisymmetric partial Fourier unitary. -/
import UnifiedTheory.Audit.KFCausalShiftedPhysicalFourierSlices
import UnifiedTheory.Audit.KFCausalNarrowFourierInverseHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalPhysicalFourierGeneralCoordinates
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalMeasureUnitaryPullback
open KFCausalPhysicalMixedCoordinates
open KFCausalPairedModeCoordinates (modeIsometry mode_preserves_volume modePullback
  antisymmetric_coordinates symmetric_coordinates)
open KFCausalNarrowFourierInverseHalf (inverseProduct inverseProduct_coe inverseProduct_fourier)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalVacuumMixedClockNormalization (inverseHalf)
open KFCausalShiftedPhysicalFourierSlices (reconstruct)

abbrev Product := Block 2 × Block 4

def pairedChart : Configuration ≃ᵐ Product :=
  KFCausalEuclideanConfiguration.split.symm.trans
    (modeIsometry.toMeasurableEquiv.trans (KFCausalEuclideanProductCoordinates.split 2 4))

theorem pairedChart_preserves_volume : MeasurePreserving pairedChart :=
  ((KFCausalEuclideanProductCoordinates.split_preserves_volume 2 4).comp mode_preserves_volume).comp
    KFCausalEuclideanConfiguration.split_preserves_volume.symm

theorem pairedChart_apply (x : Configuration) :
    pairedChart x =
      (WithLp.toLp 2 ![KFCausalPairedModeCoordinates.scale*(x.2 0-x.2 1),
        KFCausalPairedModeCoordinates.scale*(x.2 2-x.2 3)],
       WithLp.toLp 2 ![x.1,KFCausalPairedModeCoordinates.scale*(x.2 0+x.2 1),
        KFCausalPairedModeCoordinates.scale*(x.2 2+x.2 3),x.2 4]) := by
  apply Prod.ext
  · rw [show (pairedChart x).1 =
      (KFCausalEuclideanProductCoordinates.split 2 4
        (modeIsometry (KFCausalEuclideanConfiguration.split.symm x))).1 from rfl,antisymmetric_coordinates]
    rfl
  · rw [show (pairedChart x).2 =
      (KFCausalEuclideanProductCoordinates.split 2 4
        (modeIsometry (KFCausalEuclideanConfiguration.split.symm x))).2 from rfl,symmetric_coordinates]
    rfl

theorem pairedChart_reconstruct (z : Product) : pairedChart (z.2 0,reconstruct z.1 z.2) = z := by
  rw [pairedChart_apply]
  apply Prod.ext
  · ext i
    fin_cases i
    · dsimp [reconstruct]
      linear_combination 2*(z.1 0)*KFCausalPairedModeCoordinates.scale_square
    · dsimp [reconstruct]
      linear_combination 2*(z.1 1)*KFCausalPairedModeCoordinates.scale_square
  · ext i
    fin_cases i
    · rfl
    · dsimp [reconstruct]
      linear_combination 2*(z.2 1)*KFCausalPairedModeCoordinates.scale_square
    · dsimp [reconstruct]
      linear_combination 2*(z.2 2)*KFCausalPairedModeCoordinates.scale_square
    · rfl

theorem pairedChart_symm (z : Product) : pairedChart.symm z = (z.2 0,reconstruct z.1 z.2) := by
  apply pairedChart.injective
  rw [pairedChart.apply_symm_apply,pairedChart_reconstruct]

theorem pairedCoordinates_coe (u : Hilbert) :
    pairedCoordinates u =ᵐ[volume] fun z : Product => u (z.2 0,reconstruct z.1 z.2) := by
  have h1 := unitaryPullback_symm_coe (KFCausalEuclideanProductCoordinates.split 2 4)
    (KFCausalEuclideanProductCoordinates.split_preserves_volume 2 4)
    (modePullback.symm (KFCausalEuclideanConfiguration.euclideanPullback u))
  have h2 := unitaryPullback_symm_coe modeIsometry.toMeasurableEquiv mode_preserves_volume
    (KFCausalEuclideanConfiguration.euclideanPullback u)
  have h3 := KFCausalEuclideanConfiguration.euclideanPullback_coe u
  filter_upwards [h1,
    (KFCausalEuclideanProductCoordinates.split_preserves_volume 2 4).symm.quasiMeasurePreserving.ae h2,
    (KFCausalEuclideanProductCoordinates.split_preserves_volume 2 4).symm.quasiMeasurePreserving.ae
      ((MeasurePreserving.symm modeIsometry.toMeasurableEquiv mode_preserves_volume).quasiMeasurePreserving.ae h3)] with z hz hmode hu
  have he := hz.trans (hmode.trans hu)
  change pairedCoordinates u z = u (pairedChart.symm z) at he
  simpa only [pairedChart_symm] using he

variable (ε : ℝ) (hε : 0 < ε)

theorem paired_inverse (f : Hilbert) :
    pairedCoordinates (inverseL ε hε f) = inverseProduct ε hε (pairedCoordinates f) := by
  have hi : inverseL ε hε f =ᵐ[volume] fun x => inverseHalf ε x.1*f x :=
    KFCausalClockFloorClockHalf.inverseAction_coe ε hε f
  have hp := pairedChart_preserves_volume.symm.quasiMeasurePreserving.ae hi
  apply Lp.ext
  filter_upwards [pairedCoordinates_coe (inverseL ε hε f),pairedCoordinates_coe f,
    inverseProduct_coe ε hε (pairedCoordinates f),hp] with z hz hf hr hi
  simp only [pairedChart_symm] at hi
  rw [hz,hr,hf]
  exact hi

theorem mixed_inverse (f : Hilbert) :
    mixedCoordinates (inverseL ε hε f) = inverseProduct ε hε (mixedCoordinates f) := by
  change KFCausalPartialFourier.leftFourier 2 4 (pairedCoordinates (inverseL ε hε f)) = _
  rw [paired_inverse,inverseProduct_fourier]
  rfl

theorem mixed_inverse_coe (f : Hilbert) :
    mixedCoordinates (inverseL ε hε f) =ᵐ[volume]
      fun z => inverseHalf ε (z.2 0)*(mixedCoordinates f) z := by
  rw [mixed_inverse]
  exact inverseProduct_coe ε hε _

#print axioms pairedChart_preserves_volume
#print axioms pairedChart_apply
#print axioms pairedChart_reconstruct
#print axioms pairedChart_symm
#print axioms pairedCoordinates_coe
#print axioms paired_inverse
#print axioms mixed_inverse
#print axioms mixed_inverse_coe
end
end UnifiedTheory.Audit.KFCausalPhysicalFourierGeneralCoordinates
