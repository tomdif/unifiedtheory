/- General representatives for the existing paired coordinates, and a
clock-preserving coordinate permutation for the joint Fourier estimates. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierCoordinates
import UnifiedTheory.Audit.KFCausalShiftedNarrowJointGaussian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalNarrowFourierGeneralCoordinates
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalMeasureUnitaryPullback
open KFCausalNarrowFourierCoordinates
open KFCausalShiftedNarrowFourierGeometry (reconstruct)
open KFCausalShiftedNarrowJointGaussian (narrow spectator)

abbrev Product := Block 2 × Block 4

def pairedChart : Configuration ≃ᵐ Product :=
  KFCausalEuclideanConfiguration.split.symm.trans
    (modeIsometry.toMeasurableEquiv.trans (KFCausalEuclideanProductCoordinates.split 2 4))

theorem pairedChart_preserves_volume : MeasurePreserving pairedChart :=
  ((KFCausalEuclideanProductCoordinates.split_preserves_volume 2 4).comp mode_preserves_volume).comp
    KFCausalEuclideanConfiguration.split_preserves_volume.symm

theorem pairedChart_apply (x : Configuration) :
    pairedChart x =
      (WithLp.toLp 2 ![KFCausalPairedModeCoordinates.scale*(x.2 0+x.2 1),
        KFCausalPairedModeCoordinates.scale*(x.2 2-x.2 3)],
       WithLp.toLp 2 ![x.1,KFCausalPairedModeCoordinates.scale*(x.2 0-x.2 1),
        KFCausalPairedModeCoordinates.scale*(x.2 2+x.2 3),x.2 4]) := by
  apply Prod.ext
  · rw [show (pairedChart x).1 =
      (KFCausalEuclideanProductCoordinates.split 2 4
        (modeIsometry (KFCausalEuclideanConfiguration.split.symm x))).1 from rfl,narrow_coordinates]
    rfl
  · rw [show (pairedChart x).2 =
      (KFCausalEuclideanProductCoordinates.split 2 4
        (modeIsometry (KFCausalEuclideanConfiguration.split.symm x))).2 from rfl,spectator_coordinates]
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

def frequencyIndex : Fin 2 ⊕ Fin 4 ≃ Fin 6 :=
  (finSumFinEquiv).trans ((Equiv.swap 0 1).trans (Equiv.swap 0 2))

def frequencyIsometry : KFCausalEuclideanConfiguration.Space ≃ₗᵢ[ℝ]
    KFCausalEuclideanProductCoordinates.Joint 2 4 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ frequencyIndex.symm

def frequencyChart : Configuration ≃ᵐ Product :=
  KFCausalEuclideanConfiguration.split.symm.trans
    (frequencyIsometry.toMeasurableEquiv.trans (KFCausalEuclideanProductCoordinates.split 2 4))

theorem frequencyChart_preserves_volume : MeasurePreserving frequencyChart :=
  ((KFCausalEuclideanProductCoordinates.split_preserves_volume 2 4).comp
    frequencyIsometry.measurePreserving).comp KFCausalEuclideanConfiguration.split_preserves_volume.symm

theorem frequencyChart_apply (x : Configuration) : frequencyChart x = (narrow x,spectator x) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [frequencyChart,frequencyIsometry,frequencyIndex,
      LinearIsometryEquiv.piLpCongrLeft,MeasurableEquiv.trans_apply,
      KFCausalEuclideanProductCoordinates.split_fst,Equiv.swap_apply_def,finSumFinEquiv,narrow] <;> rfl
  · ext i
    fin_cases i <;> simp [frequencyChart,frequencyIsometry,frequencyIndex,
      LinearIsometryEquiv.piLpCongrLeft,MeasurableEquiv.trans_apply,
      KFCausalEuclideanProductCoordinates.split_snd,Equiv.swap_apply_def,finSumFinEquiv,spectator] <;> rfl

def frequencyUnpack (z : Product) : Configuration := (z.2 0,![z.1 0,z.1 1,z.2 1,z.2 2,z.2 3])

theorem frequencyChart_symm (z : Product) : frequencyChart.symm z = frequencyUnpack z := by
  apply frequencyChart.injective
  rw [frequencyChart.apply_symm_apply,frequencyChart_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> rfl
  · ext i
    fin_cases i <;> rfl

def frequencyCoordinates : Hilbert ≃ₗᵢ[ℂ] ProductHilbert 2 4 :=
  (unitaryPullback frequencyChart frequencyChart_preserves_volume).symm

theorem frequencyCoordinates_coe (u : Hilbert) :
    frequencyCoordinates u =ᵐ[volume] u ∘ frequencyUnpack := by
  simpa only [Function.comp_def,frequencyChart_symm] using
    unitaryPullback_symm_coe frequencyChart frequencyChart_preserves_volume u

#print axioms pairedChart_preserves_volume
#print axioms pairedChart_apply
#print axioms pairedChart_reconstruct
#print axioms pairedChart_symm
#print axioms pairedCoordinates_coe
#print axioms frequencyChart_preserves_volume
#print axioms frequencyChart_apply
#print axioms frequencyChart_symm
#print axioms frequencyCoordinates_coe
end
end UnifiedTheory.Audit.KFCausalNarrowFourierGeneralCoordinates
