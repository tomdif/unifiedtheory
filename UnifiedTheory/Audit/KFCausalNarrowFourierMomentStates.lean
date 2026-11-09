/- Actual Hilbert states for first narrow and broad position moments,
identified in both physical and narrow Fourier coordinates. -/
import UnifiedTheory.Audit.KFCausalNarrowGaussianMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNarrowFourierMomentStates
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalEuclideanConfiguration (Space euclideanPullback euclideanPullback_coe)
open KFCausalPairedModeCoordinates (scale)
open KFCausalNarrowFourierCoordinates (pairedState mixedCoordinates pairedState_position_coe mixedCoordinates_functions_coe)
open KFCausalNarrowGaussianMoments
open KFCausalNarrowFourierPackets (spectator spectator_memLp configurationDensity coordinateDensity paired_density mixed_density)
open KFCausalReciprocalGaussianFourier (product product_memLp product_integrable)

def leftPositions (q : Transverse) : Block 2 := WithLp.toLp 2 ![scale*(q 0+q 1),scale*(q 2-q 3)]
def rightPositions (q : Transverse) : Block 2 := WithLp.toLp 2 ![scale*(q 0-q 1),scale*(q 2+q 3)]
def spectatorPositions (x : Configuration) : Block 4 :=
  WithLp.toLp 2 ![x.1,scale*(x.2 0-x.2 1),scale*(x.2 2+x.2 3),x.2 4]

theorem spectator_position (x : Configuration) (i : Fin 2) :
    spectatorPositions x i.castSucc.succ = rightPositions x.2 i := by fin_cases i <;> rfl

theorem paired_configuration_coe (f : Block 2 → ℂ) (g : Block 4 → ℂ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    pairedState (hf.toLp f) (hg.toLp g) =ᵐ[volume]
      fun x => f (leftPositions x.2)*g (spectatorPositions x) := by
  have hp := pairedState_position_coe f g hf hg
  have he : (fun x : Space => (pairedState (hf.toLp f) (hg.toLp g))
      (KFCausalEuclideanConfiguration.split x)) =ᵐ[volume]
      fun x => f (leftPositions (KFCausalEuclideanConfiguration.split x).2)*
        g (spectatorPositions (KFCausalEuclideanConfiguration.split x)) := by
    filter_upwards [euclideanPullback_coe (pairedState (hf.toLp f) (hg.toLp g)),hp] with x hx hp
    exact hx.symm.trans hp
  have ht := KFCausalEuclideanConfiguration.split_preserves_volume.symm.quasiMeasurePreserving.ae he
  filter_upwards [ht] with x hx
  simpa only [MeasurableEquiv.apply_symm_apply] using hx

variable (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 0 < w)
  (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)

def leftState (i : Fin 2) : Hilbert :=
  pairedState ((narrowMoment_memLp (α/w) (div_pos hα hw) i).toLp (narrowMoment (α/w) i))
    ((spectator_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg).toLp (spectator (α*w) β b P g))

def rightState (i : Fin 2) : Hilbert :=
  pairedState ((product_memLp (α/w) (α/w) (div_pos hα hw) (div_pos hα hw)).toLp (product (α/w) (α/w)))
    ((broadMoment_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg i).toLp (broadMoment (α*w) β b P g i))

theorem leftState_coe (i : Fin 2) :
    leftState α β w hα hβ hw b P g hc hg i =ᵐ[volume]
      fun x => (leftPositions x.2 i:ℂ)*configurationDensity α β w b P g x := by
  have hp := paired_configuration_coe (narrowMoment (α/w) i) (spectator (α*w) β b P g)
    (narrowMoment_memLp (α/w) (div_pos hα hw) i)
    (spectator_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg)
  filter_upwards [hp] with x hx
  rw [leftState,hx,narrowMoment_eq,mul_assoc]
  exact congrArg ((leftPositions x.2 i:ℂ)*·) (paired_density α β w b P g x)

theorem rightState_coe (i : Fin 2) :
    rightState α β w hα hβ hw b P g hc hg i =ᵐ[volume]
      fun x => (rightPositions x.2 i:ℂ)*configurationDensity α β w b P g x := by
  have hp := paired_configuration_coe (product (α/w) (α/w)) (broadMoment (α*w) β b P g i)
    (product_memLp (α/w) (α/w) (div_pos hα hw) (div_pos hα hw))
    (broadMoment_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg i)
  filter_upwards [hp] with x hx
  rw [rightState,hx,broadMoment,spectator_position,mul_left_comm]
  exact congrArg ((rightPositions x.2 i:ℂ)*·) (paired_density α β w b P g x)

theorem leftState_coordinates_coe (i : Fin 2) :
    mixedCoordinates (leftState α β w hα hβ hw b P g hc hg i) =ᵐ[volume]
      fun z => (-(Real.pi:ℂ)*Complex.I*(z.1 i:ℂ)/(α/w:ℝ))*coordinateDensity α β w b P g z := by
  have hp := mixedCoordinates_functions_coe (narrowMoment (α/w) i) (spectator (α*w) β b P g)
    (narrowMoment_integrable (α/w) (div_pos hα hw) i)
    (narrowMoment_memLp (α/w) (div_pos hα hw) i)
    (spectator_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg)
  filter_upwards [hp] with z hz
  rw [leftState,hz,narrowMoment_fourier _ (div_pos hα hw),mul_assoc,mixed_density α β w hα hw b P g z]

theorem rightState_coordinates_coe (i : Fin 2) :
    mixedCoordinates (rightState α β w hα hβ hw b P g hc hg i) =ᵐ[volume]
      fun z => (z.2 i.castSucc.succ:ℂ)*coordinateDensity α β w b P g z := by
  have hp := mixedCoordinates_functions_coe (product (α/w) (α/w)) (broadMoment (α*w) β b P g i)
    (product_integrable (α/w) (α/w) (div_pos hα hw) (div_pos hα hw))
    (product_memLp (α/w) (α/w) (div_pos hα hw) (div_pos hα hw))
    (broadMoment_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg i)
  filter_upwards [hp] with z hz
  rw [rightState,hz,broadMoment,mul_left_comm,mixed_density α β w hα hw b P g z]

#print axioms spectator_position
#print axioms paired_configuration_coe
#print axioms leftState_coe
#print axioms rightState_coe
#print axioms leftState_coordinates_coe
#print axioms rightState_coordinates_coe
end
end UnifiedTheory.Audit.KFCausalNarrowFourierMomentStates
