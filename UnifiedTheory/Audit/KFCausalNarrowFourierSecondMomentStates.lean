/- Actual second-position moment states, with physical and transformed
representatives. These are constructed L2 vectors, not domain assumptions. -/
import UnifiedTheory.Audit.KFCausalNarrowGaussianSecondMoments
import UnifiedTheory.Audit.KFCausalNarrowFourierMomentStates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNarrowFourierSecondMomentStates
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
open KFCausalNarrowGaussianSecondMoments
open KFCausalNarrowFourierMomentStates (leftPositions rightPositions spectatorPositions spectator_position paired_configuration_coe)
open KFCausalNarrowFourierPackets (spectator spectator_memLp configurationDensity coordinateDensity paired_density mixed_density)
open KFCausalReciprocalGaussianFourier (product product_memLp product_integrable)

variable (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 0 < w)
  (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)

def leftSquareState (i : Fin 2) : Hilbert :=
  pairedState ((narrowSquare_memLp (α/w) (div_pos hα hw) i).toLp (narrowSquare (α/w) i))
    ((spectator_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg).toLp (spectator (α*w) β b P g))

def rightSquareState (i : Fin 2) : Hilbert :=
  pairedState ((product_memLp (α/w) (α/w) (div_pos hα hw) (div_pos hα hw)).toLp (product (α/w) (α/w)))
    ((broadSquare_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg i).toLp (broadSquare (α*w) β b P g i))

theorem leftSquareState_coe (i : Fin 2) :
    leftSquareState α β w hα hβ hw b P g hc hg i =ᵐ[volume]
      fun x => (leftPositions x.2 i:ℂ)^2*configurationDensity α β w b P g x := by
  have hp := paired_configuration_coe (narrowSquare (α/w) i) (spectator (α*w) β b P g)
    (narrowSquare_memLp (α/w) (div_pos hα hw) i)
    (spectator_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg)
  filter_upwards [hp] with x hx
  rw [leftSquareState,hx,narrowSquare_eq,mul_assoc]
  exact congrArg ((leftPositions x.2 i:ℂ)^2*·) (paired_density α β w b P g x)

theorem rightSquareState_coe (i : Fin 2) :
    rightSquareState α β w hα hβ hw b P g hc hg i =ᵐ[volume]
      fun x => (rightPositions x.2 i:ℂ)^2*configurationDensity α β w b P g x := by
  have hp := paired_configuration_coe (product (α/w) (α/w)) (broadSquare (α*w) β b P g i)
    (product_memLp (α/w) (α/w) (div_pos hα hw) (div_pos hα hw))
    (broadSquare_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg i)
  filter_upwards [hp] with x hx
  rw [rightSquareState,hx,broadSquare,spectator_position,mul_left_comm]
  exact congrArg ((rightPositions x.2 i:ℂ)^2*·) (paired_density α β w b P g x)

theorem leftSquareState_coordinates_coe (i : Fin 2) :
    mixedCoordinates (leftSquareState α β w hα hβ hw b P g hc hg i) =ᵐ[volume]
      fun z => (1/(2*(α/w:ℝ))-(Real.pi:ℂ)^2*(z.1 i:ℂ)^2/(α/w:ℝ)^2)*coordinateDensity α β w b P g z := by
  have hp := mixedCoordinates_functions_coe (narrowSquare (α/w) i) (spectator (α*w) β b P g)
    (narrowSquare_integrable (α/w) (div_pos hα hw) i)
    (narrowSquare_memLp (α/w) (div_pos hα hw) i)
    (spectator_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg)
  filter_upwards [hp] with z hz
  rw [leftSquareState,hz,narrowSquare_fourier _ (div_pos hα hw),mul_assoc,mixed_density α β w hα hw b P g z]

theorem rightSquareState_coordinates_coe (i : Fin 2) :
    mixedCoordinates (rightSquareState α β w hα hβ hw b P g hc hg i) =ᵐ[volume]
      fun z => (z.2 i.castSucc.succ:ℂ)^2*coordinateDensity α β w b P g z := by
  have hp := mixedCoordinates_functions_coe (product (α/w) (α/w)) (broadSquare (α*w) β b P g i)
    (product_integrable (α/w) (α/w) (div_pos hα hw) (div_pos hα hw))
    (product_memLp (α/w) (α/w) (div_pos hα hw) (div_pos hα hw))
    (broadSquare_memLp (α*w) β (mul_pos hα hw) hβ b P g hc hg i)
  filter_upwards [hp] with z hz
  rw [rightSquareState,hz,broadSquare,mul_left_comm,mixed_density α β w hα hw b P g z]

#print axioms leftSquareState_coe
#print axioms rightSquareState_coe
#print axioms leftSquareState_coordinates_coe
#print axioms rightSquareState_coordinates_coe
end
end UnifiedTheory.Audit.KFCausalNarrowFourierSecondMomentStates
