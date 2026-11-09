/- Pointwise identifications of the physical diagonal Gaussian, its paired
coordinates and its normalized mixed-coordinate radial profile. -/
import UnifiedTheory.Audit.KFCausalChargeGaussianProducts
import UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
import UnifiedTheory.Audit.KFCausalPairedModeCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorShearBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalChargeGaussianIdentities
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalChargeGaussianProducts
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

theorem norm_two_square (x : Block 2) : ‖x‖^2 = (x 0)^2+(x 1)^2 := by
  simp [EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs]

theorem gaussian_spectator_product (γ α β : ℝ) (g : ℝ → ℂ) (u : Block 2) (v : Block 4) :
    gaussian 2 γ u * spectator α β g v = g (v 0)*
      Complex.exp (-((γ*((u 0)^2+(u 1)^2)+α*((v 1)^2+(v 2)^2)+β*(v 3)^2:ℝ):ℂ)) := by
  simp only [gaussian,spectator,← Complex.ofReal_pow,norm_two_square]
  rw [mul_left_comm,← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

theorem mixed_profile_identity (α β c : ℝ) (hα : 0 < α)
    (hmatch : Real.pi^2/α = α*c^2) (g : ℝ → ℂ) (x : Joint 2 4) :
    (𝓕 (gaussian 2 α)) (KFCausalEuclideanProductCoordinates.split 2 4 x).1 *
      spectator α β g (KFCausalEuclideanProductCoordinates.split 2 4 x).2 =
      ((Real.pi/α:ℝ):ℂ)*profile α β c g x := by
  rw [gaussian_two_fourier α hα,mul_assoc,gaussian_spectator_product]
  simp only [split_fst,split_snd,profile,radius_coordinates,hmatch]
  congr 2
  congr 1
  congr 1
  ring

def positionProfile (α β : ℝ) (g : ℝ → ℂ) (x : Space) : ℂ :=
  g (x 0)*Complex.exp (-((α*((x 1)^2+(x 2)^2+(x 3)^2+(x 4)^2)+β*(x 5)^2:ℝ):ℂ))

def configurationProfile (α β : ℝ) (g : ℝ → ℂ) (x : Configuration) : ℂ :=
  g x.1*KFCausalClockFloorShearBounds.physicalGaussian α β x.2

theorem paired_profile_identity (α β : ℝ) (g : ℝ → ℂ) (x : Space) :
    gaussian 2 α (WithLp.toLp 2 ![KFCausalPairedModeCoordinates.scale*(x 1-x 2),
      KFCausalPairedModeCoordinates.scale*(x 3-x 4)]) *
    spectator α β g (WithLp.toLp 2 ![x 0,KFCausalPairedModeCoordinates.scale*(x 1+x 2),
      KFCausalPairedModeCoordinates.scale*(x 3+x 4),x 5]) = positionProfile α β g x := by
  rw [gaussian_spectator_product]
  change g (x 0)*Complex.exp (-((α*((KFCausalPairedModeCoordinates.scale*(x 1-x 2))^2+
    (KFCausalPairedModeCoordinates.scale*(x 3-x 4))^2)+
    α*((KFCausalPairedModeCoordinates.scale*(x 1+x 2))^2+
    (KFCausalPairedModeCoordinates.scale*(x 3+x 4))^2)+β*(x 5)^2:ℝ):ℂ)) = _
  unfold positionProfile
  congr 1
  congr 1
  congr 1
  ring_nf
  rw [KFCausalPairedModeCoordinates.scale_square]
  ring

theorem configurationProfile_split (α β : ℝ) (g : ℝ → ℂ) (x : Space) :
    configurationProfile α β g (KFCausalEuclideanConfiguration.split x) = positionProfile α β g x := by
  simp [configurationProfile,positionProfile,KFCausalEuclideanConfiguration.split_apply,
    KFCausalClockFloorShearBounds.physicalGaussian,Fin.sum_univ_succ,add_assoc]

theorem configurationProfile_continuous (α β : ℝ) (g : ℝ → ℂ) (hg : Continuous g) :
    Continuous (configurationProfile α β g) := by
  unfold configurationProfile KFCausalClockFloorShearBounds.physicalGaussian
  fun_prop

theorem configurationProfile_zero (α β : ℝ) (g : ℝ → ℂ) :
    configurationProfile α β g (0,0) = g 0 := by
  simp [configurationProfile,KFCausalClockFloorShearBounds.physicalGaussian]

#print axioms norm_two_square
#print axioms gaussian_spectator_product
#print axioms mixed_profile_identity
#print axioms paired_profile_identity
#print axioms configurationProfile_split
#print axioms configurationProfile_continuous
#print axioms configurationProfile_zero

end
end UnifiedTheory.Audit.KFCausalChargeGaussianIdentities
