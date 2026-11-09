/- A joint Gaussian envelope for the narrow Fourier profiles. The exact
broad charged/neutral Gaussian is bounded before polynomial factors, so
the neutral shear cannot consume decay lost in a separate coarse bound. -/
import UnifiedTheory.Audit.KFCausalShiftedNarrowFourierChargedEnvelope
import UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalShiftedNarrowJointGaussian
noncomputable section
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalShiftedNarrowFourierGeometry (reconstruct neutral broadRadius radius)
open KFCausalClockFloorRelativeShift (scale relative)
open KFCausalClockFloorShearBounds (physicalGaussian)
open KFCausalImaginaryShearPathBounds (width width_positive transverse_bound)
open KFCausalClockFloorCoherentBounds (sourceConstant)

def narrow (x : Configuration) : Block 2 := WithLp.toLp 2 ![x.2 0,x.2 1]
def spectator (x : Configuration) : Block 4 := WithLp.toLp 2 ![x.1,x.2 2,x.2 3,x.2 4]
def sourceVector (b : ℂ) : Fin 5 → ℂ := ![0,0,0,0,b]
def N (ε y : ℝ) (x : Configuration) : ℂ := neutral (scale ε y x.1) (spectator x)
def Z (α ε y : ℝ) (x : Configuration) : ℂ :=
  radius ((α:ℂ)*(scale ε y x.1)^2) (narrow x) (spectator x)
def gaussian (α β ε y : ℝ) (b : ℂ) (x : Configuration) : ℂ :=
  Complex.exp (-Z α ε y x-(β:ℂ)*N ε y x^2+b*N ε y x)
def jointWidth (α β : ℝ) : ℝ :=
  min ((Real.pi^2/α)*(Real.exp (-Real.pi/3)/2)) (width α β)
def sourceBound (α β : ℝ) (b : ℂ) : ℝ := Real.exp (sourceConstant α β (sourceVector b)/2)

theorem jointWidth_positive (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : 0 < jointWidth α β := by
  have := width_positive α β hα hβ
  unfold jointWidth
  positivity

theorem sourceBound_positive (α β : ℝ) (b : ℂ) : 0 < sourceBound α β b := Real.exp_pos _

theorem narrow_square (x : Configuration) : ‖narrow x‖^2 = (x.2 0)^2+(x.2 1)^2 := by
  rw [KFCausalShiftedNarrowFourierGeometry.narrow_norm_square]
  rfl

theorem broad_exponent (α β : ℝ) (r b : ℂ) (v : Block 4) :
    KFCausalRelativeGaussianDifferential.exponent α β (sourceVector b) r (reconstruct 0 v) =
      -(α:ℂ)*r^2*(broadRadius v:ℂ)-(β:ℂ)*neutral r v^2+b*neutral r v := by
  dsimp [KFCausalRelativeGaussianDifferential.exponent]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  dsimp [sourceVector,KFCausalPhysicalGaussianMoments.widths,
    KFCausalRelativeGaussianDifferential.position,reconstruct,neutral,broadRadius]
  push_cast
  have hs : (KFCausalPairedModeCoordinates.scale:ℂ)^2 = (1/2:ℂ) := by
    rw [← Complex.ofReal_pow,KFCausalPairedModeCoordinates.scale_square]
    norm_num
  ring_nf
  rw [hs]
  ring

theorem broad_gaussian_norm (γ : ℝ) (v : Block 4) :
    ‖physicalGaussian γ γ (reconstruct 0 v)‖ = Real.exp (-γ*(broadRadius v+(v 3)^2)) := by
  rw [physicalGaussian,Complex.norm_exp]
  simp only [Complex.neg_re,Complex.ofReal_re]
  congr 1
  dsimp [reconstruct,broadRadius]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  dsimp
  ring_nf
  rw [KFCausalPairedModeCoordinates.scale_square]
  ring

theorem gaussian_split (α β ε y : ℝ) (b : ℂ) (x : Configuration) :
    gaussian α β ε y b x =
      Complex.exp (-((Real.pi^2/α:ℝ):ℂ)*((scale ε y x.1)^2)⁻¹*(‖narrow x‖:ℂ)^2)*
        Complex.exp (KFCausalRelativeGaussianDifferential.exponent α β (sourceVector b)
          (scale ε y x.1) (reconstruct 0 (spectator x))) := by
  rw [gaussian,Z,KFCausalShiftedNarrowFourierClockBounds.radius_split,broad_exponent,← Complex.exp_add]
  congr 1
  unfold N
  ring

theorem isotropic_norm (γ : ℝ) (x : Configuration) :
    ‖physicalGaussian γ γ x.2‖ =
      Real.exp (-γ*(‖narrow x‖^2+broadRadius (spectator x)+(spectator x 3)^2)) := by
  rw [physicalGaussian,Complex.norm_exp,narrow_square]
  simp only [Complex.neg_re,Complex.ofReal_re,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  dsimp [spectator,broadRadius]
  congr 1
  ring

theorem gaussian_continuous (α β ε y : ℝ) (b : ℂ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (gaussian α β ε y b) := by
  have hr := (KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy).continuous
  have hn (s : ℝ) : scale ε y s ≠ 0 := fun he => by
    have hp := KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy
    rw [he] at hp
    exact lt_irrefl 0 hp
  rw [show gaussian α β ε y b = fun x =>
    Complex.exp (-(((Real.pi^2/α:ℝ):ℂ)*((scale ε y x.1)^2)⁻¹*(‖narrow x‖:ℂ)^2+
      (α:ℂ)*(scale ε y x.1)^2*(broadRadius (spectator x):ℂ))-(β:ℂ)*N ε y x^2+b*N ε y x) by
        funext x; rw [gaussian,Z,KFCausalShiftedNarrowFourierClockBounds.radius_split]]
  simp only [← Complex.ofReal_pow,narrow_square]
  dsimp [N,neutral,spectator,broadRadius]
  fun_prop (disch := intro x; exact pow_ne_zero 2 (hn x.1))

theorem gaussian_bound (α β ε y : ℝ) (b : ℂ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (x : Configuration) :
    ‖gaussian α β ε y b x‖ ≤ sourceBound α β b*‖physicalGaussian (jointWidth α β) (jointWidth α β) x.2‖ := by
  have hstrip := KFCausalShiftedGaussianRadialMoments.relative_strip ε y hε hy x.1
  have hb := transverse_bound α β hα hβ hw (sourceVector b) (relative ε y x.1) hstrip
    (reconstruct 0 (spectator x))
  change ‖Complex.exp (KFCausalRelativeGaussianDifferential.exponent α β (sourceVector b)
    (scale ε y x.1) (reconstruct 0 (spectator x)))‖ ≤ _ at hb
  rw [broad_gaussian_norm] at hb
  have hi := (KFCausalShiftedNarrowFourierClockBounds.scale_bounds ε y x.1 hε hy).2.1
  have hn : ‖Complex.exp (-((Real.pi^2/α:ℝ):ℂ)*((scale ε y x.1)^2)⁻¹*(‖narrow x‖:ℂ)^2)‖ ≤
      Real.exp (-((Real.pi^2/α)*(Real.exp (-Real.pi/3)/2))*‖narrow x‖^2) := by
    rw [Complex.norm_exp]
    simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.neg_re,Complex.neg_im,
      Complex.ofReal_re,Complex.ofReal_im,neg_zero,zero_mul,mul_zero,sub_zero]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi
      (by positivity : 0 ≤ Real.pi^2/α)) (sq_nonneg ‖narrow x‖)
    nlinarith only [h1]
  rw [gaussian_split,norm_mul]
  apply (mul_le_mul hn hb (norm_nonneg _) (Real.exp_pos _).le).trans
  rw [isotropic_norm]
  have h1 := mul_le_mul_of_nonneg_right
    (show jointWidth α β ≤ (Real.pi^2/α)*(Real.exp (-Real.pi/3)/2) from min_le_left _ _)
      (sq_nonneg ‖narrow x‖)
  have h2 := mul_le_mul_of_nonneg_right
    (show jointWidth α β ≤ width α β from min_le_right _ _)
      (add_nonneg (KFCausalShiftedNarrowFourierGeometry.broadRadius_nonnegative (spectator x))
        (sq_nonneg (spectator x 3)))
  change Real.exp _*(sourceBound α β b*Real.exp _) ≤ sourceBound α β b*_
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (sourceBound_positive α β b).le
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith only [h1,h2])

#print axioms jointWidth_positive
#print axioms sourceBound_positive
#print axioms narrow_square
#print axioms broad_exponent
#print axioms broad_gaussian_norm
#print axioms gaussian_split
#print axioms isotropic_norm
#print axioms gaussian_continuous
#print axioms gaussian_bound
end
end UnifiedTheory.Audit.KFCausalShiftedNarrowJointGaussian
