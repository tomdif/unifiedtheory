/- Polynomial multipliers of the joint Fourier Gaussian, uniformly in
clock position. Actual normalized scale derivatives are represented by
bounded inverse-clock differences; clock moments are kept separate. -/
import UnifiedTheory.Audit.KFCausalShiftedNarrowJointMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalShiftedNarrowControlledFactors
noncomputable section
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalRadialMultipliers
open KFCausalShiftedNarrowJointGaussian (narrow spectator N Z)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalShiftedGaussianPureDifferential
  (realInverse realInverse_controlled inverseClock_controlled scale_controlled)
open KFCausalShiftedGaussianLongitudinalDifferential (inverseClock)
local notation "κ" => (KFCausalPairedModeCoordinates.scale:ℂ)

def inverseSquare (ε y : ℝ) (x : Configuration) : ℂ := ((scale ε y x.1)^2)⁻¹
def normalization (α ε y : ℝ) (x : Configuration) : ℂ := ((Real.pi/α:ℝ):ℂ)*inverseSquare ε y x
def difference (ε y : ℝ) (x : Configuration) : ℂ := inverseClock ε y x.1-realInverse ε x.1
def F (ε z : ℝ) (x : Configuration) : ℂ :=
  KFCausalShiftedNarrowFourierGeometry.mixedField (scale ε z x.1) (spectator x)
def normalizedNeutral (ε y : ℝ) (x : Configuration) : ℂ :=
  2*κ*difference ε y x*scale ε y x.1*(x.2 3:ℂ)
def normalizedField (ε z : ℝ) (x : Configuration) : ℂ :=
  3*κ*difference ε z x*scale ε z x.1*(x.2 3:ℂ)
def normalizedRadius (α ε y : ℝ) (x : Configuration) : ℂ := difference ε y x*
  ((α:ℂ)*(scale ε y x.1)^2*((x.2 2:ℂ)^2+(x.2 3:ℂ)^2)-
    ((Real.pi^2/α:ℝ):ℂ)*inverseSquare ε y x*((x.2 0:ℂ)^2+(x.2 1:ℂ)^2))
def amplitudeRate (ε p y : ℝ) (x : Configuration) : ℂ :=
  (p:ℂ)*Complex.I*inverseClock ε y x.1-realInverse ε x.1-difference ε y x

theorem polynomial_controlled (U : Configuration → ℂ) (hU : Controlled U) (P : Polynomial ℂ) :
    Controlled (fun x => P.eval (U x)) := by
  simp only [Polynomial.eval_eq_sum,Polynomial.sum]
  exact controlled_sum P.support _ (fun i _ =>
    controlled_mul _ _ (controlled_const (P.coeff i)) (controlled_pow U hU i))

theorem pairSquare_controlled (i j : Fin 5) :
    Controlled (fun x : Configuration => (x.2 i:ℂ)^2+(x.2 j:ℂ)^2) :=
  controlled_add _ _ (controlled_pow _ (controlled_coordinate i) 2) (controlled_pow _ (controlled_coordinate j) 2)

variable (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)

include hε hy

theorem inverseSquare_controlled : Controlled (inverseSquare ε y) := by
  have hn (s : ℝ) : scale ε y s ≠ 0 := fun he => by
    have hp := KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy
    rw [he] at hp
    exact lt_irrefl 0 hp
  exact controlled_clock (fun s => ((scale ε y s)^2)⁻¹)
    (((KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy).continuous.pow 2).inv₀
      (fun s => pow_ne_zero 2 (hn s)))
    (Real.exp (Real.pi/3)) (Real.exp_pos _).le
    (fun s => (KFCausalShiftedNarrowFourierClockBounds.scale_bounds ε y s hε hy).2.2)

theorem normalization_controlled (α : ℝ) : Controlled (normalization α ε y) :=
  controlled_mul _ _ (controlled_const _) (inverseSquare_controlled ε y hε hy)

theorem difference_controlled : Controlled (difference ε y) :=
  controlled_sub _ _ (inverseClock_controlled ε y hε hy) (realInverse_controlled ε hε)

theorem neutral_controlled : Controlled (N ε y) := by
  change Controlled (fun x : Configuration => (x.2 4:ℂ)+4*κ*(scale ε y x.1-1)*(x.2 3:ℂ))
  exact controlled_add _ _ (controlled_coordinate 4)
    (controlled_mul _ _ (controlled_mul _ _ (controlled_const _)
      (controlled_sub _ _ (scale_controlled ε y hε hy) (controlled_const 1))) (controlled_coordinate 3))

theorem field_controlled : Controlled (F ε y) := by
  change Controlled (fun x : Configuration => (x.2 4:ℂ)+2*κ*(3*scale ε y x.1-2)*(x.2 3:ℂ))
  exact controlled_add _ _ (controlled_coordinate 4)
    (controlled_mul _ _ (controlled_mul _ _ (controlled_const _)
      (controlled_sub _ _ (controlled_mul _ _ (controlled_const 3) (scale_controlled ε y hε hy))
        (controlled_const 2))) (controlled_coordinate 3))

theorem radius_controlled (α : ℝ) : Controlled (Z α ε y) := by
  have he : Z α ε y = fun x : Configuration =>
      ((Real.pi^2/α:ℝ):ℂ)*inverseSquare ε y x*((x.2 0:ℂ)^2+(x.2 1:ℂ)^2)+
        (α:ℂ)*(scale ε y x.1)^2*((x.2 2:ℂ)^2+(x.2 3:ℂ)^2) := by
    funext x
    rw [Z,KFCausalShiftedNarrowFourierClockBounds.radius_split]
    simp only [← Complex.ofReal_pow,KFCausalShiftedNarrowJointGaussian.narrow_square]
    dsimp [spectator,KFCausalShiftedNarrowFourierGeometry.broadRadius,inverseSquare]
    push_cast
    rfl
  rw [he]
  exact controlled_add _ _
    (controlled_mul _ _ (controlled_mul _ _ (controlled_const _) (inverseSquare_controlled ε y hε hy))
      (pairSquare_controlled 0 1))
    (controlled_mul _ _ (controlled_mul _ _ (controlled_const _) (controlled_pow _ (scale_controlled ε y hε hy) 2))
      (pairSquare_controlled 2 3))

theorem normalizedNeutral_controlled : Controlled (normalizedNeutral ε y) :=
  controlled_mul _ _ (controlled_mul _ _
    (controlled_mul _ _ (controlled_const _) (difference_controlled ε y hε hy))
      (scale_controlled ε y hε hy)) (controlled_coordinate 3)

theorem normalizedField_controlled : Controlled (normalizedField ε y) :=
  controlled_mul _ _ (controlled_mul _ _
    (controlled_mul _ _ (controlled_const _) (difference_controlled ε y hε hy))
      (scale_controlled ε y hε hy)) (controlled_coordinate 3)

theorem normalizedRadius_controlled (α : ℝ) : Controlled (normalizedRadius α ε y) :=
  controlled_mul _ _ (difference_controlled ε y hε hy) (controlled_sub _ _
    (controlled_mul _ _ (controlled_mul _ _ (controlled_const _) (controlled_pow _ (scale_controlled ε y hε hy) 2))
      (pairSquare_controlled 2 3))
    (controlled_mul _ _ (controlled_mul _ _ (controlled_const _) (inverseSquare_controlled ε y hε hy))
      (pairSquare_controlled 0 1)))

theorem amplitudeRate_controlled (p : ℝ) : Controlled (amplitudeRate ε p y) :=
  controlled_sub _ _ (controlled_sub _ _
    (controlled_mul _ _ (controlled_const _) (inverseClock_controlled ε y hε hy))
      (realInverse_controlled ε hε)) (difference_controlled ε y hε hy)

#print axioms polynomial_controlled
#print axioms pairSquare_controlled
#print axioms inverseSquare_controlled
#print axioms normalization_controlled
#print axioms difference_controlled
#print axioms neutral_controlled
#print axioms field_controlled
#print axioms radius_controlled
#print axioms normalizedNeutral_controlled
#print axioms normalizedField_controlled
#print axioms normalizedRadius_controlled
#print axioms amplitudeRate_controlled
end
end UnifiedTheory.Audit.KFCausalShiftedNarrowControlledFactors
