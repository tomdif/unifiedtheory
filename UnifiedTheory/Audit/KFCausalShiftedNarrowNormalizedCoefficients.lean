/- Exact normalized clock rates and the polynomial coefficients of the
potential Fourier derivative. Only one unbounded clock moment remains. -/
import UnifiedTheory.Audit.KFCausalShiftedNarrowControlledFactors
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialFourierClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalShiftedNarrowNormalizedCoefficients
noncomputable section
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalShiftedNarrowJointGaussian (narrow spectator N)
open KFCausalShiftedNarrowControlledFactors
open KFCausalRadialMultipliers
open KFCausalShiftedGaussianPureDifferential (realInverse)
open KFCausalShiftedGaussianLongitudinalDifferential (inverseClock amplitudeSlope)
open KFCausalClockFloorRelativeShift (scale argument)
open KFCausalNeutralPlaneClockGeometry (velocity)
open KFCausalShiftedNarrowFourierClockDerivative (neutralSlope fieldSlope radiusSlope)

theorem normalization_eq (α ε y : ℝ) (x : Configuration) :
    normalization α ε y x = (Real.pi:ℂ)/((α:ℂ)*(scale ε y x.1)^2) := by
  unfold normalization inverseSquare
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem velocity_normalized (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (x : Configuration) :
    realInverse ε x.1*velocity ε (Real.exp x.1) (scale ε y x.1) =
      difference ε y x*scale ε y x.1/2 := by
  have hv := (KFCausalNeutralPlaneClockGeometry.scale_velocity ε y x.1 hε hy).unique
    (KFCausalShiftedGaussianLongitudinalDifferential.scale_derivative ε y x.1 hε hy)
  have hc : ((Real.exp x.1+ε:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  rw [hv]
  unfold difference realInverse
  field_simp

theorem neutral_normalized (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (x : Configuration) :
    realInverse ε x.1*neutralSlope (velocity ε (Real.exp x.1) (scale ε y x.1)) (spectator x) =
      normalizedNeutral ε y x := by
  have hv := velocity_normalized ε y hε hy x
  dsimp [neutralSlope,spectator,normalizedNeutral]
  linear_combination (4*(KFCausalPairedModeCoordinates.scale:ℂ)*(x.2 3:ℂ))*hv

theorem field_normalized (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (x : Configuration) :
    realInverse ε x.1*fieldSlope (velocity ε (Real.exp x.1) (scale ε y x.1)) (spectator x) =
      normalizedField ε y x := by
  have hv := velocity_normalized ε y hε hy x
  dsimp [fieldSlope,spectator,normalizedField]
  linear_combination (6*(KFCausalPairedModeCoordinates.scale:ℂ)*(x.2 3:ℂ))*hv

theorem radius_normalized (α ε y : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (x : Configuration) :
    realInverse ε x.1*radiusSlope ((α:ℂ)*(scale ε y x.1)^2)
      (2*(α:ℂ)*scale ε y x.1*velocity ε (Real.exp x.1) (scale ε y x.1)) (narrow x) (spectator x) =
      normalizedRadius α ε y x := by
  rw [KFCausalShiftedNarrowFourierClockBounds.normalized_radius_identity α ε y x.1 hα hε hy]
  simp only [← Complex.ofReal_pow,KFCausalShiftedNarrowJointGaussian.narrow_square]
  dsimp [normalizedRadius,difference,inverseSquare,spectator,KFCausalShiftedNarrowFourierGeometry.broadRadius]
  push_cast
  rfl

theorem normalization_normalized (α ε y : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (x : Configuration) :
    realInverse ε x.1*(-((Real.pi:ℂ)*(2*(α:ℂ)*scale ε y x.1*
      velocity ε (Real.exp x.1) (scale ε y x.1))/((α:ℂ)*(scale ε y x.1)^2)^2)) =
      -normalization α ε y x*difference ε y x := by
  have hv := velocity_normalized ε y hε hy x
  have ha : (α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
  have hr : scale ε y x.1 ≠ 0 := fun he => by
    have hp := KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y x.1 hε hy
    rw [he] at hp
    exact lt_irrefl 0 hp
  rw [normalization_eq]
  field_simp [ha,hr]
  linear_combination -2*hv

theorem amplitude_normalized (ε a p y : ℝ) (hε : 0 < ε) (x : Configuration) :
    realInverse ε x.1*amplitudeSlope ε a p y x.1+(KFCausalClockFloorPureClockDerivative.rate ε x.1:ℂ) =
      (p:ℂ)*Complex.I*inverseClock ε y x.1-2*(a:ℂ)*argument ε y x.1-realInverse ε x.1 := by
  have hc : ((Real.exp x.1+ε:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  unfold realInverse amplitudeSlope KFCausalClockFloorPureClockDerivative.rate
    KFCausalClockFloorFlow.clock KFCausalClockFloorTransportDerivative.amplitudeLogSlope
  push_cast
  push_cast at hc
  field_simp [hc]
  ring

def core (ε y z : ℝ) (P : Polynomial ℂ) (k : ℕ) (x : Configuration) : ℂ :=
  F ε z x^k*P.eval (N ε y x)
def coreRate (β ε y z : ℝ) (b : ℂ) (P : Polynomial ℂ) (k : ℕ) (x : Configuration) : ℂ :=
  (k:ℂ)*F ε z x^(k-1)*normalizedField ε z x*P.eval (N ε y x)+
    F ε z x^k*P.derivative.eval (N ε y x)*normalizedNeutral ε y x+
    core ε y z P k x*(b-2*(β:ℂ)*N ε y x)*normalizedNeutral ε y x
def inputCoefficient (α ε y z : ℝ) (C : ℂ) (P : Polynomial ℂ) (k : ℕ) (x : Configuration) : ℂ :=
  normalization α ε y x*C*core ε y z P k x
def regularCoefficient (α β ε y z p : ℝ) (C b : ℂ) (P : Polynomial ℂ) (k : ℕ) (x : Configuration) : ℂ :=
  normalization α ε y x*C*(amplitudeRate ε p y x*core ε y z P k x+coreRate β ε y z b P k x)
def chargedCoefficient (α ε y z : ℝ) (C : ℂ) (P : Polynomial ℂ) (k : ℕ) (x : Configuration) : ℂ :=
  inputCoefficient α ε y z C P k x*normalizedRadius α ε y x

variable (ε y z : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3)
include hε hy hz

theorem core_controlled (P : Polynomial ℂ) (k : ℕ) : Controlled (core ε y z P k) :=
  controlled_mul _ _ (controlled_pow _ (field_controlled ε z hε hz) k)
    (polynomial_controlled _ (neutral_controlled ε y hε hy) P)

theorem coreRate_controlled (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (k : ℕ) :
    Controlled (coreRate β ε y z b P k) :=
  controlled_add _ _ (controlled_add _ _
    (controlled_mul _ _ (controlled_mul _ _
      (controlled_mul _ _ (controlled_const _) (controlled_pow _ (field_controlled ε z hε hz) (k-1)))
        (normalizedField_controlled ε z hε hz)) (polynomial_controlled _ (neutral_controlled ε y hε hy) P))
    (controlled_mul _ _ (controlled_mul _ _ (controlled_pow _ (field_controlled ε z hε hz) k)
      (polynomial_controlled _ (neutral_controlled ε y hε hy) P.derivative)) (normalizedNeutral_controlled ε y hε hy)))
    (controlled_mul _ _ (controlled_mul _ _ (core_controlled ε y z hε hy hz P k)
      (controlled_sub _ _ (controlled_const b)
        (controlled_mul _ _ (controlled_const (2*(β:ℂ))) (neutral_controlled ε y hε hy))))
          (normalizedNeutral_controlled ε y hε hy))

theorem inputCoefficient_controlled (α : ℝ) (C : ℂ) (P : Polynomial ℂ) (k : ℕ) :
    Controlled (inputCoefficient α ε y z C P k) :=
  controlled_mul _ _ (controlled_mul _ _ (normalization_controlled ε y hε hy α) (controlled_const C))
    (core_controlled ε y z hε hy hz P k)

theorem regularCoefficient_controlled (α β p : ℝ) (C b : ℂ) (P : Polynomial ℂ) (k : ℕ) :
    Controlled (regularCoefficient α β ε y z p C b P k) :=
  controlled_mul _ _ (controlled_mul _ _ (normalization_controlled ε y hε hy α) (controlled_const C))
    (controlled_add _ _ (controlled_mul _ _ (amplitudeRate_controlled ε y hε hy p) (core_controlled ε y z hε hy hz P k))
      (coreRate_controlled ε y z hε hy hz β b P k))

theorem chargedCoefficient_controlled (α : ℝ) (C : ℂ) (P : Polynomial ℂ) (k : ℕ) :
    Controlled (chargedCoefficient α ε y z C P k) :=
  controlled_mul _ _ (inputCoefficient_controlled ε y z hε hy hz α C P k)
    (normalizedRadius_controlled ε y hε hy α)

#print axioms normalization_eq
#print axioms velocity_normalized
#print axioms neutral_normalized
#print axioms field_normalized
#print axioms radius_normalized
#print axioms normalization_normalized
#print axioms amplitude_normalized
#print axioms core_controlled
#print axioms coreRate_controlled
#print axioms inputCoefficient_controlled
#print axioms regularCoefficient_controlled
#print axioms chargedCoefficient_controlled
end
end UnifiedTheory.Audit.KFCausalShiftedNarrowNormalizedCoefficients
