/- Exact cancellation of the full-clock cross integrals for the clock
half and the two equally weighted pairs of transverse momenta. The
neutral component in the second direction is retained and removed by
its own parity, not by an assumed plane symmetry. -/
import UnifiedTheory.Audit.KFCausalChargedPairKineticSymmetries
import UnifiedTheory.Audit.KFCausalChargedPairKineticPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalChargedPairKineticCancellation
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorShearBounds (physicalGaussian)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalChargedPairDifferential
open KFCausalChargedPairKineticPairing
open KFCausalChargedPairKineticSymmetries
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalClockFloorTrialClockEnergy (dampedClockFunction)

def staticPolynomial (α β : ℝ) (q : Transverse) : ℝ :=
  responsePolynomial α β (modelDirections 0) q+responsePolynomial α β (modelDirections 1) q

def growingPolynomial (α β : ℝ) (q : Transverse) : ℝ :=
  responsePolynomial α β (modelDirections 2) q+responsePolynomial α β (modelDirections 3) q

theorem static_four (α β : ℝ) (q : Transverse) :
    staticPolynomial α β q+staticPolynomial α β (reflect q)+
      staticPolynomial α β (swap q)+staticPolynomial α β (reflect (swap q)) = 0 := by
  simp [staticPolynomial,responsePolynomial,derivativePolynomial,pairDerivative,weightedLinear,
    KFCausalChargedPairCoordinates.pairPolynomial,modelDirections,swap,reflect]
  ring

theorem growing_swap (α β : ℝ) (q : Transverse) :
    growingPolynomial α β (swap q) = -growingPolynomial α β q := by
  simp [growingPolynomial,responsePolynomial,derivativePolynomial,pairDerivative,weightedLinear,
    KFCausalChargedPairCoordinates.pairPolynomial,modelDirections,swap]
  ring

def staticDensity (ε a h : ℝ) (x : Configuration) : ℂ :=
  momentumDensity ε a h (modelDirections 0) x+momentumDensity ε a h (modelDirections 1) x

def growingDensity (ε a h : ℝ) (x : Configuration) : ℂ :=
  momentumDensity ε a h (modelDirections 2) x+momentumDensity ε a h (modelDirections 3) x

theorem static_density (ε a h : ℝ) (x : Configuration) :
    staticDensity ε a h x =
      (h^2*‖dampedClockFunction ε a x.1‖^2*staticPolynomial (groundWidth h) (neutralWidth h) x.2*
        ‖physicalGaussian (groundWidth h) (neutralWidth h) x.2‖^2:ℝ) := by
  unfold staticDensity momentumDensity staticPolynomial
  push_cast
  ring

theorem growing_density (ε a h : ℝ) (x : Configuration) :
    growingDensity ε a h x =
      (h^2*‖dampedClockFunction ε a x.1‖^2*growingPolynomial (groundWidth h) (neutralWidth h) x.2*
        ‖physicalGaussian (groundWidth h) (neutralWidth h) x.2‖^2:ℝ) := by
  unfold growingDensity momentumDensity growingPolynomial
  push_cast
  ring

theorem clock_density_swap (ε a h : ℝ) (x : Configuration) :
    clockDensity ε a h (fullSwap x) = -clockDensity ε a h x := by
  simp only [clockDensity,fullSwap_apply,gaussian_swap,pair_swap]
  push_cast
  ring

theorem growing_density_swap (ε a h : ℝ) (x : Configuration) :
    growingDensity ε a h (fullSwap x) = -growingDensity ε a h x := by
  simp only [growing_density,fullSwap_apply,gaussian_swap,growing_swap]
  push_cast
  ring

theorem static_density_four (ε a h : ℝ) (x : Configuration) :
    staticDensity ε a h x+staticDensity ε a h (fullReflect x)+
      staticDensity ε a h (fullSwap x)+staticDensity ε a h (fullReflect (fullSwap x)) = 0 := by
  have hc : (staticPolynomial (groundWidth h) (neutralWidth h) x.2:ℂ)+
      (staticPolynomial (groundWidth h) (neutralWidth h) (reflect x.2):ℂ)+
      (staticPolynomial (groundWidth h) (neutralWidth h) (swap x.2):ℂ)+
      (staticPolynomial (groundWidth h) (neutralWidth h) (reflect (swap x.2)):ℂ) = 0 := by
    exact_mod_cast static_four (groundWidth h) (neutralWidth h) x.2
  simp only [static_density,fullSwap_apply,fullReflect_apply,gaussian_reflect,gaussian_swap]
  push_cast
  linear_combination (h:ℂ)^2*(‖dampedClockFunction ε a x.1‖:ℂ)^2*
    (‖physicalGaussian (groundWidth h) (neutralWidth h) x.2‖:ℂ)^2*hc

theorem clock_integral_zero (ε a h : ℝ) : (∫ x, clockDensity ε a h x) = 0 :=
  odd_integral_zero _ fullSwap fullSwap_preserving (clock_density_swap ε a h)

theorem growing_integral_zero (ε a h : ℝ) : (∫ x, growingDensity ε a h x) = 0 :=
  odd_integral_zero _ fullSwap fullSwap_preserving (growing_density_swap ε a h)

theorem static_integral_zero (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) : (∫ x, staticDensity ε a h x) = 0 :=
  four_integral_zero _ ((momentumDensity_integrable ε a h hε ha hh hb 0).add
    (momentumDensity_integrable ε a h hε ha hh hb 1)) (static_density_four ε a h)

#print axioms static_four
#print axioms growing_swap
#print axioms static_density
#print axioms growing_density
#print axioms clock_density_swap
#print axioms growing_density_swap
#print axioms static_density_four
#print axioms clock_integral_zero
#print axioms growing_integral_zero
#print axioms static_integral_zero
end
end UnifiedTheory.Audit.KFCausalChargedPairKineticCancellation
