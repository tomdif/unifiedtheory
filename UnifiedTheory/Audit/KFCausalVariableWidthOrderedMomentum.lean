/- The exact Gaussian clock slope extends to every polynomial ordered
momentum output. Source-circle integration and finite complex sums preserve
the unbounded multiplication relation, with all three ordered factors. -/
import UnifiedTheory.Audit.KFCausalUnboundedMultiplierIntegral
import UnifiedTheory.Audit.KFCausalVariableWidthPolynomialMomentum
import UnifiedTheory.Audit.KFCausalPolynomialOrderedMomentumDensity
import UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalVariableWidthOrderedMomentum
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalUnboundedMultiplierIntegral
  (relation relation_integral relation_smul relation_sum)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (weakSlope)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (argument argument_smooth)
open UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential
  (inverseClock inverseClock_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge
  (index input_factor_density momentum_factor_density)
open UnifiedTheory.Audit.KFCausalPolynomialGaussianStates
  (circleSource sourceBound circleSource_continuous circleSource_bound)
open UnifiedTheory.Audit.KFCausalSourceCircleCoefficients
open UnifiedTheory.Audit.KFCausalVariableWidthPolynomialDomain (powerOutput output)
open UnifiedTheory.Audit.KFCausalVariableWidthPolynomialMomentum
  (factorCurve factorCurve_continuous powerMomentumFactor momentumFactor)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)

open KFCausalPolynomialOrderedMomentumDensity (clockSlope clockSlope_continuous)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)

include hh

theorem source_relation (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) :
    relation (clockSlope ε a h p)
      (KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw C p b h hb v l (index n))
      (KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hw C p b h hb v l (index n)) := by
  filter_upwards [input_factor_density ε a α β hε ha hα hβ hw C p b h hb v l n,
    momentum_factor_density ε a α β hε ha hα hβ hw C p b h hh hb v l n] with x hi hm
  rw [hi,hm]
  rfl

variable (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5)

theorem power_relation (d : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) :
    relation (clockSlope ε a h p)
      (powerOutput ε a α β hε ha hα hβ hw h C p b i hb d v l (index n))
      (powerMomentumFactor ε a α β hε ha hα hβ hw h p b i C hb d v l (index n)) := by
  let F : ℝ → Hilbert := fun θ => KFCausalClockFloorSourcedCommonDomain.factorOutput
    ε a α β hε ha hα hβ hw (weight d θ) p (circleSource b i θ) h hb v l (index n)
  let G := factorCurve ε a α β hε ha hα hβ hw h p b i hb d v l (index n)
  have hF : Continuous F :=
    KFCausalVariableWidthSourceCurves.factor_continuous ε a α β hε ha hα hβ hw h hb |p| (sourceBound b)
      (weight d) (fun _ => p) (circleSource b i) (weight_continuous d) continuous_const
      (circleSource_continuous b i) (fun θ => (weight_norm d θ).le) (fun _ => le_rfl)
      (circleSource_bound b i) v l (index n)
  have hG : Continuous G := factorCurve_continuous ε a α β hε ha hα hβ hw h p b i hb d v l (index n)
  have he : relation (clockSlope ε a h p) (∫ θ, F θ ∂angleMeasure) (∫ θ, G θ ∂angleMeasure) :=
    relation_integral _ (clockSlope_continuous ε a h hε hb p).measurable F G
      ((continuous_angle_memLp F hF).integrable (by norm_num))
      ((continuous_angle_memLp G hG).integrable (by norm_num))
      (Filter.Eventually.of_forall (fun θ =>
        source_relation ε a α β hε ha hα hβ hw h hh hb (weight d θ) p (circleSource b i θ) v l n))
  exact relation_smul _ (clockSlope_continuous ε a h hε hb p).measurable _ _ he (C*normalization d)

theorem polynomial_relation (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) :
    relation (clockSlope ε a h p)
      (output ε a α β hε ha hα hβ hw h C p b i hb P v l (index n))
      (momentumFactor ε a α β hε ha hα hβ hw h p b i C hb P v l (index n)) :=
  relation_sum _ (clockSlope_continuous ε a h hε hb p).measurable P.support _ _
    (fun d _ => relation_smul _ (clockSlope_continuous ε a h hε hb p).measurable _ _
      (power_relation ε a α β hε ha hα hβ hw h hh hb C p b i d v l n) (P.coeff d))

#print axioms source_relation
#print axioms power_relation
#print axioms polynomial_relation
end
end UnifiedTheory.Audit.KFCausalVariableWidthOrderedMomentum
