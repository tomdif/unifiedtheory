/- Charge averaging preserves the exact clock-slope representative of
the ordered momentum outputs of neutral polynomial packets. Their clock
frequency is fixed along the charge orbit, so no extra source derivative
or interchange of point evaluation with integration is used. -/
import UnifiedTheory.Audit.KFCausalPolynomialOrderedMomentumDensity
import UnifiedTheory.Audit.KFCausalDisplacedPolynomialProjectedResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalProjectedPolynomialMomentumDensity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalUnboundedMultiplierIntegral (relation relation_integral)
open UnifiedTheory.Audit.KFCausalPolynomialOrderedMomentumDensity (clockSlope clockSlope_continuous polynomial_relation)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)
open UnifiedTheory.Audit.KFCausalDisplacedPolynomialEnergyLift (inputOrbit momentumOrbit orbit_memLp)
open UnifiedTheory.Audit.KFCausalDisplacedPolynomialProjectedResponse (meanInput meanMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (amplitude clockFrequency source)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds (clockFrequency_parameter)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (P : Polynomial ℂ)
local notation "w" => clockSlope ε a h (clockFrequency h k)

theorem orbit_relation (n : Fin 3) (θ : ℝ) :
    relation w (inputOrbit ε a h hε ha hh hb q k P (index n) θ)
      (momentumOrbit ε a h hε ha hh hb q k P (index n) θ) := by
  exact polynomial_relation ε a h hε ha hh hb
    (amplitude h (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k))
    (clockFrequency h (parameter (2*Real.pi*θ) k))
    (source h (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k)) 4 P modelDirections pointField n

theorem mean_relation (n : Fin 3) :
    relation w (meanInput ε a h hε ha hh hb q k P (index n))
      (meanMomentum ε a h hε ha hh hb q k P (index n)) :=
  relation_integral _ (clockSlope_continuous ε a h hε hb (clockFrequency h k)).measurable _ _
    ((orbit_memLp ε a h hε ha hh hb q k P (index n)).1.integrable (by norm_num))
    ((orbit_memLp ε a h hε ha hh hb q k P (index n)).2.integrable (by norm_num))
    (Filter.Eventually.of_forall (orbit_relation ε a h hε ha hh hb q k P n))

theorem weighted_output_memLp (n : Fin 3) :
    MemLp (fun x : Configuration => w x*meanInput ε a h hε ha hh hb q k P (index n) x) 2 volume :=
  (Lp.memLp (meanMomentum ε a h hε ha hh hb q k P (index n))).ae_eq
    (mean_relation ε a h hε ha hh hb q k P n)

#print axioms orbit_relation
#print axioms mean_relation
#print axioms weighted_output_memLp
end
end UnifiedTheory.Audit.KFCausalProjectedPolynomialMomentumDensity
