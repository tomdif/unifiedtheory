/- All eight projected factor means are actual natural graph outputs
for displaced neutral polynomial packets and their pure-clock momenta.
Their full energy and signed momentum-response form retain every factor
and every complex polynomial interference term. No evolution derivative
or response bound uniform in polynomial degree is asserted. -/
import UnifiedTheory.Audit.KFCausalDisplacedPolynomialEnergyLift
import UnifiedTheory.Audit.KFCausalEnergyFactorGraphIntegration
import UnifiedTheory.Audit.KFCausalProjectedFactorMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalDisplacedPolynomialProjectedResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalDisplacedPolynomialOrbit (packet momentum momentum_graph)
open UnifiedTheory.Audit.KFCausalDisplacedPolynomialEnergyLift
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action action_strong_continuous)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroProjection)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors
  (modelDirections energyWeight energyWeight_norm_square)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalProjectedKineticResponse (action_integral)
open UnifiedTheory.Audit.KFCausalZeroChargeStructuredResponse (output project)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (P : Polynomial ℂ)
local notation "f" => packet ε a h hε ha hh q k P
local notation "b" => momentum ε a h hε ha hh q k P

def meanInput (j : Fin 8) : Hilbert := ∫ θ, inputOrbit ε a h hε ha hh hb q k P j θ ∂angleMeasure
def meanMomentum (j : Fin 8) : Hilbert := ∫ θ, momentumOrbit ε a h hε ha hh hb q k P j θ ∂angleMeasure
def factorEnergy (j : Fin 8) : ℝ := ‖meanInput ε a h hε ha hh hb q k P j‖^2
def factorRate (j : Fin 8) : ℝ := (-2/h)*(inner ℂ
  (meanInput ε a h hε ha hh hb q k P j) (meanMomentum ε a h hε ha hh hb q k P j)).im

theorem meanMomentum_reduction (j : Fin 8) :
    meanMomentum ε a h hε ha hh hb q k P j =
      KFCausalPolynomialMomentumReduction.factorMap ε a h hε ha hb
        (KFCausalClockFloorDisplacedSources.clockFrequency h k) j
        (meanInput ε a h hε ha hh hb q k P j,
          meanInput ε (a/2) h hε (by positivity) hh hb q k P j) := by
  let L := KFCausalPolynomialMomentumReduction.factorMap ε a h hε ha hb
    (KFCausalClockFloorDisplacedSources.clockFrequency h k) j
  have hi := ((orbit_memLp ε a h hε ha hh hb q k P j).1).integrable (by norm_num)
  have hj := ((orbit_memLp ε (a/2) h hε (by positivity) hh hb q k P j).1).integrable (by norm_num)
  have he (θ : ℝ) : momentumOrbit ε a h hε ha hh hb q k P j θ =
      L (inputOrbit ε a h hε ha hh hb q k P j θ,
        inputOrbit ε (a/2) h hε (by positivity) hh hb q k P j θ) :=
    KFCausalDisplacedPolynomialFormOrbit.momentumFactor_reduction ε a h hε ha hh hb q k P
      (2*Real.pi*θ) modelDirections pointField j
  unfold meanMomentum
  simp_rw [he]
  rw [L.integral_comp_comm (hi.prodMk hj),integral_pair hi hj]
  rfl

theorem factorRate_reduction (j : Fin 8) :
    factorRate ε a h hε ha hh hb q k P j =
      (-2/h)*(inner ℂ (meanInput ε a h hε ha hh hb q k P j)
        (KFCausalPolynomialMomentumReduction.factorMap ε a h hε ha hb
          (KFCausalClockFloorDisplacedSources.clockFrequency h k) j
          (meanInput ε a h hε ha hh hb q k P j,
            meanInput ε (a/2) h hε (by positivity) hh hb q k P j))).im := by
  rw [factorRate,meanMomentum_reduction]

variable (hq : q (.inr 0) = 0)

include hq in
theorem meanInput_graph (j : Fin 8) :
    (zeroProjection h hh f,meanInput ε a h hε ha hh hb q k P j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph := by
  simpa only [action_integral] using
    KFCausalEnergyFactorGraphIntegration.factor_graph ε h hε modelDirections pointField
      (fun θ => action h hh (2*Real.pi*θ) f) (inputOrbit ε a h hε ha hh hb q k P)
      ((action_strong_continuous h hh f).comp (continuous_const.mul continuous_id))
      (inputOrbit_continuous ε a h hε ha hh hb q k P)
      (inputOrbit_graph ε a h hε ha hh hb q k P hq) j

include hq in
theorem meanMomentum_graph (j : Fin 8) :
    (zeroProjection h hh b,meanMomentum ε a h hε ha hh hb q k P j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph := by
  simpa only [action_integral] using
    KFCausalEnergyFactorGraphIntegration.factor_graph ε h hε modelDirections pointField
      (fun θ => action h hh (2*Real.pi*θ) b) (momentumOrbit ε a h hε ha hh hb q k P)
      ((action_strong_continuous h hh b).comp (continuous_const.mul continuous_id))
      (momentumOrbit_continuous ε a h hε ha hh hb q k P)
      (momentumOrbit_graph ε a h hε ha hh hb q k P hq) j

include hb hq in
theorem projected_common_domains :
    zeroProjection h hh f ∈ commonEnergyDomain ε hε h modelDirections pointField ∧
      zeroProjection h hh b ∈ commonEnergyDomain ε hε h modelDirections pointField :=
  ⟨(commonEnergyDomain_iff ε hε h modelDirections pointField _).mpr
      (fun j => LinearPMap.mem_domain_of_mem_graph (meanInput_graph ε a h hε ha hh hb q k P hq j)),
    (commonEnergyDomain_iff ε hε h modelDirections pointField _).mpr
      (fun j => LinearPMap.mem_domain_of_mem_graph (meanMomentum_graph ε a h hε ha hh hb q k P hq j))⟩

theorem projected_momentum_graph :
    (zeroProjection h hh f,zeroProjection h hh b) ∈ (pureMomentum ε hε h).graph :=
  KFCausalPureClockZeroProjection.projected_graph ε hε h hh f b
    (momentum_graph ε a h hε ha hh q k P)

variable (mass2 quartic vacuum t : ℝ)
local notation "out" => output ε h hε hh hb mass2 quartic vacuum t
local notation "proj" => project ε h hε hh hb mass2 quartic vacuum t
local notation "u" => inputLift ε a h hε ha hh hb q k P hq mass2 quartic vacuum t
local notation "v" => momentumLift ε a h hε ha hh hb q k P hq mass2 quartic vacuum t
local notation "E" => factorEnergy ε a h hε ha hh hb q k P
local notation "r" => factorRate ε a h hε ha hh hb q k P

def projectedEnergy : ℝ := ‖out (proj u)‖^2
def projectedResponse : ℝ := (-2/h)*(inner ℂ (out (proj u)) (out (proj v))).im

theorem energy_decomposition :
    projectedEnergy ε a h hε ha hh hb q k P hq mass2 quartic vacuum t =
      ∑ j : Fin 8, ‖energyWeight mass2 quartic vacuum t j‖^2*E j :=
  KFCausalProjectedFactorMeans.projected_lift_energy ε h hε hh hb mass2 quartic vacuum t f
    (inputOrbit ε a h hε ha hh hb q k P)
    (inputOrbit_continuous ε a h hε ha hh hb q k P)
    (inputOrbit_graph ε a h hε ha hh hb q k P hq)

theorem response_decomposition :
    projectedResponse ε a h hε ha hh hb q k P hq mass2 quartic vacuum t =
      ∑ j : Fin 8, ‖energyWeight mass2 quartic vacuum t j‖^2*r j :=
  KFCausalProjectedFactorMeans.projected_lift_response ε h hε hh hb mass2 quartic vacuum t f b
    (inputOrbit ε a h hε ha hh hb q k P) (momentumOrbit ε a h hε ha hh hb q k P)
    (inputOrbit_continuous ε a h hε ha hh hb q k P)
    (momentumOrbit_continuous ε a h hε ha hh hb q k P)
    (inputOrbit_graph ε a h hε ha hh hb q k P hq)
    (momentumOrbit_graph ε a h hε ha hh hb q k P hq)

omit ε a h hε ha hh hb q k P hq in
theorem physical_sum (hm : 0 ≤ mass2) (hg : 0 ≤ quartic) (hv : 0 ≤ vacuum) (z : Fin 8 → ℝ) :
    (∑ j : Fin 8, ‖energyWeight mass2 quartic vacuum t j‖^2*z j) =
      (z 0+z 1+z 2)/2+Real.exp (2*t)*((z 3+z 4)/2+mass2/2*z 5+quartic/4*z 6+vacuum*z 7) := by
  simp_rw [energyWeight_norm_square mass2 quartic vacuum t hm hg hv]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  ring!

theorem physical_energy (hm : 0 ≤ mass2) (hg : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    projectedEnergy ε a h hε ha hh hb q k P hq mass2 quartic vacuum t =
      (E 0+E 1+E 2)/2+Real.exp (2*t)*((E 3+E 4)/2+mass2/2*E 5+quartic/4*E 6+vacuum*E 7) :=
  (energy_decomposition ε a h hε ha hh hb q k P hq mass2 quartic vacuum t).trans
    (physical_sum mass2 quartic vacuum t hm hg hv E)

theorem physical_response (hm : 0 ≤ mass2) (hg : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    projectedResponse ε a h hε ha hh hb q k P hq mass2 quartic vacuum t =
      (r 0+r 1+r 2)/2+Real.exp (2*t)*((r 3+r 4)/2+mass2/2*r 5+quartic/4*r 6+vacuum*r 7) :=
  (response_decomposition ε a h hε ha hh hb q k P hq mass2 quartic vacuum t).trans
    (physical_sum mass2 quartic vacuum t hm hg hv r)

#print axioms meanMomentum_reduction
#print axioms factorRate_reduction
#print axioms meanInput_graph
#print axioms meanMomentum_graph
#print axioms projected_common_domains
#print axioms projected_momentum_graph
#print axioms energy_decomposition
#print axioms response_decomposition
#print axioms physical_sum
#print axioms physical_energy
#print axioms physical_response
end
end UnifiedTheory.Audit.KFCausalDisplacedPolynomialProjectedResponse
