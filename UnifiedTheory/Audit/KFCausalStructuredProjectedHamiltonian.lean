/- The complete projected eight-factor Hamiltonian form on finite
complex displaced superpositions. The three ordered factors use the
proved whole-clock response kernels. All five clock/kinetic factors and
all physical weights remain in the equality. -/
import UnifiedTheory.Audit.KFCausalProjectedFactorMeans
import UnifiedTheory.Audit.KFCausalStructuredReducedResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse
  (StructuredState input momentumOutput inputOrbit momentumOrbit inputLift momentumLift
    inputOrbit_continuous momentumOrbit_continuous inputOrbit_graph momentumOrbit_graph)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight energyWeight_norm_square)
open UnifiedTheory.Audit.KFCausalZeroChargeStructuredResponse (output project)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)
open UnifiedTheory.Audit.KFCausalChargeResponseFubini (angles measure)

private theorem physical_sum (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) (r : Fin 8 → ℝ) :
    (∑ i : Fin 8, ‖energyWeight mass2 quartic vacuum t i‖^2*r i) =
      (r 0+r 1+r 2)/2+Real.exp (2*t)*((r 3+r 4)/2+mass2/2*r 5+quartic/4*r 6+vacuum*r 7) := by
  simp_rw [energyWeight_norm_square mass2 quartic vacuum t hm hq hv]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  ring!

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)

def meanInput (i : Fin 8) : Hilbert := ∫ θ, inputOrbit ε h hε hh hb S i θ ∂angleMeasure
def meanMomentum (i : Fin 8) : Hilbert := ∫ θ, momentumOrbit ε h hε hh hb S i θ ∂angleMeasure
def factorEnergy (i : Fin 8) : ℝ := ‖meanInput ε h hε hh hb S i‖^2
def factorRate (i : Fin 8) : ℝ := (-2/h)*(inner ℂ
  (meanInput ε h hε hh hb S i) (meanMomentum ε h hε hh hb S i)).im

def reducedRate (n : Fin 3) : ℝ := (∫ a, ∫ x : Configuration,
  KFCausalStructuredReducedResponse.density ε h hε hh S S n true a x ∂volume ∂angles).re

variable (mass2 quartic vacuum t : ℝ)
local notation "out" => output ε h hε hh hb mass2 quartic vacuum t
local notation "P" => project ε h hε hh hb mass2 quartic vacuum t
local notation "u" => inputLift ε h hε hh hb S mass2 quartic vacuum t
local notation "v" => momentumLift ε h hε hh hb S mass2 quartic vacuum t
local notation "E" => factorEnergy ε h hε hh hb S
local notation "r" => factorRate ε h hε hh hb S
local notation "R" => reducedRate ε h hε hh S

def projectedEnergy : ℝ := ‖out (P u)‖^2
def projectedResponse : ℝ := (-2/h)*(inner ℂ (out (P u)) (out (P v))).im

theorem energy_decomposition : projectedEnergy ε h hε hh hb S mass2 quartic vacuum t =
    ∑ i : Fin 8, ‖energyWeight mass2 quartic vacuum t i‖^2*E i :=
  KFCausalProjectedFactorMeans.projected_lift_energy ε h hε hh hb mass2 quartic vacuum t
    (input ε h hε hh S) (inputOrbit ε h hε hh hb S)
    (inputOrbit_continuous ε h hε hh hb S) (inputOrbit_graph ε h hε hh hb S)

theorem response_decomposition : projectedResponse ε h hε hh hb S mass2 quartic vacuum t =
    ∑ i : Fin 8, ‖energyWeight mass2 quartic vacuum t i‖^2*r i :=
  KFCausalProjectedFactorMeans.projected_lift_response ε h hε hh hb mass2 quartic vacuum t
    (input ε h hε hh S) (momentumOutput ε h hε hh S)
    (inputOrbit ε h hε hh hb S) (momentumOrbit ε h hε hh hb S)
    (inputOrbit_continuous ε h hε hh hb S) (momentumOrbit_continuous ε h hε hh hb S)
    (inputOrbit_graph ε h hε hh hb S) (momentumOrbit_graph ε h hε hh hb S)

theorem physical_energy (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    projectedEnergy ε h hε hh hb S mass2 quartic vacuum t =
      (E 0+E 1+E 2)/2+Real.exp (2*t)*((E 3+E 4)/2+mass2/2*E 5+quartic/4*E 6+vacuum*E 7) :=
  (energy_decomposition ε h hε hh hb S mass2 quartic vacuum t).trans
    (physical_sum mass2 quartic vacuum t hm hq hv E)

theorem physical_response (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    projectedResponse ε h hε hh hb S mass2 quartic vacuum t =
      (r 0+r 1+r 2)/2+Real.exp (2*t)*((r 3+r 4)/2+mass2/2*r 5+quartic/4*r 6+vacuum*r 7) :=
  (response_decomposition ε h hε hh hb S mass2 quartic vacuum t).trans
    (physical_sum mass2 quartic vacuum t hm hq hv r)

theorem growing_weak_integral (n : Fin 3) :
    (∫ z, KFCausalStructuredChargeResponse.weakDensity ε h hε hh S S n z ∂measure) =
      (r (index n) : ℂ) := KFCausalStructuredChargeResponse.diagonal_response ε h hε hh hb S n

theorem growing_reduced_integral (n : Fin 3) :
    (∫ a, ∫ x : Configuration, KFCausalStructuredReducedResponse.density ε h hε hh S S n true a x ∂volume ∂angles) =
      (r (index n) : ℂ) := KFCausalStructuredReducedResponse.diagonal_response ε h hε hh hb S n

include hb in
theorem reduced_rate_eq (n : Fin 3) : R n = r (index n) :=
  congrArg Complex.re (growing_reduced_integral ε h hε hh hb S n)

theorem full_reduced_response (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    projectedResponse ε h hε hh hb S mass2 quartic vacuum t =
      (r 0+r 1+r 2)/2+Real.exp (2*t)*((r 3+r 4)/2+mass2/2*R 1+quartic/4*R 2+vacuum*R 0) := by
  rw [physical_response ε h hε hh hb S mass2 quartic vacuum t hm hq hv,
    reduced_rate_eq ε h hε hh hb S 1,reduced_rate_eq ε h hε hh hb S 2,reduced_rate_eq ε h hε hh hb S 0]
  rfl

#print axioms energy_decomposition
#print axioms response_decomposition
#print axioms physical_energy
#print axioms physical_response
#print axioms growing_weak_integral
#print axioms growing_reduced_integral
#print axioms reduced_rate_eq
#print axioms full_reduced_response
end
end UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian
