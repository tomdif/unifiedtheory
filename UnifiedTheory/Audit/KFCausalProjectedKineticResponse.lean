/- Projected kinetic responses satisfy the actual kinetic graph theorem.
Closed-graph integration constructs the factor outputs of the projected
input and its projected pure-clock momentum. No preservation of a finite
packet span by charge projection is assumed. -/
import UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedKineticResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure orbit orbitState_coe orbit_mean)
open UnifiedTheory.Audit.KFCausalProbabilityL2Mean (mean_integral)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group action action_strong_continuous)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroProjection)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph (clockMomentum_closed)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf clockHalf_selfAdjoint)
open UnifiedTheory.Audit.KFCausalCoherentFactorResponseBounds (kineticIndex)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse
  (StructuredState input momentumOutput inputOrbit momentumOrbit momentum_graph
    inputOrbit_continuous momentumOrbit_continuous inputOrbit_graph momentumOrbit_graph)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian (meanInput meanMomentum factorRate factorEnergy)

theorem integral_closed_graph (T : Hilbert →ₗ.[ℂ] Hilbert) (hT : T.IsClosed)
    (f g : ℝ → Hilbert) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ θ, (f θ,g θ) ∈ T.graph) :
    (∫ θ, f θ ∂angleMeasure,∫ θ, g θ ∂angleMeasure) ∈ T.graph := by
  letI : CompleteSpace T.graph := hT.completeSpace_coe
  let v : ℝ → T.graph := fun θ => ⟨(f θ,g θ),hfg θ⟩
  have hv : Continuous v := (hf.prodMk hg).subtype_mk _
  have hi := (continuous_angle_memLp v hv).integrable (by norm_num)
  let z : T.graph := ∫ θ, v θ ∂angleMeasure
  let p : T.graph →L[ℂ] Hilbert := (ContinuousLinearMap.fst ℂ Hilbert Hilbert).comp T.graph.subtypeL
  let q : T.graph →L[ℂ] Hilbert := (ContinuousLinearMap.snd ℂ Hilbert Hilbert).comp T.graph.subtypeL
  have hp : (∫ θ, f θ ∂angleMeasure) = p z := p.integral_comp_comm hi
  have hq : (∫ θ, g θ ∂angleMeasure) = q z := q.integral_comp_comm hi
  rw [hp,hq]
  exact z.property

theorem action_integral (h : ℝ) (hh : h ≠ 0) (f : Hilbert) :
    (∫ θ, action h hh (2*Real.pi*θ) f ∂angleMeasure) = zeroProjection h hh f := by
  have he := orbit_mean (group h hh) (2*Real.pi) (by positivity) f
  exact (integral_congr_ae (orbitState_coe (group h hh) (2*Real.pi) f)).symm.trans
    ((mean_integral angleMeasure (orbit (group h hh) (2*Real.pi) f)).symm.trans he)

theorem averaged_graph (h : ℝ) (hh : h ≠ 0) (T : Hilbert →ₗ.[ℂ] Hilbert) (hT : T.IsClosed)
    (f : Hilbert) (g : ℝ → Hilbert) (hg : Continuous g)
    (hfg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ T.graph) :
    (zeroProjection h hh f,∫ θ, g θ ∂angleMeasure) ∈ T.graph := by
  rw [← action_integral h hh f]
  exact integral_closed_graph T hT _ g
    ((action_strong_continuous h hh f).comp (continuous_const.mul continuous_id)) hg hfg

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)
local notation "g" => meanInput ε h hε hh hb S
local notation "k" => meanMomentum ε h hε hh hb S
local notation "f" => zeroProjection h hh (input ε h hε hh S)
local notation "b" => zeroProjection h hh (momentumOutput ε h hε hh S)

theorem input_kinetic_graph (i : Fin 4) :
    (f,g (kineticIndex i)) ∈ (clockMomentum ε h (modelDirections i)).graph := by
  apply averaged_graph h hh _ (clockMomentum_closed ε hε h (modelDirections i))
    (input ε h hε hh S) (inputOrbit ε h hε hh hb S (kineticIndex i))
    (inputOrbit_continuous ε h hε hh hb S (kineticIndex i))
  intro θ
  have hx := inputOrbit_graph ε h hε hh hb S θ (kineticIndex i)
  fin_cases i <;> exact hx

theorem momentum_kinetic_graph (i : Fin 4) :
    (b,k (kineticIndex i)) ∈ (clockMomentum ε h (modelDirections i)).graph := by
  apply averaged_graph h hh _ (clockMomentum_closed ε hε h (modelDirections i))
    (momentumOutput ε h hε hh S) (momentumOrbit ε h hε hh hb S (kineticIndex i))
    (momentumOrbit_continuous ε h hε hh hb S (kineticIndex i))
  intro θ
  have hx := momentumOrbit_graph ε h hε hh hb S θ (kineticIndex i)
  fin_cases i <;> exact hx

theorem input_clock_graph : (f,g 0) ∈ (clockHalf ε).graph :=
  averaged_graph h hh _ (clockHalf_selfAdjoint ε).isClosed (input ε h hε hh S)
    (inputOrbit ε h hε hh hb S 0) (inputOrbit_continuous ε h hε hh hb S 0)
    (fun θ => inputOrbit_graph ε h hε hh hb S θ 0)

theorem momentum_clock_graph : (b,k 0) ∈ (clockHalf ε).graph :=
  averaged_graph h hh _ (clockHalf_selfAdjoint ε).isClosed (momentumOutput ε h hε hh S)
    (momentumOrbit ε h hε hh hb S 0) (momentumOrbit_continuous ε h hε hh hb S 0)
    (fun θ => momentumOrbit_graph ε h hε hh hb S θ 0)

theorem kinetic_response (i : Fin 4) : factorRate ε h hε hh hb S (kineticIndex i) =
    KFCausalClockFloorPureClockKineticResponse.response ε hε (g (kineticIndex i)) :=
  KFCausalClockFloorPureClockKineticResponse.weak_response ε hε h hh (modelDirections i) f _ b _
    (input_kinetic_graph ε h hε hh hb S i)
    (KFCausalPureClockZeroProjection.projected_graph ε hε h hh _ _ (momentum_graph ε h hε hh S))
    (momentum_kinetic_graph ε h hε hh hb S i)

theorem kinetic_bounds (i : Fin 4) :
    0 ≤ factorRate ε h hε hh hb S (kineticIndex i) ∧
      factorRate ε h hε hh hb S (kineticIndex i) ≤ (1/(4*ε))*factorEnergy ε h hε hh hb S (kineticIndex i) := by
  rw [kinetic_response ε h hε hh hb S i]
  exact KFCausalClockFloorPureClockKineticResponse.response_bounds ε hε (g (kineticIndex i))

#print axioms integral_closed_graph
#print axioms action_integral
#print axioms averaged_graph
#print axioms input_kinetic_graph
#print axioms momentum_kinetic_graph
#print axioms input_clock_graph
#print axioms momentum_clock_graph
#print axioms kinetic_response
#print axioms kinetic_bounds
end
end UnifiedTheory.Audit.KFCausalProjectedKineticResponse
