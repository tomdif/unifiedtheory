/- At zero couplings the residual output closure is exactly the static
output closure. The reconstruction theorem therefore identifies the actual
free form domain with the intersection of two explicit maximal root domains.
The reconstruction bound |h| ≤ π ε / 3 is retained explicitly. -/
import UnifiedTheory.Audit.KFCausalClockFloorResidualFormReconstruction
import UnifiedTheory.Audit.KFCausalClockFloorStaticOutputClosure
import UnifiedTheory.Audit.KFCausalClockFloorFreeBalancedEnergy

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFreeFormSum
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp)
open KFCausalPhysicalEnergyTransport (timeOutput staticOutput)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalClockFloorStaticPotentialOutputClosure (selectedOutput selectedOutputLp)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedHamiltonian (graphFormVector graphFormVector_surjective)

private theorem selected_time_free (t : ℝ) (x : EnergyOutputSpace)
    (hz : ∀ i : Fin 8, 5 ≤ i.val → coordinateLp i x = 0) :
    selectedOutputLp (timeOutputLp 0 t x) = staticOutputLp x := by
  have he (i : Fin 8) (hi : 5 ≤ i.val) : ∀ᵐ θ ∂angleMeasure, x θ i = 0 := by
    filter_upwards [(coordinate i).coeFn_compLp x,
      Lp.eq_zero_iff_ae_eq_zero.mp (hz i hi)] with θ h1 h2
    exact h1.symm.trans h2
  apply Lp.ext
  filter_upwards [selectedOutput.coeFn_compLp (timeOutputLp 0 t x),
    (timeOutput 0 t).coeFn_compLp x,staticOutput.coeFn_compLp x,
    he 5 (by decide),he 6 (by decide),he 7 (by decide)] with θ h1 h2 h3 h5 h6 h7
  change selectedOutput.compLp (timeOutputLp 0 t x) θ = staticOutput.compLp x θ
  rw [h1]
  change selectedOutput ((timeOutput 0 t).compLp x θ) = _
  rw [h2,h3]
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [selectedOutput,KFCausalFiniteOutputRescaling.selected_apply,
    KFCausalClockFloorStaticPotentialOutputClosure.retained,
    KFCausalPhysicalEnergyTransport.timeOutput_apply,staticOutput,h5,h6,h7]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (t : ℝ)
local notation "V" => FormSpace ε hε h hh hb 0 0 0 0
local notation "J" => embedding ε hε h hh hb 0 0 0 0
local notation "A" => energyOutput ε hε h hh hb 0 0 0 0

theorem residual_source_eq_static (u : V) :
    KFCausalClockFloorStaticPotentialOutputClosure.sourceMap ε hε h hh hb 0 0 0 t u =
      staticOutputLp (A u) := by
  change selectedOutputLp (timeOutputLp 0 t (A u)) = staticOutputLp (A u)
  exact selected_time_free t (A u)
    (KFCausalClockFloorFreeBalancedEnergy.inactive_output ε hε h hh hb 0 u)

theorem residual_initialGraph_eq_static :
    KFCausalClockFloorStaticPotentialOutputClosure.initialGraph ε hε h hh hb 0 0 0 t =
      KFCausalClockFloorStaticOutputClosure.initialGraph ε hε h hh hb 0 0 0 0 := by
  let B := (J).prod (KFCausalClockFloorStaticPotentialOutputClosure.sourceMap ε hε h hh hb 0 0 0 t)
  let C := (KFCausalClockFloorAveragedEnergy.embedding ε hε h
    (hamiltonian_bound ε h hb) hh 0 0 0 0).prod
      (KFCausalClockFloorStaticRootSource.staticOutput ε hε h hh hb 0 0 0 0)
  have he : (fun v => B (graphFormVector ε hε h hh hb 0 0 0 0 v)) = (fun v => C v) := by
    funext v
    apply Prod.ext
    · exact KFCausalClockFloorAveragedHamiltonian.graphFormVector_embedding ε hε h hh hb 0 0 0 0 v
    · exact (residual_source_eq_static ε hε h hh hb t _).trans
        (congrArg staticOutputLp
          (KFCausalClockFloorAveragedHamiltonian.graphFormVector_output ε hε h hh hb 0 0 0 0 v))
  apply SetLike.coe_injective
  exact ((graphFormVector_surjective ε hε h hh hb 0 0 0 0).range_comp B).symm.trans
    (congrArg Set.range he)

theorem residual_operator_eq_static :
    KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hb 0 0 0 t =
      KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hb 0 0 0 0 := by
  apply LinearPMap.eq_of_eq_graph
  exact (KFCausalClockFloorStaticPotentialOutputClosure.operator_graph ε hε h hh hb 0 0 0 t).trans
    ((congrArg Submodule.topologicalClosure (residual_initialGraph_eq_static ε hε h hh hb t)).trans
      (KFCausalClockFloorStaticOutputClosure.operator_graph ε hε h hh hb 0 0 0 0).symm)

theorem residual_domain_iff (f : Hilbert) :
    f ∈ (KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hb 0 0 0 t).domain ↔
      f ∈ (KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h).domain := by
  rw [residual_operator_eq_static ε hε h hh hb t]
  exact KFCausalClockFloorStaticOutputClosure.operator_domain ε hε h hh hb 0 0 0 0 f

/-- Both implications for the actual free form, on the full Hilbert space.
The operators on the right are the already identified maximal multiplier roots. -/
theorem free_form_domain (hb' : |h| ≤ Real.pi*ε/3) (f : Hilbert) :
    f ∈ (KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
      (hamiltonian_bound ε h (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb'))
      hh 0 0 0 t).domain ↔
      f ∈ (KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h).domain ∧
      f ∈ (KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h).domain := by
  rw [KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_root_inter_residual
    ε hε h hh hb' 0 0 0 t f,residual_domain_iff]

#print axioms residual_source_eq_static
#print axioms residual_initialGraph_eq_static
#print axioms residual_operator_eq_static
#print axioms residual_domain_iff
#print axioms free_form_domain
end
end UnifiedTheory.Audit.KFCausalClockFloorFreeFormSum
