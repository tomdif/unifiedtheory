/- Extract the actual vacuum graph and its dissipative observation from
the completed averaged energy form in the physical zero-charge sector. -/
import UnifiedTheory.Audit.KFCausalClockFloorDriftDetection
import UnifiedTheory.Audit.KFCausalClockFloorVacuumOutputFaithful
import UnifiedTheory.Audit.KFCausalZeroChargeStructuredResponse
import UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorVacuumObservation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalProbabilityL2Mean (mean mean_comp mean_const mean_norm_le comp_const)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (growingPart)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (graphFormVector graphFormVector_surjective)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport (growingOutput timeOutput timeOutput_apply)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput
open UnifiedTheory.Audit.KFCausalClockFloorDriftDetection
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroSector zeroProjection_fixes)

private theorem const_pairing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (x y : E) :
    inner ℂ (Lp.const 2 angleMeasure x) (Lp.const 2 angleMeasure y) = inner ℂ x y :=
  ((Lp.constL 2 angleMeasure ℂ : E →L[ℂ] Lp E 2 angleMeasure).adjoint_inner_right x
    (Lp.const 2 angleMeasure y)).symm.trans (congrArg (inner ℂ x) (mean_const angleMeasure y))

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k
local notation "J" => embedding ε hε h hne hb m g k
local notation "A" => energyOutput ε hε h hne hb m g k
local notation "T" => formTransfer ε hε h hne hb m g k

def vacuum (t : ℝ) (u : V t) : Hilbert := (mean angleMeasure (A t u)) 7

theorem output_constant (t : ℝ) (u : V t) (hu : J t u ∈ zeroSector h hne) :
    A t u = Lp.const 2 angleMeasure (mean angleMeasure (A t u)) := by
  let v := Classical.choose (graphFormVector_surjective ε hε h hne hb m g k t u)
  have hv := Classical.choose_spec (graphFormVector_surjective ε hε h hne hb m g k t u)
  let j := KFCausalClockFloorAveragedEnergy.embedding ε hε h (hamiltonian_bound ε h hb) hne m g k t
  let a := KFCausalClockFloorAveragedEnergy.energyOutput ε hε h (hamiltonian_bound ε h hb) hne m g k t
  have hj : j v = J t u := congrArg (J t) hv
  have ha : a v = A t u := congrArg (A t) hv
  have hz : j v ∈ zeroSector h hne := (congrArg (fun f : Hilbert => f ∈ zeroSector h hne) hj).mpr hu
  let P := KFCausalZeroChargeStructuredResponse.project ε h hε hne hb m g k t
  have hp : P v = v := by
    apply KFCausalClockFloorAveragedEnergy.embedding_injective ε hε h (hamiltonian_bound ε h hb) hne m g k t
    change KFCausalStandingChargeOperator.zeroProjection h hne (j v) = j v
    exact zeroProjection_fixes h hne _ hz
  have he : a (P v) = Lp.const 2 angleMeasure (mean angleMeasure (a v)) :=
    KFCausalZeroChargeStructuredResponse.projected_output ε h hε hne hb m g k t v
  have he' : a v = Lp.const 2 angleMeasure (mean angleMeasure (a v)) :=
    (congrArg a hp).symm.trans he
  exact (congrArg (fun q : KFCausalAveragedOutputRescaling.EnergyOutputSpace =>
    q = Lp.const 2 angleMeasure (mean angleMeasure q)) ha).mp he'

theorem vacuum_graph (t : ℝ) (u : V t) (hu : J t u ∈ zeroSector h hne) :
    (energyWeight m g k t 7 • J t u,vacuum ε hε h hne hb m g k t u) ∈
      (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph := by
  let v := Classical.choose (graphFormVector_surjective ε hε h hne hb m g k t u)
  have hv := Classical.choose_spec (graphFormVector_surjective ε hε h hne hb m g k t u)
  let D := KFCausalClockFloorFormHamiltonian.formData ε hε h (hamiltonian_bound ε h hb) m g k t
  let j := KFCausalClosedGraphForm.embedding D
  let a := KFCausalClosedGraphForm.energyOutput D
  let sec := KFCausalClockFloorAveragedEnergy.sectionMap ε hε h (hamiltonian_bound ε h hb) hne m g k t v
  let jv := KFCausalClockFloorAveragedEnergy.embedding ε hε h (hamiltonian_bound ε h hb) hne m g k t
  have hvj : jv v = J t u := congrArg (J t) hv
  have hva : a.compLp sec = A t u := congrArg (A t) hv
  have hz : jv v ∈ zeroSector h hne := (congrArg (fun f : Hilbert => f ∈ zeroSector h hne) hvj).mpr hu
  have he : a.compLp sec = Lp.const 2 angleMeasure (mean angleMeasure (A t u)) :=
    hva.trans (output_constant ε hε h hne hb m g k t u hu)
  have hout : ∀ᵐ θ ∂angleMeasure, a (sec θ) = mean angleMeasure (A t u) := by
    filter_upwards [a.coeFn_compLp sec,Lp.coeFn_const 2 angleMeasure (mean angleMeasure (A t u))] with θ h1 h2
    exact h1.symm.trans ((congrArg (fun q : KFCausalAveragedOutputRescaling.EnergyOutputSpace => q θ) he).trans h2)
  have hj := KFCausalClockFloorAveragedEnergy.orbit_lift_ae ε hε h (hamiltonian_bound ε h hb) hne m g k t v
  obtain ⟨θ,hjθ,haθ⟩ := (hj.and hout).exists
  have hj' : j (sec θ) = J t u := hjθ.trans ((hz (2*Real.pi*θ)).trans hvj)
  have hg := KFCausalClockFloorVacuumOutputFaithful.closedEnergy_vacuum_graph ε hε h
    (hamiltonian_bound ε h hb) modelDirections pointField m g k t (j (sec θ)) (a (sec θ)) (sec θ).property
  exact (congrArg₂ (fun f q => (energyWeight m g k t 7 • f,q 7) ∈
    (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph) hj' haθ).mp hg

theorem vacuum_norm_bound (u : V 0) :
    ‖vacuum ε hε h hne hb m g k 0 u‖ ≤ ‖growingPart ε hε h hne hb m g k u‖ := by
  have he : growingOutput (mean angleMeasure (A 0 u)) 7 = (mean angleMeasure (A 0 u)) 7 := by
    simp only [growingOutput,KFCausalFiniteOutputRescaling.selected_apply]
    norm_num
  calc
    _ = ‖growingOutput (mean angleMeasure (A 0 u)) 7‖ := congrArg norm he.symm
    _ ≤ ‖growingOutput (mean angleMeasure (A 0 u))‖ := PiLp.norm_apply_le _ _
    _ = ‖mean angleMeasure (growingOutput.compLp (A 0 u))‖ :=
      congrArg norm (mean_comp angleMeasure growingOutput (A 0 u)).symm
    _ ≤ _ := mean_norm_le angleMeasure _

theorem vacuum_scaling (t : ℝ) (u : V 0) :
    vacuum ε hε h hne hb m g k t (T 0 t u) =
      (Real.exp t:ℂ) • vacuum ε hε h hne hb m g k 0 u := by
  unfold vacuum
  rw [transfer_energyOutput]
  change (mean angleMeasure ((timeOutput 0 t).compLp (A 0 u))) 7 = _
  rw [mean_comp,timeOutput_apply]
  norm_num

theorem coordinate_detection_bound (q : Output (Fin 8) Hilbert) :
    detection ε hε (q 7) ≤ -(inner ℂ q (classicalOutput ε hε q)).re := by
  have hn (i : Fin 8) : 0 ≤ -(inner ℂ (q i) (classicalFactor ε hε i (q i))).re := by
    unfold classicalFactor
    split
    · simp
    · exact detection_nonnegative ε hε _
  have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hn i)
    (Finset.mem_univ (7 : Fin 8))
  simpa only [PiLp.inner_apply,Complex.re_sum,Finset.sum_neg_distrib,
    classicalOutput_apply,classicalFactor,show ¬ (7 : Fin 8).val < 5 by decide,
    if_false,detection] using hs

theorem vacuum_detection_bound (t : ℝ) (u : V t) (hu : J t u ∈ zeroSector h hne) :
    detection ε hε (vacuum ε hε h hne hb m g k t u) ≤
      -(inner ℂ (A t u) ((classicalOutput ε hε).compLp (A t u))).re := by
  have he := output_constant ε hε h hne hb m g k t u hu
  conv_rhs => rw [he,comp_const,const_pairing]
  exact coordinate_detection_bound ε hε _

#print axioms output_constant
#print axioms vacuum_graph
#print axioms vacuum_norm_bound
#print axioms vacuum_scaling
#print axioms coordinate_detection_bound
#print axioms vacuum_detection_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorVacuumObservation
