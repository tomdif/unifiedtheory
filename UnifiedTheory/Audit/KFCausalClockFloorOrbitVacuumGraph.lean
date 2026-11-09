/- Extract the vacuum operator along the entire physical charge orbit.
The L2 graph retains every angle, so no zero-charge restriction or
replacement by the mean vacuum output is needed. -/
import UnifiedTheory.Audit.KFCausalLpClosedOperator
import UnifiedTheory.Audit.KFCausalClockFloorVacuumObservation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumGraph
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure orbit orbitState_coe)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace growingOutputLp)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (growingPart)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (graphFormVector_surjective)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport (growingOutput timeOutput timeOutput_apply)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport (timeOutputLp)

abbrev OrbitSpace := Lp Hilbert 2 angleMeasure
def coordinate : Output (Fin 8) Hilbert →L[ℂ] Hilbert := PiLp.proj 2 (fun _ : Fin 8 => Hilbert) 7
def coordinateLp : EnergyOutputSpace →L[ℂ] OrbitSpace := coordinate.compLpL 2 angleMeasure
def physicalOrbit (h : ℝ) (hne : h ≠ 0) : Hilbert →ₗᵢ[ℂ] OrbitSpace :=
  orbit (KFCausalPhysicalCircleAction.group h hne) (2*Real.pi)
def vacuumOperator (ε : ℝ) (hε : 0 < ε) (h : ℝ) : OrbitSpace →ₗ.[ℂ] OrbitSpace :=
  KFCausalLpClosedOperator.operator angleMeasure
    (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h)

theorem physicalOrbit_coe (h : ℝ) (hne : h ≠ 0) (f : Hilbert) :
    physicalOrbit h hne f =ᵐ[angleMeasure] fun θ =>
      KFCausalPhysicalCircleAction.action h hne (2*Real.pi*θ) f :=
  orbitState_coe (KFCausalPhysicalCircleAction.group h hne) (2*Real.pi) f

theorem vacuumOperator_closed (ε : ℝ) (hε : 0 < ε) (h : ℝ) : (vacuumOperator ε hε h).IsClosed :=
  KFCausalLpClosedOperator.operator_closed angleMeasure _
    (KFCausalClockFloorBoundedInverse.orderedExponential_closed ε hε h)

theorem vacuumOperator_graph_zero (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (f : OrbitSpace) (hf : (f,0) ∈ (vacuumOperator ε hε h).graph) : f = 0 :=
  KFCausalLpClosedOperator.operator_graph_zero angleMeasure _
    (KFCausalClockFloorVacuumOutputFaithful.ordered_graph_zero ε hε h) f hf

theorem coordinate_growing_bound (q : EnergyOutputSpace) : ‖coordinateLp q‖ ≤ ‖growingOutputLp q‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coordinate.coeFn_compLp q,growingOutput.coeFn_compLp q] with θ h1 h2
  change ‖coordinate.compLp q θ‖ ≤ ‖growingOutput.compLp q θ‖
  rw [h1,h2]
  have he : growingOutput (q θ) 7 = coordinate (q θ) := by
    simp only [growingOutput,KFCausalFiniteOutputRescaling.selected_apply]
    norm_num
    rfl
  rw [← he]
  exact PiLp.norm_apply_le _ _

theorem coordinate_time (s t : ℝ) (q : EnergyOutputSpace) :
    coordinateLp (timeOutputLp s t q) = (Real.exp (t-s):ℂ) • coordinateLp q := by
  apply Lp.ext
  filter_upwards [coordinate.coeFn_compLp (timeOutputLp s t q),
    (timeOutput s t).coeFn_compLp q,coordinate.coeFn_compLp q,
    Lp.coeFn_smul (Real.exp (t-s):ℂ) (coordinateLp q)] with θ h1 h2 h3 h4
  change coordinate.compLp (timeOutputLp s t q) θ = _
  rw [h1,h4]
  change coordinate ((timeOutput s t).compLp q θ) = (Real.exp (t-s):ℂ) • coordinate.compLp q θ
  rw [h2,h3]
  change timeOutput s t (q θ) 7 = _
  rw [timeOutput_apply]
  norm_num
  rfl

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k
local notation "J" => embedding ε hε h hne hb m g k
local notation "A" => energyOutput ε hε h hne hb m g k
local notation "R" => physicalOrbit h hne

def vacuum (t : ℝ) (u : V t) : OrbitSpace := coordinateLp (A t u)

theorem vacuum_graph (t : ℝ) (u : V t) :
    (R (energyWeight m g k t 7 • J t u),vacuum ε hε h hne hb m g k t u) ∈
      (vacuumOperator ε hε h).graph := by
  obtain ⟨v,hv⟩ := graphFormVector_surjective ε hε h hne hb m g k t u
  let D := KFCausalClockFloorFormHamiltonian.formData ε hε h (hamiltonian_bound ε h hb) m g k t
  let j := KFCausalClosedGraphForm.embedding D
  let a := KFCausalClosedGraphForm.energyOutput D
  let sec := KFCausalClockFloorAveragedEnergy.sectionMap ε hε h (hamiltonian_bound ε h hb) hne m g k t v
  let jv := KFCausalClockFloorAveragedEnergy.embedding ε hε h (hamiltonian_bound ε h hb) hne m g k t
  have hjv : jv v = J t u := congrArg (J t) hv
  have hav : a.compLp sec = A t u := congrArg (A t) hv
  have ho := KFCausalClockFloorAveragedEnergy.orbit_lift_ae ε hε h (hamiltonian_bound ε h hb) hne m g k t v
  rw [vacuumOperator,KFCausalLpClosedOperator.operator_graph]
  filter_upwards [ho,a.coeFn_compLp sec,coordinate.coeFn_compLp (A t u),
    physicalOrbit_coe h hne (energyWeight m g k t 7 • J t u)] with θ h1 h2 h3 h4
  have hout : A t u θ = a (sec θ) :=
    (congrArg (fun q : EnergyOutputSpace => q θ) hav).symm.trans h2
  have hin : R (energyWeight m g k t 7 • J t u) θ = energyWeight m g k t 7 • j (sec θ) := by
    exact h4.trans (((KFCausalPhysicalCircleAction.action h hne (2*Real.pi*θ)).map_smul _ _).trans
      (congrArg (fun f : Hilbert => energyWeight m g k t 7 • f)
        ((congrArg (KFCausalPhysicalCircleAction.action h hne (2*Real.pi*θ)) hjv).symm.trans h1.symm)))
  have hg := KFCausalClockFloorVacuumOutputFaithful.closedEnergy_vacuum_graph ε hε h
    (hamiltonian_bound ε h hb) modelDirections pointField m g k t (j (sec θ)) (a (sec θ)) (sec θ).property
  change (R (energyWeight m g k t 7 • J t u) θ,coordinate.compLp (A t u) θ) ∈ _
  have hvac : coordinate.compLp (A t u) θ = a (sec θ) 7 := h3.trans (congrArg coordinate hout)
  exact (congrArg₂ (fun f q : Hilbert => (f,q) ∈
    (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph) hin hvac).mpr hg

theorem vacuum_norm_bound (u : V 0) :
    ‖vacuum ε hε h hne hb m g k 0 u‖ ≤ ‖growingPart ε hε h hne hb m g k u‖ :=
  coordinate_growing_bound (A 0 u)

theorem vacuum_scaling (t : ℝ) (u : V 0) :
    vacuum ε hε h hne hb m g k t (formTransfer ε hε h hne hb m g k 0 t u) =
      (Real.exp t:ℂ) • vacuum ε hε h hne hb m g k 0 u := by
  have ho := transfer_energyOutput ε hε h hne hb m g k 0 t u
  exact (congrArg coordinateLp ho).trans (by simpa only [sub_zero] using coordinate_time 0 t (A 0 u))

#print axioms physicalOrbit_coe
#print axioms vacuumOperator_closed
#print axioms vacuumOperator_graph_zero
#print axioms coordinate_growing_bound
#print axioms coordinate_time
#print axioms vacuum_graph
#print axioms vacuum_norm_bound
#print axioms vacuum_scaling
end
end UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumGraph
