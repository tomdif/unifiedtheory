/- Every weighted factor of the completed averaged energy lies in its
actual closed factor graph along the entire charge orbit. This includes
zero coefficients and imposes no charge-sector restriction. -/
import UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumGraph
import UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
import UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorOrbitFactorGraphs
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace growingOutputLp)
open UnifiedTheory.Audit.KFCausalClockFloorOrbitVacuumGraph (OrbitSpace physicalOrbit physicalOrbit_coe)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity (growingMap)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (graphFormVector_surjective)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport (growingOutput)

def factorOperator (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 8) : OrbitSpace →ₗ.[ℂ] OrbitSpace :=
  KFCausalLpClosedOperator.operator angleMeasure (energyFactor ε hε h modelDirections pointField i).closure

theorem factorOperator_closed (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hb : |h| ≤ Real.pi*ε) (i : Fin 8) : (factorOperator ε hε h i).IsClosed :=
  KFCausalLpClosedOperator.operator_closed angleMeasure _
    ((KFCausalClockFloorMatterClosure.energyFactor_closable ε h hε hb modelDirections pointField i).closure_isClosed)

theorem coordinates_detect_zero (y : EnergyOutputSpace) (hy : ∀ i, coordinateLp i y = 0) : y = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  have he (i : Fin 8) : ∀ᵐ θ ∂angleMeasure, y θ i = 0 := by
    filter_upwards [(coordinate i).coeFn_compLp y,
      Lp.eq_zero_iff_ae_eq_zero.mp (hy i)] with θ h1 h2
    exact h1.symm.trans h2
  filter_upwards [ae_all_iff.mpr he] with θ hθ
  exact PiLp.ext (hθ)

theorem coordinate_growing (i : Fin 8) (y : EnergyOutputSpace) :
    coordinateLp i (growingOutputLp y) = if i.val < 3 then 0 else coordinateLp i y := by
  apply Lp.ext
  filter_upwards [(coordinate i).coeFn_compLp (growingOutputLp y),
    growingOutput.coeFn_compLp y,(coordinate i).coeFn_compLp y,
    Lp.coeFn_zero (E := Hilbert) (p := 2) (μ := angleMeasure)] with θ h1 h2 h3 h0
  change (coordinate i).compLp (growingOutputLp y) θ = _
  rw [h1]
  change growingOutput.compLp y θ i = _
  rw [h2]
  by_cases hi : i.val < 3
  · simp only [growingOutput,KFCausalFiniteOutputRescaling.selected_apply,hi,
      not_true_eq_false,if_false,if_true,h0,Pi.zero_apply]
  · simpa only [growingOutput,KFCausalFiniteOutputRescaling.selected_apply,hi,
      not_false_eq_true,if_true,if_false] using h3.symm

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k
local notation "J" => embedding ε hε h hne hb m g k
local notation "A" => energyOutput ε hε h hne hb m g k
local notation "R" => physicalOrbit h hne

private theorem orbit_graph_of_base (t : ℝ) (u : V t) (i : Fin 8)
    (T : Hilbert →ₗ.[ℂ] Hilbert) (c : ℂ)
    (hbase : ∀ v : KFCausalClosedGraphForm.FormSpace
        (KFCausalClockFloorFormHamiltonian.formData ε hε h (hamiltonian_bound ε h hb) m g k t),
      (c • KFCausalClosedGraphForm.embedding _ v,KFCausalClosedGraphForm.energyOutput _ v i) ∈ T.graph) :
    (R (c • J t u),coordinateLp i (A t u)) ∈
      (KFCausalLpClosedOperator.operator angleMeasure T).graph := by
  obtain ⟨v,hv⟩ := graphFormVector_surjective ε hε h hne hb m g k t u
  let D := KFCausalClockFloorFormHamiltonian.formData ε hε h (hamiltonian_bound ε h hb) m g k t
  let j := KFCausalClosedGraphForm.embedding D
  let a := KFCausalClosedGraphForm.energyOutput D
  let sec := KFCausalClockFloorAveragedEnergy.sectionMap ε hε h (hamiltonian_bound ε h hb) hne m g k t v
  let jv := KFCausalClockFloorAveragedEnergy.embedding ε hε h (hamiltonian_bound ε h hb) hne m g k t
  have hjv : jv v = J t u := congrArg (J t) hv
  have hav : a.compLp sec = A t u := congrArg (A t) hv
  have ho := KFCausalClockFloorAveragedEnergy.orbit_lift_ae ε hε h (hamiltonian_bound ε h hb) hne m g k t v
  rw [KFCausalLpClosedOperator.operator_graph]
  filter_upwards [ho,a.coeFn_compLp sec,(coordinate i).coeFn_compLp (A t u),
    physicalOrbit_coe h hne (c • J t u)] with θ h1 h2 h3 h4
  have hout : A t u θ = a (sec θ) :=
    (congrArg (fun q : EnergyOutputSpace => q θ) hav).symm.trans h2
  have hin : R (c • J t u) θ = c • j (sec θ) := by
    exact h4.trans (((KFCausalPhysicalCircleAction.action h hne (2*Real.pi*θ)).map_smul _ _).trans
      (congrArg (fun f : Hilbert => c • f)
        ((congrArg (KFCausalPhysicalCircleAction.action h hne (2*Real.pi*θ)) hjv).symm.trans h1.symm)))
  have hg := hbase (sec θ)
  change (R (c • J t u) θ,(coordinate i).compLp (A t u) θ) ∈ _
  have hy : (coordinate i).compLp (A t u) θ = a (sec θ) i := h3.trans (congrArg (coordinate i) hout)
  exact (congrArg₂ (fun f q : Hilbert => (f,q) ∈
    T.graph) hin hy).mpr hg

theorem factor_graph (t : ℝ) (u : V t) (i : Fin 8) :
    (R (energyWeight m g k t i • J t u),coordinateLp i (A t u)) ∈
      (factorOperator ε hε h i).graph := by
  apply orbit_graph_of_base ε hε h hne hb m g k t u i
    (energyFactor ε hε h modelDirections pointField i).closure (energyWeight m g k t i)
  intro v
  exact KFCausalClockFloorJointEnergy.closedEnergy_component_graph ε hε h
    modelDirections pointField m g k t (hamiltonian_bound ε h hb)
    (KFCausalClosedGraphForm.embedding _ v) (KFCausalClosedGraphForm.energyOutput _ v) v.property i

def growingWeight (m g k : ℝ) (i : Fin 8) : ℂ := if i.val < 3 then 0 else energyWeight m g k 0 i

theorem growing_factor_graph (u : V 0) (i : Fin 8) :
    (R (growingWeight m g k i • J 0 u),coordinateLp i (growingMap ε hε h hne hb m g k u)) ∈
      (factorOperator ε hε h i).graph := by
  change (R (growingWeight m g k i • J 0 u),coordinateLp i (growingOutputLp (A 0 u))) ∈ _
  rw [coordinate_growing]
  by_cases hi : i.val < 3
  · simpa only [growingWeight,hi,if_true,zero_smul,map_zero] using
      (factorOperator ε hε h i).graph.zero_mem
  · simpa only [growingWeight,hi,if_false] using factor_graph ε hε h hne hb m g k 0 u i

#print axioms factorOperator_closed
#print axioms coordinates_detect_zero
#print axioms coordinate_growing
#print axioms factor_graph
#print axioms growing_factor_graph
end
end UnifiedTheory.Audit.KFCausalClockFloorOrbitFactorGraphs
