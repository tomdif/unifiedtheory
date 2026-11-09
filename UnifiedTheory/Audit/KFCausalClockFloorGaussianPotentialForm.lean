/- Clock Gaussian actions on the completed ordered-potential form. Natural
graph transport descends from the reference form to the potential output
closure, where the radial kinetic rows vanish identically and the half-shift
Gaussian adjoint identity holds with zero defect. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingOutputPairing
import UnifiedTheory.Audit.KFCausalClockFloorPotentialHamiltonian

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianPotentialForm
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalFiniteOutputRescaling (selected_apply)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorGaussianGrowingTransport (action)
open KFCausalAnalyticClockSecondTransport (firstShift)
open KFCausalClockFloorChartPhasePairing (orderedOutput orderedOutputLp)
open KFCausalClockFloorGaussianGrowingForm
  (growingAction growingActionLp growingAction_apply reference_stability)
open KFCausalClockFloorGaussianGrowingOutputPairing (output_pairing orbit_pairing)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)

private theorem range_closure_transport
    {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (j : V →L[ℂ] X) (b : V →L[ℂ] Y) (d : X →L[ℂ] X) (l : Y →L[ℂ] Y)
    (hs : ∀ u, ∃ v, j v=d (j u) ∧ b v=l (b u))
    (x : X) (y : Y) (hxy : (x,y) ∈ (j.prod b).toLinearMap.range.topologicalClosure) :
    (d x,l y) ∈ (j.prod b).toLinearMap.range.topologicalClosure := by
  let S := (j.prod b).toLinearMap.range
  let P := d.prodMap l
  have hS : S ≤ S.topologicalClosure.comap P.toLinearMap := by
    rintro z ⟨u,rfl⟩
    obtain ⟨v,hvJ,hvB⟩ := hs u
    apply S.le_topologicalClosure
    exact ⟨v,Prod.ext hvJ hvB⟩
  exact S.topologicalClosure_minimal hS (S.isClosed_topologicalClosure.preimage P.continuous) hxy

private theorem point_ordered_idem (z : Output (Fin 8) Hilbert) :
    orderedOutput (orderedOutput z)=orderedOutput z := by
  apply PiLp.ext
  intro i
  by_cases h5 : i.val < 5 <;>
    simp only [orderedOutput,selected_apply,h5,not_true_eq_false,not_false_eq_true,if_true,if_false]

private theorem lp_ordered_idem (z : EnergyOutputSpace) :
    orderedOutputLp (orderedOutputLp z)=orderedOutputLp z := by
  let w := orderedOutputLp z
  apply Lp.ext
  filter_upwards [orderedOutput.coeFn_compLp w,orderedOutput.coeFn_compLp z] with θ h1 h2
  change (orderedOutput.compLp w) θ=(orderedOutput.compLp z) θ
  rw [h1]
  change orderedOutput ((orderedOutput.compLp z) θ)=(orderedOutput.compLp z) θ
  rw [h2,point_ordered_idem]

private theorem coordinate_ordered (i : Fin 8) (y : EnergyOutputSpace) :
    coordinateLp i (orderedOutputLp y)=if i.val<5 then 0 else coordinateLp i y := by
  apply Lp.ext
  filter_upwards [(coordinate i).coeFn_compLp (orderedOutputLp y),
    orderedOutput.coeFn_compLp y,(coordinate i).coeFn_compLp y,
    Lp.coeFn_zero (E := Hilbert) (p := 2) (μ := angleMeasure)] with θ h1 h2 h3 h0
  change (coordinate i).compLp (orderedOutputLp y) θ=_
  rw [h1]
  change orderedOutput.compLp y θ i=_
  rw [h2]
  by_cases hi : i.val<5
  · simp only [orderedOutput,selected_apply,hi,not_true_eq_false,if_false,if_true,h0,Pi.zero_apply]
  · simpa only [orderedOutput,selected_apply,hi,not_false_eq_true,if_true,if_false] using h3.symm

variable (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a)
  (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (y : ℝ) (m g k : ℝ)

theorem orderedOutput_growingAction (z : Output (Fin 8) Hilbert) :
    orderedOutput (growingAction ε a ha h y z)=
      growingAction ε a ha h y (orderedOutput z) := by
  apply PiLp.ext
  intro i
  by_cases h5 : i.val < 5
  · by_cases h3 : i.val < 3 <;>
      simp only [orderedOutput,selected_apply,growingAction_apply,h5,h3,
        not_true_eq_false,if_true,if_false,map_zero]
  · have h3 : ¬ i.val < 3 := by omega
    simp only [orderedOutput,selected_apply,growingAction_apply,h5,h3,
      not_false_eq_true,if_true,if_false]

theorem orderedOutputLp_growingActionLp (z : EnergyOutputSpace) :
    orderedOutputLp (growingActionLp ε a ha h y z)=
      growingActionLp ε a ha h y (orderedOutputLp z) := by
  let g := growingActionLp ε a ha h y z
  let o := orderedOutputLp z
  apply Lp.ext
  filter_upwards [orderedOutput.coeFn_compLp g,(growingAction ε a ha h y).coeFn_compLp z,
    (growingAction ε a ha h y).coeFn_compLp o,orderedOutput.coeFn_compLp z]
    with θ h1 h2 h3 h4
  change (orderedOutput.compLp g) θ=((growingAction ε a ha h y).compLp o) θ
  rw [h1,h3]
  change orderedOutput (((growingAction ε a ha h y).compLp z) θ)=
    growingAction ε a ha h y ((orderedOutput.compLp z) θ)
  rw [h2,h4,orderedOutput_growingAction]

private theorem ordered_growing_eq (p q : EnergyOutputSpace)
    (hpq : p=growingActionLp ε a ha h y q) :
    orderedOutputLp p=growingActionLp ε a ha h y (orderedOutputLp q) := by
  rw [hpq,orderedOutputLp_growingActionLp]

local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hb m g k 0
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb m g k 0
local notation "RB" => KFCausalClockFloorAveragedRegularity.growingMap ε hε h hh hb m g k
local notation "PA" => KFCausalClockFloorPotentialOutputClosure.potentialMap ε hε h hh hb m g k
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hb m g k
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hb m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hb m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD

private theorem potential_reference_stability (u : RV) :
    ∃ v : RV, RJ v=action ε a ha y (RJ u) ∧ PA v=growingActionLp ε a ha h y (PA u) := by
  let hs := reference_stability ε hε a ha h hh hb y m g k u
  let v := Classical.choose hs
  have hv := Classical.choose_spec hs
  exact ⟨v,hv.1,ordered_growing_eq ε a ha h y (RB v) (RB u) hv.2⟩

theorem potential_graph_action (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (Tpot).graph) :
    (action ε a ha y f,growingActionLp ε a ha h y z) ∈ (Tpot).graph := by
  rw [KFCausalClockFloorPotentialOutputClosure.operator_graph] at hz ⊢
  exact range_closure_transport (RJ) (PA) (action ε a ha y) (growingActionLp ε a ha h y)
    (potential_reference_stability ε hε a ha h hh hb y m g k) f z hz

def formAction : PV →L[ℂ] PV :=
  KFCausalClosedGraphDiagonalAction.action PD (action ε a ha y) (growingActionLp ε a ha h y)
    (potential_graph_action ε hε a ha h hh hb y m g k)

theorem formAction_embedding (u : PV) :
    PJ (formAction ε hε a ha h hh hb y m g k u)=action ε a ha y (PJ u) := rfl

theorem formAction_output (u : PV) :
    PB (formAction ε hε a ha h hh hb y m g k u)=growingActionLp ε a ha h y (PB u) := rfl

theorem ordered_output_pairing (f g : Output (Fin 8) Hilbert) :
    inner ℂ (growingAction ε a ha h 0 (orderedOutput f)) (orderedOutput g)=
      inner ℂ (orderedOutput f) (growingAction ε a ha h h (orderedOutput g)) := by
  have hp := output_pairing ε a ha h (orderedOutput f) (orderedOutput g)
  have h3 : orderedOutput f 3=0 := by
    simp only [orderedOutput,selected_apply, show (3:Fin 8).val < 5 by decide, not_true_eq_false, if_false]
  have h4 : orderedOutput f 4=0 := by
    simp only [orderedOutput,selected_apply, show (4:Fin 8).val < 5 by decide, not_true_eq_false, if_false]
  simpa only [h3,h4,inner_zero_left,add_zero] using hp

theorem ordered_orbit_pairing (f g : EnergyOutputSpace) :
    inner ℂ (growingActionLp ε a ha h 0 (orderedOutputLp f)) (orderedOutputLp g)=
      inner ℂ (orderedOutputLp f) (growingActionLp ε a ha h h (orderedOutputLp g)) := by
  have hp := orbit_pairing ε a ha h (orderedOutputLp f) (orderedOutputLp g)
  have h3 : coordinateLp 3 (orderedOutputLp f)=0 := by
    rw [coordinate_ordered,if_pos (by decide)]
  have h4 : coordinateLp 4 (orderedOutputLp f)=0 := by
    rw [coordinate_ordered,if_pos (by decide)]
  simpa only [h3,h4,inner_zero_left,add_zero] using hp

private theorem source_ordered (u : RV) :
    orderedOutputLp (PA u)=PA u :=
  lp_ordered_idem (RB u)

private theorem selected_potential_output (u : PV) :
    orderedOutputLp (PB u)=PB u :=
  congrFun ((KFCausalClockFloorPotentialHamiltonian.referenceLift_dense ε hε h hh hb m g k).equalizer
    (orderedOutputLp.continuous.comp (PB).continuous) (PB).continuous
    (funext (fun w => (congrArg orderedOutputLp
      (KFCausalClockFloorPotentialHamiltonian.referenceLift_output ε hε h hh hb m g k w)).trans
      ((source_ordered ε hε h hh hb m g k w).trans
        (KFCausalClockFloorPotentialHamiltonian.referenceLift_output ε hε h hh hb m g k w).symm)))) u

theorem form_pairing (u v : PV) :
    inner ℂ (PB (formAction ε hε a ha h hh hb 0 m g k u)) (PB v)=
      inner ℂ (PB u) (PB (formAction ε hε a ha h hh hb h m g k v)) := by
  have hu := selected_potential_output ε hε h hh hb m g k u
  have hv := selected_potential_output ε hε h hh hb m g k v
  have e0 : PB (formAction ε hε a ha h hh hb 0 m g k u)=
      growingActionLp ε a ha h 0 (orderedOutputLp (PB u)) :=
    (formAction_output ε hε a ha h hh hb 0 m g k u).trans
      (congrArg (growingActionLp ε a ha h 0) hu.symm)
  have eh : PB (formAction ε hε a ha h hh hb h m g k v)=
      growingActionLp ε a ha h h (orderedOutputLp (PB v)) :=
    (formAction_output ε hε a ha h hh hb h m g k v).trans
      (congrArg (growingActionLp ε a ha h h) hv.symm)
  exact (congrArg₂ (inner ℂ) e0 hv.symm).trans
    ((ordered_orbit_pairing ε a ha h (PB u) (PB v)).trans
      (congrArg₂ (inner ℂ) hu (eh.symm)))

#print axioms orderedOutput_growingAction
#print axioms orderedOutputLp_growingActionLp
#print axioms potential_graph_action
#print axioms formAction_embedding
#print axioms formAction_output
#print axioms ordered_output_pairing
#print axioms ordered_orbit_pairing
#print axioms form_pairing
end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianPotentialForm
