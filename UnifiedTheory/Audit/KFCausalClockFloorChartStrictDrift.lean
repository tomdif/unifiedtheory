/- Positive vacuum coupling makes the derived chart drift strictly
positive for every nonzero state, in every charge sector. This gives
strict mean growth, without a uniform rate or an escape conclusion. -/
import UnifiedTheory.Audit.KFCausalClockFloorChartEhrenfest
import UnifiedTheory.Audit.KFCausalClockFloorVacuumObservation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorChartStrictDrift
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorChartPhasePairing (orderedOutput orderedOutputLp)
open UnifiedTheory.Audit.KFCausalClockFloorChartTransportLimit (drift output drift_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorChartEhrenfest (chartMoment chart_integral_balance)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution evolution_norm evolution_embedding)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (graphFormVector_surjective)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k
local notation "J" => embedding ε hε h hne hh m g k
local notation "A" => energyOutput ε hε h hne hh m g k

theorem ordered_output_ne_zero (hk : 0 < k) (t : ℝ) (u : V t) (hu : J t u ≠ 0) :
    orderedOutputLp (A t u) ≠ 0 := by
  intro hz
  obtain ⟨v,hv⟩ := graphFormVector_surjective ε hε h hne hh m g k t u
  let D := KFCausalClockFloorFormHamiltonian.formData ε hε h (hamiltonian_bound ε h hh) m g k t
  let j := KFCausalClosedGraphForm.embedding D
  let a := KFCausalClosedGraphForm.energyOutput D
  let sec := KFCausalClockFloorAveragedEnergy.sectionMap ε hε h (hamiltonian_bound ε h hh) hne m g k t v
  let jv := KFCausalClockFloorAveragedEnergy.embedding ε hε h (hamiltonian_bound ε h hh) hne m g k t
  have hjv : jv v = J t u := congrArg (J t) hv
  have hav : a.compLp sec = A t u := congrArg (A t) hv
  have hout : ∀ᵐ θ ∂angleMeasure, orderedOutput (a (sec θ)) = 0 := by
    filter_upwards [a.coeFn_compLp sec,orderedOutput.coeFn_compLp (A t u),
      (Lp.coeFn_zero (E := KFCausalFiniteJointGraph.Output (Fin 8) Hilbert) (p := 2) (μ := angleMeasure))]
      with θ h1 h2 h0
    have h3 : A t u θ = a (sec θ) :=
      (congrArg (fun z : KFCausalAveragedOutputRescaling.EnergyOutputSpace => z θ) hav).symm.trans h1
    have h4 : orderedOutput.compLp (A t u) θ = 0 :=
      (congrArg (fun z : KFCausalAveragedOutputRescaling.EnergyOutputSpace => z θ) hz).trans h0
    exact (congrArg orderedOutput h3).symm.trans (h2.symm.trans h4)
  have horbit := KFCausalClockFloorAveragedEnergy.orbit_lift_ae ε hε h (hamiltonian_bound ε h hh) hne m g k t v
  obtain ⟨θ,hθ,houtθ⟩ := (horbit.and hout).exists
  have h7 : a (sec θ) 7 = 0 := by
    have he := congrArg (fun z : KFCausalFiniteJointGraph.Output (Fin 8) Hilbert => z 7) houtθ
    simpa only [orderedOutput,KFCausalFiniteOutputRescaling.selected_apply,
      show ¬ (7:Fin 8).val < 5 by decide,not_false_eq_true,if_true,PiLp.zero_apply] using he
  have hjne : j (sec θ) ≠ 0 := by
    intro he
    have hn : ‖j (sec θ)‖ = ‖J t u‖ :=
      (congrArg norm hθ).trans
        (((KFCausalPhysicalCircleAction.action h hne (2*Real.pi*θ)).norm_map (jv v)).trans (congrArg norm hjv))
    rw [he,norm_zero] at hn
    exact hu (norm_eq_zero.mp hn.symm)
  exact KFCausalClockFloorVacuumOutputFaithful.form_vacuum_ne_zero ε hε h
    (hamiltonian_bound ε h hh) m g k t hk (sec θ) hjne h7

theorem drift_positive (hk : 0 < k) (s t : ℝ) (w : V 0) (hw : J 0 w ≠ 0) :
    0 < drift ε hε h hne hh m g k s t w := by
  have hu : J t (formTransfer ε hε h hne hh m g k 0 t
      (formFlow ε hε h hne hh m g k s t w)) ≠ 0 := by
    intro hz
    have hn : ‖evolution ε hε h hne hh m g k s t (J 0 w)‖ = 0 := by
      rw [evolution_embedding,← transfer_embedding ε hε h hne hh m g k 0 t,hz,norm_zero]
    rw [evolution_norm] at hn
    exact hw (norm_eq_zero.mp hn)
  exact sq_pos_of_pos (norm_pos_iff.mpr (ordered_output_ne_zero ε hε h hne hh m g k hk t _ hu))

theorem chart_strictMono (hk : 0 < k) (s : ℝ) (w : V 0) (hw : J 0 w ≠ 0)
    (hleft : Integrable (KFCausalClockFloorInverseGapMoment.density ε (J 0 w))) :
    StrictMonoOn (fun t => chartMoment ε hε h hne hh m g k s t w) (Set.Ici s) := by
  intro a ha b hb hab
  have hi := intervalIntegral.intervalIntegral_pos_of_pos
    ((drift_continuous ε hε h hne hh m g k s w).intervalIntegrable a b)
    (fun t => drift_positive ε hε h hne hh m g k hk s t w hw) hab
  rw [chart_integral_balance ε hε h hne hh m g k s a b ha hb w hleft] at hi
  exact sub_pos.mp hi

#print axioms ordered_output_ne_zero
#print axioms drift_positive
#print axioms chart_strictMono
end
end UnifiedTheory.Audit.KFCausalClockFloorChartStrictDrift
