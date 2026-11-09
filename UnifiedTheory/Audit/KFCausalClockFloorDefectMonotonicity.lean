/- The physical clock-defect norm cannot increase at any forward time
under the actual charge-averaged evolution. The full Hamiltonian form
sign passes through bounded Yosida dynamics and the proved all-L2
strong limit. This is fixed-floor defect control, not a canonical
quantum commutator or a quantum-to-classical limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianDefect
import UnifiedTheory.Audit.KFCausalYosidaSignedPairing
import UnifiedTheory.Audit.KFCausalBoundedDefectMonotonicity
import UnifiedTheory.Audit.KFCausalClockFloorAveragedSequenceConvergence
import UnifiedTheory.Audit.KFCausalClockFloorSmallDefectStates
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectMonotonicity
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectForm
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianDefect
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSequenceConvergence
open UnifiedTheory.Audit.KFCausalClockFloorAveragedCountableLimit (cutoff cutoff_pos)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hne : hbar ≠ 0)
  (hh : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "D" => defectOperator ε hε
local notation "U" => evolution ε hε hbar hne hh mass2 quartic vacuum
local notation "V" => dynamics ε hε hbar hne hh mass2 quartic vacuum

theorem yosida_square_sign (a t : ℝ) (ha : 0 < a) (f : Hilbert) :
    0 ≤ hbar*(inner ℂ (averagedYosida ε hε hbar hne hh mass2 quartic vacuum a t f) (D (D f))).im :=
  KFCausalYosidaSignedPairing.signed_pairing
    (hamiltonian ε hε hbar hne hh mass2 quartic vacuum t) _ ((D).comp D) a hbar
    (averaged_resolves ε hε hbar hne hh mass2 quartic vacuum a t ha)
    (defect_square_inner_im_zero ε hε)
    (hamiltonian_square_sign ε hε hbar hne hh mass2 quartic vacuum t) f

theorem yosida_defect_antitone (a : ℝ) (ha : 0 < a) (s : ℝ) (f : Hilbert) :
    Antitone (fun t => ‖D (V a ha s t f)‖) := by
  apply KFCausalBoundedDefectMonotonicity.norm_antitone D (defect_inner ε hε) hbar hne
    (fun t => V a ha s t f) (averagedYosida ε hε hbar hne hh mass2 quartic vacuum a)
  · intro t
    exact dynamics_state_derivative ε hε hbar hne hh mass2 quartic vacuum a ha s t f
  · intro t
    exact yosida_square_sign ε hε hbar hne hh mass2 quartic vacuum a t ha _

theorem yosida_defect_le_initial (a : ℝ) (ha : 0 < a) (s t : ℝ) (hst : s ≤ t) (f : Hilbert) :
    ‖D (V a ha s t f)‖ ≤ ‖D f‖ := by
  have h := yosida_defect_antitone ε hε hbar hne hh mass2 quartic vacuum a ha s f hst
  simpa only [dynamics_initial,ContinuousLinearMap.id_apply] using h

theorem evolution_defect_antitone (s : ℝ) (f : Hilbert) :
    Antitone (fun t => ‖D (U s t f)‖) := by
  intro r t hrt
  have ht := ((D).continuous.tendsto _).comp
    (cutoff_dynamics_strong_limit ε hε hbar hne hh mass2 quartic vacuum s t f)
  have hr := ((D).continuous.tendsto _).comp
    (cutoff_dynamics_strong_limit ε hε hbar hne hh mass2 quartic vacuum s r f)
  exact le_of_tendsto_of_tendsto ht.norm hr.norm (Filter.Eventually.of_forall fun n =>
    yosida_defect_antitone ε hε hbar hne hh mass2 quartic vacuum (cutoff n) (cutoff_pos n) s f hrt)

theorem evolution_defect_le_initial (s t : ℝ) (hst : s ≤ t) (f : Hilbert) :
    ‖D (U s t f)‖ ≤ ‖D f‖ := by
  have h := evolution_defect_antitone ε hε hbar hne hh mass2 quartic vacuum s f hst
  have hi : U s s f = f := congrArg (fun P : Hilbert →L[ℂ] Hilbert => P f)
    (evolution_initial ε hε hbar hne hh mass2 quartic vacuum s)
  simpa only [hi] using h

theorem evolution_small_defect (s : ℝ) (δ : ℝ) (f : Hilbert) (hf : ‖D f‖ < δ) :
    ∀ t, s ≤ t → ‖D (U s t f)‖ < δ := by
  intro t hst
  exact (evolution_defect_le_initial ε hε hbar hne hh mass2 quartic vacuum s t hst f).trans_lt hf

theorem exists_unit_zero_all_future_small_defect (s δ : ℝ) (hδ : 0 < δ) :
    ∃ f : Hilbert, ‖f‖ = 1 ∧
      f ∈ (KFCausalClockFloorAveragedEnergy.energyOperator ε hε hbar
        (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε hbar hh)
        hne mass2 quartic vacuum s).domain ∧
      ∀ t, s ≤ t → ‖U s t f‖ = 1 ∧
        (U s t f,0) ∈ (KFCausalStandingChargeOperator.standingCharge hbar hne).graph ∧
        ‖D (U s t f)‖ < δ := by
  obtain ⟨f,hn,hz,he,_,hd⟩ := KFCausalClockFloorSmallDefectStates.exists_unit_zero_energy_small_defect
    ε hε hbar hne hh mass2 quartic vacuum s δ hδ
  refine ⟨f,hn,he,?_⟩
  intro t hst
  exact ⟨(evolution_norm ε hε hbar hne hh mass2 quartic vacuum s t f).trans hn,
    KFCausalClockFloorAveragedEvolutionProjection.evolution_charge_zero
      ε hε hbar hne hh mass2 quartic vacuum s t f hz,
    evolution_small_defect ε hε hbar hne hh mass2 quartic vacuum s δ f hd t hst⟩

#print axioms yosida_square_sign
#print axioms yosida_defect_antitone
#print axioms yosida_defect_le_initial
#print axioms evolution_defect_antitone
#print axioms evolution_defect_le_initial
#print axioms evolution_small_defect
#print axioms exists_unit_zero_all_future_small_defect

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectMonotonicity
