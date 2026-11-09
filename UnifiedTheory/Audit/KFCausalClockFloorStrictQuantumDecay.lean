/- Strict quantum clock-defect decrease at every real time for every
nonzero state in the actual averaged energy form at positive vacuum coupling.
No small-hbar limit, force convergence, or derivative sign is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedStrictRate
import UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest
import UnifiedTheory.Audit.KFCausalClockFloorDefectMonotonicity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorStrictQuantumDecay
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorAveragedStrictRate (completed_rate_negative)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (standingCharge)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
  (mass2 quartic vacuum : ℝ) (hv : 0 < vacuum)
local notation "V₀" => FormSpace ε hε hbar hh hb mass2 quartic vacuum 0
local notation "J" => embedding ε hε hbar hh hb mass2 quartic vacuum 0
local notation "U" => evolution ε hε hbar hh hb mass2 quartic vacuum
local notation "D" => defectOperator ε hε
local notation "EnergyOperator" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε hbar
  (hamiltonian_bound ε hbar hb) hh mass2 quartic vacuum

include hv

theorem exactRate_negative (s t : ℝ) (w : V₀) (hw : J w ≠ 0) :
    exactRate ε hε hbar hh hb mass2 quartic vacuum s t w < 0 := by
  apply completed_rate_negative ε hε hbar hh hb mass2 quartic vacuum t hv
    (formTransfer ε hε hbar hh hb mass2 quartic vacuum 0 t
      (formFlow ε hε hbar hh hb mass2 quartic vacuum s t w))
  intro hz
  have hj := transfer_embedding ε hε hbar hh hb mass2 quartic vacuum 0 t
    (formFlow ε hε hbar hh hb mass2 quartic vacuum s t w)
  have hn := formFlow_physical_norm ε hε hbar hh hb mass2 quartic vacuum s t w
  have hzero := hj.symm.trans hz
  apply hw
  apply norm_eq_zero.mp
  exact hn.symm.trans (congrArg norm hzero |>.trans norm_zero)

theorem expectation_strictAnti (s : ℝ) (w : V₀) (hw : J w ≠ 0) :
    StrictAnti (fun t => (inner ℂ (U s t (J w)) (D (U s t (J w)))).re) := by
  apply strictAnti_of_deriv_neg
  intro t
  rw [(expectation_derivative ε hε hbar hh hb mass2 quartic vacuum s t w).deriv]
  exact exactRate_negative ε hε hbar hh hb mass2 quartic vacuum hv s t w hw

theorem energy_domain_strictAnti (s : ℝ) (f : Hilbert) (hf : f ∈ (EnergyOperator s).domain) (hn : f ≠ 0) :
    StrictAnti (fun t => (inner ℂ (U s t f) (D (U s t f))).re) := by
  let data := KFCausalClockFloorAveragedHamiltonian.formData ε hε hbar hh hb mass2 quartic vacuum s
  let g := KFCausalClosedGraphForm.graphVector data ⟨f,hf⟩
  let w := formTransfer ε hε hbar hh hb mass2 quartic vacuum s 0 g
  have hj : J w = f := transfer_embedding ε hε hbar hh hb mass2 quartic vacuum s 0 g
  have hn' : J w ≠ 0 := fun hz => hn (hj.symm.trans hz)
  have hs := expectation_strictAnti ε hε hbar hh hb mass2 quartic vacuum hv s w hn'
  exact (congrArg (fun z : Hilbert => StrictAnti (fun t => (inner ℂ (U s t z) (D (U s t z))).re)) hj) ▸ hs

theorem exists_unit_zero_strict_small_defect (s δ : ℝ) (hδ : 0 < δ) :
    ∃ f : Hilbert, ‖f‖ = 1 ∧ (f,0) ∈ (standingCharge hbar hh).graph ∧
      f ∈ (EnergyOperator s).domain ∧
      StrictAnti (fun t => (inner ℂ (U s t f) (D (U s t f))).re) ∧
      ∀ t, s ≤ t → ‖D (U s t f)‖ < δ := by
  obtain ⟨f,hn,_,he,hq,hd⟩ := KFCausalClockFloorSmallDefectStates.exists_unit_zero_energy_small_defect
    ε hε hbar hh hb mass2 quartic vacuum s δ hδ
  have hf : f ≠ 0 := by
    intro hz
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  exact ⟨f,hn,hq,he,energy_domain_strictAnti ε hε hbar hh hb mass2 quartic vacuum hv s f he hf,
    KFCausalClockFloorDefectMonotonicity.evolution_small_defect ε hε hbar hh hb mass2 quartic vacuum s δ f hd⟩

#print axioms exactRate_negative
#print axioms expectation_strictAnti
#print axioms energy_domain_strictAnti
#print axioms exists_unit_zero_strict_small_defect

end
end UnifiedTheory.Audit.KFCausalClockFloorStrictQuantumDecay
