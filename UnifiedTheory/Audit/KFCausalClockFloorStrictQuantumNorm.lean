/- The physical clock-error norm itself strictly decreases at every real
time on every nonzero averaged energy-form state at positive vacuum coupling.
Its nonnegative limit is constructed but is not identified with zero. -/
import UnifiedTheory.Audit.KFCausalClockFloorSquaredEhrenfest
import UnifiedTheory.Audit.KFCausalClockFloorStrictQuantumLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorStrictQuantumNorm
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest (evolvingOutput)
open UnifiedTheory.Audit.KFCausalClockFloorSquaredEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorAveragedStrictRate (completed_square_rate_negative)
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

theorem squaredRate_negative (s t : ℝ) (w : V₀) (hw : J w ≠ 0) :
    squaredRate ε hε hbar hh hb mass2 quartic vacuum s t w < 0 := by
  have hn : embedding ε hε hbar hh hb mass2 quartic vacuum t
      (formTransfer ε hε hbar hh hb mass2 quartic vacuum 0 t
        (formFlow ε hε hbar hh hb mass2 quartic vacuum s t w)) ≠ 0 := by
    intro hz
    have hj := transfer_embedding ε hε hbar hh hb mass2 quartic vacuum 0 t
      (formFlow ε hε hbar hh hb mass2 quartic vacuum s t w)
    have he := formFlow_physical_norm ε hε hbar hh hb mass2 quartic vacuum s t w
    apply hw
    exact norm_eq_zero.mp (he.symm.trans ((congrArg norm (hj.symm.trans hz)).trans norm_zero))
  have hr := completed_square_rate_negative ε hε hbar hh hb mass2 quartic vacuum t hv _ hn
  rw [output_square_compLp] at hr
  exact hr

theorem norm_strictAnti (s : ℝ) (w : V₀) (hw : J w ≠ 0) :
    StrictAnti (fun t => ‖D (U s t (J w))‖) := by
  have hs : StrictAnti (fun t => ‖D (U s t (J w))‖^2) := by
    apply strictAnti_of_deriv_neg
    intro t
    rw [(norm_square_derivative ε hε hbar hh hb mass2 quartic vacuum s t w).deriv]
    exact squaredRate_negative ε hε hbar hh hb mass2 quartic vacuum hv s t w hw
  intro r t hrt
  have h := hs hrt
  nlinarith [norm_nonneg (D (U s t (J w))),norm_nonneg (D (U s r (J w)))]

theorem energy_domain_norm_strictAnti (s : ℝ) (f : Hilbert) (hf : f ∈ (EnergyOperator s).domain) (hn : f ≠ 0) :
    StrictAnti (fun t => ‖D (U s t f)‖) := by
  let data := KFCausalClockFloorAveragedHamiltonian.formData ε hε hbar hh hb mass2 quartic vacuum s
  let g := KFCausalClosedGraphForm.graphVector data ⟨f,hf⟩
  let w := formTransfer ε hε hbar hh hb mass2 quartic vacuum s 0 g
  have hj : J w = f := transfer_embedding ε hε hbar hh hb mass2 quartic vacuum s 0 g
  have hn' : J w ≠ 0 := fun hz => hn (hj.symm.trans hz)
  have hs := norm_strictAnti ε hε hbar hh hb mass2 quartic vacuum hv s w hn'
  exact (congrArg (fun z : Hilbert => StrictAnti (fun t => ‖D (U s t z)‖)) hj) ▸ hs

theorem exists_unit_zero_strict_norm (s δ : ℝ) (hδ : 0 < δ) :
    ∃ f : Hilbert, ‖f‖ = 1 ∧ (f,0) ∈ (standingCharge hbar hh).graph ∧
      f ∈ (EnergyOperator s).domain ∧ StrictAnti (fun t => ‖D (U s t f)‖) ∧
      ∀ t, s ≤ t → ‖D (U s t f)‖ < δ := by
  obtain ⟨f,hn,_,he,hq,hd⟩ := KFCausalClockFloorSmallDefectStates.exists_unit_zero_energy_small_defect
    ε hε hbar hh hb mass2 quartic vacuum s δ hδ
  have hf : f ≠ 0 := by
    intro hz
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  exact ⟨f,hn,hq,he,energy_domain_norm_strictAnti ε hε hbar hh hb mass2 quartic vacuum hv s f he hf,
    KFCausalClockFloorDefectMonotonicity.evolution_small_defect ε hε hbar hh hb mass2 quartic vacuum s δ f hd⟩

theorem norm_limit (s : ℝ) (w : V₀) (hw : J w ≠ 0) :
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧ (∀ t, ℓ < ‖D (U s t (J w))‖) ∧
      Tendsto (fun t => ‖D (U s t (J w))‖) atTop (𝓝 ℓ) := by
  let F : ℝ → ℝ := fun t => ‖D (U s t (J w))‖
  have hs : StrictAnti F := norm_strictAnti ε hε hbar hh hb mass2 quartic vacuum hv s w hw
  have h0 (t : ℝ) : 0 ≤ F t := norm_nonneg _
  have hbd : BddBelow (Set.range F) := ⟨0,by rintro _ ⟨t,rfl⟩; exact h0 t⟩
  refine ⟨⨅ t, F t,le_ciInf h0,?_,tendsto_atTop_ciInf hs.antitone hbd⟩
  intro t
  exact (ciInf_le hbd (t+1)).trans_lt (hs (by linarith : t < t+1))

#print axioms squaredRate_negative
#print axioms norm_strictAnti
#print axioms energy_domain_norm_strictAnti
#print axioms exists_unit_zero_strict_norm
#print axioms norm_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorStrictQuantumNorm
