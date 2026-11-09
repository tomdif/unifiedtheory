/- The actual averaged energy domain contains normalized zero-charge
states with arbitrarily small clock-defect norm at every fixed positive
floor. The proof uses the proved domain density and localized physical
targets, not an assumed family of admissible states. It gives no uniform
energy bound or common evolution-time interval for this family. -/
import UnifiedTheory.Audit.KFCausalClockLocalizedZeroState
import UnifiedTheory.Audit.KFCausalDenseUnitSmallImage
import UnifiedTheory.Audit.KFCausalClockFloorAveragedDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSmallDefectStates
noncomputable section
open Filter MeasureTheory
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockLocalizedZeroState
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy (energyOperator)

theorem exists_unit_zero_small_defect (ε hbar : ℝ) (hε : 0 < ε) (hh : hbar ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : Hilbert, ‖f‖ = 1 ∧ f ∈ zeroSector hbar hh ∧ ‖defectOperator ε hε f‖ < δ := by
  have hl : Tendsto (fun S : ℝ => ε * Real.exp (-S)) atTop (𝓝 0) := by
    simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul ε
  obtain ⟨S,hS⟩ := (hl.eventually (gt_mem_nhds hδ)).exists
  obtain ⟨f,hf,hz,hs⟩ := exists_unit_localized_zero hbar hh S
  refine ⟨f,hf,hz,?_⟩
  have hb := defectOperator_on_supported_state ε hε S f hs
  rw [hf,mul_one] at hb
  exact hb.trans_lt hS

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)

local notation "E" => LinearPMap.domain (energyOperator ε hε hbar (hamiltonian_bound ε hbar hbound)
  hh mass2 quartic vacuum t)

theorem exists_unit_zero_energy_small_defect (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : Hilbert, ‖f‖ = 1 ∧ f ∈ zeroSector hbar hh ∧ f ∈ E ∧
      (f,0) ∈ (standingCharge hbar hh).graph ∧ ‖defectOperator ε hε f‖ < δ := by
  obtain ⟨g,hg,hz,hd⟩ := exists_unit_zero_small_defect ε hbar hε hh δ hδ
  have hc := KFCausalClockFloorAveragedDensity.zero_energy_domain_closure
    ε hbar hε hh hbound mass2 quartic vacuum t
  have hgcl : g ∈ (zeroSector hbar hh ⊓ E).topologicalClosure := by
    rw [hc]
    exact hz
  obtain ⟨f,hf,hn,he⟩ := KFCausalDenseUnitSmallImage.exists_unit_small_image
    (zeroSector hbar hh ⊓ E) (defectOperator ε hε) g hg hgcl δ hd
  exact ⟨f,hn,hf.1,hf.2,(standingCharge_zero_iff hbar hh f).mpr hf.1,he⟩

theorem exists_unit_zero_energy_defect_sequence :
    ∃ f : ℕ → Hilbert,
      (∀ n, ‖f n‖ = 1 ∧ f n ∈ zeroSector hbar hh ∧ f n ∈ E ∧
        (f n,0) ∈ (standingCharge hbar hh).graph) ∧
      Tendsto (fun n => ‖defectOperator ε hε (f n)‖) atTop (𝓝 0) := by
  have hex (n : ℕ) := exists_unit_zero_energy_small_defect ε hε hbar hh hbound mass2 quartic vacuum t
    (1/((n:ℝ)+1)) (by positivity)
  choose f hf hz he hQ hd using hex
  refine ⟨f,fun n => ⟨hf n,hz n,he n,hQ n⟩,?_⟩
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hd n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

#print axioms exists_unit_zero_small_defect
#print axioms exists_unit_zero_energy_small_defect
#print axioms exists_unit_zero_energy_defect_sequence

end
end UnifiedTheory.Audit.KFCausalClockFloorSmallDefectStates
