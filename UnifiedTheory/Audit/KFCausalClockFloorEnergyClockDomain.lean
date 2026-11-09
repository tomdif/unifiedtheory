/- The actual closed joint form retains the positive half-clock factor.
In particular every zero-charge averaged-energy state has finite clock
energy, so the defect/clock-energy tradeoff applies to the constructed
small-defect states. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
import UnifiedTheory.Audit.KFCausalClockFloorDefectEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorEnergyClockDomain
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClosedGraphForm (FormSpace embedding energyOutput)
open UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian (formData)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroSector)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hb : |hbar| ≤ Real.pi*ε)
  (mass2 quartic vacuum t : ℝ)

local notation "D" => formData ε hε hbar hb mass2 quartic vacuum t

theorem form_clock_bound (u : FormSpace D) :
    ∃ g : Hilbert, (embedding D u,g) ∈ (clockHalf ε).graph ∧
      ‖g‖^2 ≤ 2 * ‖energyOutput D u‖^2 := by
  let f : Hilbert := embedding D u
  let y := energyOutput D u
  let c : ℂ := (Real.sqrt (1/2 : ℝ) : ℂ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hfg : (f,y) ∈ (closedEnergy ε hε hbar modelDirections pointField mass2 quartic vacuum t).graph :=
    u.property
  have hcomp := closedEnergy_component_graph ε hε hbar modelDirections pointField mass2 quartic vacuum t
    hb f y hfg 0
  change (c • f,y 0) ∈ (clockHalf ε).closure.graph at hcomp
  have hclosed := (clockHalf_selfAdjoint ε).isClosed
  have he : (clockHalf ε).closure.graph = (clockHalf ε).graph :=
    hclosed.isClosable.graph_closure_eq_closure_graph.symm.trans
      hclosed.submodule_topologicalClosure_eq
  rw [he] at hcomp
  have hinv := (clockHalf ε).graph.smul_mem c⁻¹ hcomp
  change (c⁻¹ • (c • f),c⁻¹ • y 0) ∈ (clockHalf ε).graph at hinv
  rw [smul_smul,inv_mul_cancel₀ hc,one_smul] at hinv
  let g : Hilbert := c⁻¹ • y 0
  have hcg : c • g = y 0 := by simp only [g,smul_smul,mul_inv_cancel₀ hc,one_smul]
  have hn : ‖c‖^2 = (1/2 : ℝ) := by
    simp only [c,Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]
  have hy := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le y 0) 2
  rw [← hcg,norm_smul,mul_pow,hn] at hy
  exact ⟨g,hinv,by linarith⟩

theorem zero_averaged_energy_clock_domain (hh : hbar ≠ 0) (f : Hilbert)
    (hz : f ∈ zeroSector hbar hh)
    (hf : f ∈ (KFCausalClockFloorAveragedEnergy.energyOperator ε hε hbar hb hh mass2 quartic vacuum t).domain) :
    f ∈ (clockHalf ε).domain := by
  have hr := (KFCausalClockFloorAveragedEnergy.zero_sector_energy_domain
    ε hε hbar hb hh mass2 quartic vacuum t f hz).mp hf
  obtain ⟨u,hu⟩ := hr
  change embedding D u = f at hu
  obtain ⟨g,hg,_⟩ := form_clock_bound ε hε hbar hb mass2 quartic vacuum t u
  rw [hu] at hg
  exact LinearPMap.mem_domain_of_mem_graph hg

#print axioms form_clock_bound
#print axioms zero_averaged_energy_clock_domain

end
end UnifiedTheory.Audit.KFCausalClockFloorEnergyClockDomain
