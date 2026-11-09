/- Chart modulation commutes with charge, clock and transverse kinetic
factors, and scales the two ordered matter factors exactly. -/
import UnifiedTheory.Audit.KFCausalClockFloorExponentialModulation
import UnifiedTheory.Audit.KFCausalBoundedClockFactorGraphs
import UnifiedTheory.Audit.KFCausalClockFloorCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorFactorChartModulation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorChartModulation
open UnifiedTheory.Audit.KFCausalClockFloorExponentialModulation
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf clockHalf_graph)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalPhysicalField (physicalField physicalField_graph)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare fieldSquare_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)

def profile (ε r s : ℝ) : ℂ := phase ε r (s,0)

theorem profile_measurable (ε r : ℝ) : Measurable (profile ε r) :=
  (phase_measurable ε r).comp (measurable_id.prodMk measurable_const)

theorem profile_bound (ε r s : ℝ) : ‖profile ε r s‖ ≤ 1 := (phase_norm ε r (s,0)).le

theorem modulation_eq_multiplier (ε r : ℝ) (f : Hilbert) :
    modulation ε r f = KFCausalBoundedClockCharge.multiplier
      (profile ε r) (profile_measurable ε r) 1 zero_le_one (profile_bound ε r) f := by
  apply Lp.ext
  filter_upwards [modulation_coe ε r f,KFCausalBoundedClockCharge.multiplier_coe
    (profile ε r) (profile_measurable ε r) 1 zero_le_one (profile_bound ε r) f] with x hx hy
  exact hx.trans hy.symm

theorem modulation_charge (ε r h : ℝ) (hne : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    modulation ε r (KFCausalPhysicalCircleAction.action h hne θ f) =
      KFCausalPhysicalCircleAction.action h hne θ (modulation ε r f) := by
  simp only [modulation_eq_multiplier]
  exact KFCausalBoundedClockCharge.multiplier_charge _ _ _ _ _ h hne θ f

theorem half_graph (ε r : ℝ) (f g : Hilbert) (hfg : (f,g) ∈ (clockHalf ε).graph) :
    (modulation ε r f,modulation ε r g) ∈ (clockHalf ε).graph := by
  simp only [modulation_eq_multiplier]
  exact KFCausalBoundedClockFactorGraphs.half_graph _ _ _ _ _ ε f g hfg

theorem kinetic_graph (ε h r : ℝ) (hne : h ≠ 0) (v : Transverse)
    (f g : Hilbert) (hfg : (f,g) ∈ (clockMomentum ε h v).graph) :
    (modulation ε r f,modulation ε r g) ∈ (clockMomentum ε h v).graph := by
  simp only [modulation_eq_multiplier]
  exact KFCausalBoundedClockFactorGraphs.kinetic_graph _ _ _ _ _ ε h hne v f g hfg

theorem field_graph (ε r : ℝ) (l : Transverse →L[ℝ] ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (physicalField l).graph) :
    (modulation ε r f,modulation ε r g) ∈ (physicalField l).graph := by
  apply (physicalField_graph l _ _).mpr
  filter_upwards [modulation_coe ε r f,modulation_coe ε r g,
    (physicalField_graph l f g).mp hfg] with x hf hg he
  rw [hg,hf,he]
  ring

theorem square_graph (ε r : ℝ) (l : Transverse →L[ℝ] ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (fieldSquare l).graph) :
    (modulation ε r f,modulation ε r g) ∈ (fieldSquare l).graph := by
  apply (fieldSquare_graph l _ _).mpr
  filter_upwards [modulation_coe ε r f,modulation_coe ε r g,
    (fieldSquare_graph l f g).mp hfg] with x hf hg he
  rw [hg,hf,he]
  ring

variable (ε : ℝ) (hε : 0 < ε) (h r : ℝ)

theorem matter_graph (M : Hilbert →ₗ.[ℂ] Hilbert)
    (hM : ∀ f g, (f,g) ∈ M.graph → (modulation ε r f,modulation ε r g) ∈ M.graph)
    (f g : Hilbert) (hfg : (f,g) ∈ (matterFactor ε hε h M).graph) :
    (modulation ε r f,(Real.exp (Real.pi*h*r):ℂ) • modulation ε r g) ∈
      (matterFactor ε hε h M).graph := by
  obtain ⟨u,hu,hg⟩ := (composition_graph _ _ f g).mp hfg
  exact (composition_graph _ _ _ _).mpr ⟨_,ordered_graph_modulation ε hε h r f u hu,
    M.graph.smul_mem (Real.exp (Real.pi*h*r):ℂ) (hM u g hg)⟩

def factorScale (i : Fin 8) : ℂ := if i.val < 5 then 1 else (Real.exp (Real.pi*h*r):ℂ)

theorem factor_graph (hne : h ≠ 0) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (i : Fin 8) (f g : Hilbert) (hfg : (f,g) ∈ (energyFactor ε hε h v l i).graph) :
    (modulation ε r f,factorScale h r i • modulation ε r g) ∈
      (energyFactor ε hε h v l i).graph := by
  fin_cases i
  · simpa only [factorScale,show (0:ℕ)<5 by decide,if_true,one_smul] using half_graph ε r f g hfg
  · simpa only [factorScale,show (1:ℕ)<5 by decide,if_true,one_smul] using kinetic_graph ε h r hne (v 0) f g hfg
  · simpa only [factorScale,show (2:ℕ)<5 by decide,if_true,one_smul] using kinetic_graph ε h r hne (v 1) f g hfg
  · simpa only [factorScale,show (3:ℕ)<5 by decide,if_true,one_smul] using kinetic_graph ε h r hne (v 2) f g hfg
  · simpa only [factorScale,show (4:ℕ)<5 by decide,if_true,one_smul] using kinetic_graph ε h r hne (v 3) f g hfg
  · exact matter_graph ε hε h r _ (field_graph ε r l) f g hfg
  · exact matter_graph ε hε h r _ (square_graph ε r l) f g hfg
  · exact ordered_graph_modulation ε hε h r f g hfg

theorem common_domain_modulation (hne : h ≠ 0) (v : Fin 4 → Transverse)
    (l : Transverse →L[ℝ] ℝ) (f : Hilbert) :
    modulation ε r f ∈ commonEnergyDomain ε hε h v l ↔ f ∈ commonEnergyDomain ε hε h v l := by
  have forward (q : ℝ) (x : Hilbert) (hx : x ∈ commonEnergyDomain ε hε h v l) :
      modulation ε q x ∈ commonEnergyDomain ε hε h v l := by
    apply (commonEnergyDomain_iff ε hε h v l _).mpr
    intro i
    exact LinearPMap.mem_domain_of_mem_graph (factor_graph ε hε h q hne v l i x _
      ((energyFactor ε hε h v l i).mem_graph ⟨x,(commonEnergyDomain_iff ε hε h v l x).mp hx i⟩))
  constructor
  · intro hf
    simpa only [modulation_inverse] using forward (-r) _ hf
  · exact forward r f

#print axioms profile_measurable
#print axioms profile_bound
#print axioms modulation_eq_multiplier
#print axioms modulation_charge
#print axioms half_graph
#print axioms kinetic_graph
#print axioms field_graph
#print axioms square_graph
#print axioms matter_graph
#print axioms factor_graph
#print axioms common_domain_modulation
end
end UnifiedTheory.Audit.KFCausalClockFloorFactorChartModulation
