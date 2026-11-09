/- The exact chart-phase action passes through simultaneous graph closure
for all eight energy factors, including zero energy coefficients. -/
import UnifiedTheory.Audit.KFCausalClockFloorFactorChartModulation
import UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
import UnifiedTheory.Audit.KFCausalFiniteOutputRescaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorClosedChartModulation
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalClockFloorChartModulation
open UnifiedTheory.Audit.KFCausalClockFloorFactorChartModulation
open UnifiedTheory.Audit.KFCausalFiniteOutputRescaling (selected selected_apply)

def outputAction (ε h r : ℝ) : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert where
  toFun g := WithLp.toLp 2 (fun i => factorScale h r i • modulation ε r (g i))
  map_add' f g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.add_apply,map_add,smul_add]
  map_smul' c g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.smul_apply,map_smul,RingHom.id_apply]
    exact smul_comm _ _ _
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => ((modulation ε r).continuous.comp
      (PiLp.continuous_apply 2 _ i)).const_smul (factorScale h r i)))

theorem outputAction_apply (ε h r : ℝ) (g : Output (Fin 8) Hilbert) (i : Fin 8) :
    outputAction ε h r g i = factorScale h r i • modulation ε r (g i) := rfl

theorem outputAction_norm_square (ε h r : ℝ) (g : Output (Fin 8) Hilbert) :
    ‖outputAction ε h r g‖^2 = ‖selected (fun i : Fin 8 => i.val < 5) g‖^2+
      Real.exp (2*Real.pi*h*r)*‖selected (fun i : Fin 8 => ¬ i.val < 5) g‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < 5
  · simp only [outputAction_apply,factorScale,hi,if_true,one_smul,LinearIsometryEquiv.norm_map,
      selected_apply,not_true_eq_false,if_false,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,add_zero]
  · simp only [outputAction_apply,factorScale,hi,if_false,norm_smul,LinearIsometryEquiv.norm_map,
      selected_apply,not_false_eq_true,if_true,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow,← Real.exp_nat_mul]
    congr 2
    ring

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (r : ℝ)
  (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)

include hne

theorem joint_graph (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ jointGraph (energyFactor ε hε h v l) c) :
    (modulation ε r f,outputAction ε h r g) ∈ jointGraph (energyFactor ε hε h v l) c := by
  intro i
  have he := factor_graph ε hε h r hne v l i (c i • f) (g i) (hfg i)
  simpa only [map_smul,outputAction_apply] using he

theorem closed_joint_graph (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (jointGraph (energyFactor ε hε h v l) c).topologicalClosure) :
    (modulation ε r f,outputAction ε h r g) ∈
      (jointGraph (energyFactor ε hε h v l) c).topologicalClosure := by
  let K := jointGraph (energyFactor ε hε h v l) c
  let P := (modulation ε r : Hilbert →L[ℂ] Hilbert).prodMap (outputAction ε h r)
  have hK : K ≤ K.topologicalClosure.comap P.toLinearMap := by
    rintro ⟨x,y⟩ hxy
    exact K.le_topologicalClosure (joint_graph ε hε h hne r v l c x y hxy)
  exact K.topologicalClosure_minimal hK (K.isClosed_topologicalClosure.preimage P.continuous) hfg

theorem closed_energy_graph (hb : |h| ≤ Real.pi*ε) (m q k t : ℝ)
    (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε h v l m q k t).graph) :
    (modulation ε r f,outputAction ε h r g) ∈ (closedEnergy ε hε h v l m q k t).graph := by
  rw [closedEnergy_graph ε hε h v l m q k t hb] at hfg ⊢
  exact closed_joint_graph ε hε h hne r v l _ f g hfg

theorem closed_energy_domain (hb : |h| ≤ Real.pi*ε) (m q k t : ℝ) (f : Hilbert) :
    modulation ε r f ∈ (closedEnergy ε hε h v l m q k t).domain ↔
      f ∈ (closedEnergy ε hε h v l m q k t).domain := by
  constructor
  · intro hf
    have hg := closed_energy_graph ε hε h hne (-r) v l hb m q k t _ _
      ((closedEnergy ε hε h v l m q k t).mem_graph ⟨_,hf⟩)
    rw [modulation_inverse] at hg
    exact LinearPMap.mem_domain_of_mem_graph hg
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph (closed_energy_graph ε hε h hne r v l hb m q k t f _
      ((closedEnergy ε hε h v l m q k t).mem_graph ⟨f,hf⟩))

#print axioms outputAction_apply
#print axioms outputAction_norm_square
#print axioms joint_graph
#print axioms closed_joint_graph
#print axioms closed_energy_graph
#print axioms closed_energy_domain
end
end UnifiedTheory.Audit.KFCausalClockFloorClosedChartModulation
