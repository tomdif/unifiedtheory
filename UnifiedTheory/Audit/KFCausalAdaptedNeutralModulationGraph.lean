/- A bounded triangular action on the actual weighted joint energy graph
and its closure. Only the second kinetic output changes. No division by
energy weights is used, so vanishing matter couplings are included. -/
import UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationFactors
import UnifiedTheory.Audit.KFCausalClockFloorJointEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationGraph
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationCoordinates
open UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationFactors
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output jointGraph)

abbrev Outputs := Output (Fin 8) Hilbert

def extra (ε : ℝ) (hε : 0 < ε) (h v : ℝ) (w : Fin 8 → ℂ) : Hilbert →L[ℂ] Outputs where
  toFun f := WithLp.toLp 2 (Pi.single 2 (((-3*h*v : ℝ) : ℂ) • (w 2 • inverseL ε hε f)))
  map_add' f g := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [map_add,smul_add]
  map_smul' c f := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [map_smul]
    module
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => by
    fin_cases i <;> simp <;> fun_prop))

def modulateOutput (v : ℝ) : Outputs →L[ℂ] Outputs where
  toFun g := WithLp.toLp 2 (fun i => action v (g i))
  map_add' f g := by ext i; simp [map_add]
  map_smul' c g := by ext i; simp [map_smul]
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => (action v).continuous.comp (PiLp.continuous_apply 2 _ i)))

theorem extra_norm (ε : ℝ) (hε : 0 < ε) (h v : ℝ) (w : Fin 8 → ℂ) (f : Hilbert) :
    ‖extra ε hε h v w f‖ = 3*|h| * |v| *‖w 2‖*‖inverseL ε hε f‖ := by
  change ‖(WithLp.toLp 2 (Pi.single 2 (((-3*h*v : ℝ) : ℂ) • (w 2 • inverseL ε hε f))) : Outputs)‖ = _
  rw [PiLp.norm_toLp_single,norm_smul,norm_smul,Complex.norm_real,
    Real.norm_eq_abs,abs_mul,abs_mul]
  norm_num
  ring

theorem modulateOutput_norm (v : ℝ) (g : Outputs) : ‖modulateOutput v g‖ = ‖g‖ := by
  have he : ‖modulateOutput v g‖^2 = ‖g‖^2 := by
    simp only [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun x : ℝ => x^2) ((action v).norm_map (g i))
  nlinarith [norm_nonneg (modulateOutput v g),norm_nonneg g]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (v : ℝ) (w : Fin 8 → ℂ)
include hne

theorem joint_graph_action (f : Hilbert) (g : Outputs)
    (hfg : (f,g) ∈ jointGraph (energyFactor ε hε h modelDirections pointField) w) :
    (action v f,modulateOutput v (g+extra ε hε h v w f)) ∈
      jointGraph (energyFactor ε hε h modelDirections pointField) w := by
  intro i
  fin_cases i
  · simpa [modulateOutput,extra,map_smul] using
      clockHalf_graph_action ε v (w 0 • f) (g 0) (hfg 0)
  · simpa [modulateOutput,extra,map_smul,frequency_apply,coordinate_apply,modelDirections] using
      kinetic_graph_action ε hε h hne v (modelDirections 0) (w 1 • f) (g 1) (hfg 1)
  · have hc : ((h*frequency v (0,modelDirections 1) : ℝ) : ℂ) = ((-3*h*v : ℝ) : ℂ) := by
      simp [frequency_apply,coordinate_apply,modelDirections]
      ring
    simpa [modulateOutput,extra,map_smul,hc] using
      kinetic_graph_action ε hε h hne v (modelDirections 1) (w 2 • f) (g 2) (hfg 2)
  · simpa [modulateOutput,extra,map_smul,frequency_apply,coordinate_apply,modelDirections] using
      kinetic_graph_action ε hε h hne v (modelDirections 2) (w 3 • f) (g 3) (hfg 3)
  · simpa [modulateOutput,extra,map_smul,frequency_apply,coordinate_apply,modelDirections] using
      kinetic_graph_action ε hε h hne v (modelDirections 3) (w 4 • f) (g 4) (hfg 4)
  · simpa [modulateOutput,extra,map_smul] using
      linear_matter_graph_action ε hε h v pointField (w 5 • f) (g 5) (hfg 5)
  · simpa [modulateOutput,extra,map_smul] using
      quadratic_matter_graph_action ε hε h v pointField (w 6 • f) (g 6) (hfg 6)
  · simpa [modulateOutput,extra,map_smul] using
      ordered_graph_action ε hε h v (w 7 • f) (g 7) (hfg 7)

def pairAction : (Hilbert × Outputs) →L[ℂ] (Hilbert × Outputs) :=
  ((action v : Hilbert →L[ℂ] Hilbert).comp (ContinuousLinearMap.fst ℂ Hilbert Outputs)).prod
    ((modulateOutput v).comp (ContinuousLinearMap.snd ℂ Hilbert Outputs+
      (extra ε hε h v w).comp (ContinuousLinearMap.fst ℂ Hilbert Outputs)))

theorem joint_closure_action (f : Hilbert) (g : Outputs)
    (hfg : (f,g) ∈ (jointGraph (energyFactor ε hε h modelDirections pointField) w).topologicalClosure) :
    (action v f,modulateOutput v (g+extra ε hε h v w f)) ∈
      (jointGraph (energyFactor ε hε h modelDirections pointField) w).topologicalClosure := by
  let S := jointGraph (energyFactor ε hε h modelDirections pointField) w
  let P := pairAction ε hε h v w
  have hs : S ≤ S.topologicalClosure.comap P.toLinearMap :=
    fun z hz => S.le_topologicalClosure (joint_graph_action ε hε h hne v w z.1 z.2 hz)
  have hc : IsClosed (S.topologicalClosure.comap P.toLinearMap : Set (Hilbert × Outputs)) :=
    S.isClosed_topologicalClosure.preimage P.continuous
  exact S.topologicalClosure_minimal hs hc hfg

theorem closed_energy_graph_action (m g k t : ℝ) (hh : |h| ≤ Real.pi*ε)
    (f : Hilbert) (y : Outputs)
    (hfy : (f,y) ∈ (closedEnergy ε hε h modelDirections pointField m g k t).graph) :
    (action v f,modulateOutput v (y+extra ε hε h v (energyWeight m g k t) f)) ∈
      (closedEnergy ε hε h modelDirections pointField m g k t).graph := by
  rw [closedEnergy_graph ε hε h modelDirections pointField m g k t hh] at hfy ⊢
  exact joint_closure_action ε hε h hne v _ f y hfy

theorem closed_energy_domain_action (m g k t : ℝ) (hh : |h| ≤ Real.pi*ε) (f : Hilbert)
    (hf : f ∈ (closedEnergy ε hε h modelDirections pointField m g k t).domain) :
    action v f ∈ (closedEnergy ε hε h modelDirections pointField m g k t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (closed_energy_graph_action ε hε h hne v m g k t hh f _
      ((closedEnergy ε hε h modelDirections pointField m g k t).mem_graph ⟨f,hf⟩))

theorem closed_energy_domain_action_iff (m g k t : ℝ) (hh : |h| ≤ Real.pi*ε) (f : Hilbert) :
    action v f ∈ (closedEnergy ε hε h modelDirections pointField m g k t).domain ↔
      f ∈ (closedEnergy ε hε h modelDirections pointField m g k t).domain := by
  refine ⟨fun hf => ?_,closed_energy_domain_action ε hε h hne v m g k t hh f⟩
  simpa only [action_inverse] using
    closed_energy_domain_action ε hε h hne (-v) m g k t hh _ hf

#print axioms extra_norm
#print axioms modulateOutput_norm
#print axioms joint_graph_action
#print axioms joint_closure_action
#print axioms closed_energy_graph_action
#print axioms closed_energy_domain_action
#print axioms closed_energy_domain_action_iff

end
end UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationGraph
