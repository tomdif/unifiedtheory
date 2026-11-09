/- The actual clock and four kinetic rows retain their natural closed
graphs under bare neutral-position phases. The full energy graph maps into
this kinetic graph; no converse or matter-domain assertion is made. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionCharge
import UnifiedTheory.Audit.KFCausalClockFloorKineticModulation
import UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionKineticGraph
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalNeutralPositionCharge
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf clockHalf_selfAdjoint)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorKineticModulation
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL inverseAction_norm_bound)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy (closedEnergy closedEnergy_component_graph)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output jointGraph)

abbrev Outputs := Output (Fin 5) Hilbert
def factor (ε h : ℝ) : Fin 5 → Hilbert →ₗ.[ℂ] Hilbert :=
  ![clockHalf ε,clockMomentum ε h (modelDirections 0),clockMomentum ε h (modelDirections 1),
    clockMomentum ε h (modelDirections 2),clockMomentum ε h (modelDirections 3)]
def weight (t : ℝ) : Fin 5 → ℂ :=
  ![Real.sqrt (1/2),Real.sqrt (1/2),Real.sqrt (1/2),
    (Real.exp t*Real.sqrt (1/2):ℝ),(Real.exp t*Real.sqrt (1/2):ℝ)]
def graph (ε h t : ℝ) := jointGraph (factor ε h) (weight t)

def select : Output (Fin 8) Hilbert →L[ℂ] Outputs where
  toFun y := WithLp.toLp 2 (fun i => y (i.castLE (by decide)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => PiLp.continuous_apply 2 _ (i.castLE (by decide))))

theorem select_norm (y : Output (Fin 8) Hilbert) : ‖select y‖ ≤ ‖y‖ := by
  have he : ‖select y‖^2 ≤ ‖y‖^2 := by
    simp only [PiLp.norm_sq_eq_of_L2,select,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,
      AddHom.coe_mk,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change ‖y 0‖^2+(‖y 1‖^2+(‖y 2‖^2+(‖y 3‖^2+‖y 4‖^2))) ≤
      ‖y 0‖^2+(‖y 1‖^2+(‖y 2‖^2+(‖y 3‖^2+(‖y 4‖^2+(‖y 5‖^2+(‖y 6‖^2+‖y 7‖^2))))))
    nlinarith [sq_nonneg ‖y 5‖,sq_nonneg ‖y 6‖,sq_nonneg ‖y 7‖]
  nlinarith [norm_nonneg (select y),norm_nonneg y]

theorem factor_closed (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 5) :
    (factor ε h i).IsClosed := by
  fin_cases i
  · exact (clockHalf_selfAdjoint ε).isClosed
  all_goals exact kinetic_closed ε hε h _

theorem full_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : |h| ≤ Real.pi*ε)
    (m g k t : ℝ) (f : Hilbert) (y : Output (Fin 8) Hilbert)
    (hfy : (f,y) ∈ (closedEnergy ε hε h modelDirections pointField m g k t).graph) :
    (f,select y) ∈ graph ε h t := by
  intro i
  have hc := closedEnergy_component_graph ε hε h modelDirections pointField m g k t hh f y hfy
    (i.castLE (by decide))
  have hfactor : energyFactor ε hε h modelDirections pointField (i.castLE (by decide)) = factor ε h i := by
    fin_cases i <;> rfl
  have hw : energyWeight m g k t (i.castLE (by decide)) = weight t i := by
    fin_cases i <;> rfl
  rw [hfactor,hw] at hc
  have hs := factor_closed ε hε h i
  rw [hs.isClosable.graph_closure_eq_closure_graph.symm.trans hs.submodule_topologicalClosure_eq] at hc
  exact hc

def extra (ε : ℝ) (hε : 0 < ε) (h v : ℝ) : Hilbert →L[ℂ] Outputs where
  toFun f := WithLp.toLp 2 (Pi.single 2 (((h*v : ℝ) : ℂ) • ((Real.sqrt (1/2):ℂ) • inverseL ε hε f)))
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

theorem extra_norm (ε : ℝ) (hε : 0 < ε) (h v : ℝ) (f : Hilbert) :
    ‖extra ε hε h v f‖ = |h| * |v| *Real.sqrt (1/2)*‖inverseL ε hε f‖ := by
  change ‖(WithLp.toLp 2 (Pi.single 2 (((h*v : ℝ) : ℂ) • ((Real.sqrt (1/2):ℂ) • inverseL ε hε f))) : Outputs)‖ = _
  rw [PiLp.norm_toLp_single,norm_smul,norm_smul,Complex.norm_real,
    Real.norm_eq_abs,abs_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

theorem extra_bound (ε : ℝ) (hε : 0 < ε) (h v : ℝ) (f : Hilbert) :
    ‖extra ε hε h v f‖ ≤ |h| * (|v| *Real.sqrt (1/2)*(Real.sqrt ε)⁻¹)*‖f‖ := by
  rw [extra_norm]
  have hi := inverseAction_norm_bound ε hε f
  change ‖inverseL ε hε f‖ ≤ _ at hi
  exact (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ |h| * |v| *Real.sqrt (1/2))).trans_eq (by ring)

theorem modulateOutput_norm (v : ℝ) (g : Outputs) : ‖modulateOutput v g‖ = ‖g‖ := by
  have he : ‖modulateOutput v g‖^2 = ‖g‖^2 := by
    simp only [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun x : ℝ => x^2) ((action v).norm_map (g i))
  nlinarith [norm_nonneg (modulateOutput v g),norm_nonneg g]

theorem graph_action (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (v t : ℝ)
    (f : Hilbert) (y : Outputs) (hfy : (f,y) ∈ graph ε h t) :
    (action v f,modulateOutput v (y+extra ε hε h v f)) ∈ graph ε h t := by
  intro i
  fin_cases i
  · simpa [modulateOutput,extra,map_smul,action] using
      clockHalf_graph_modulation ε (frequency v) (weight t 0 • f) (y 0) (hfy 0)
  · simpa [modulateOutput,extra,map_smul,action,frequency_apply,modelDirections] using
      kinetic_graph_modulation ε hε h hne (modelDirections 0) (frequency v) (weight t 1 • f) (y 1) (hfy 1)
  · simpa [modulateOutput,extra,map_smul,action,frequency_apply,modelDirections,weight] using
      kinetic_graph_modulation ε hε h hne (modelDirections 1) (frequency v) (weight t 2 • f) (y 2) (hfy 2)
  · simpa [modulateOutput,extra,map_smul,action,frequency_apply,modelDirections] using
      kinetic_graph_modulation ε hε h hne (modelDirections 2) (frequency v) (weight t 3 • f) (y 3) (hfy 3)
  · simpa [modulateOutput,extra,map_smul,action,frequency_apply,modelDirections] using
      kinetic_graph_modulation ε hε h hne (modelDirections 3) (frequency v) (weight t 4 • f) (y 4) (hfy 4)

#print axioms select_norm
#print axioms factor_closed
#print axioms full_graph
#print axioms extra_norm
#print axioms extra_bound
#print axioms modulateOutput_norm
#print axioms graph_action

end
end UnifiedTheory.Audit.KFCausalNeutralPositionKineticGraph
