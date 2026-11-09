/- The clock defect preserves the entire natural half-exponential domain.
The identity A D = B A is proved on an explicit Gaussian graph core and
extended by closedness; full-domain preservation is not a premise. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGraph
import UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectFullDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalGaussianStrip
open UnifiedTheory.Audit.KFCausalClockFloorGaussianGraph
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectBounds
open UnifiedTheory.Audit.KFCausalClockFloorExponential

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)

include hε in
theorem defect_analytic (q : ℂ) (hq : |q.im| ≤ Real.pi*ε/3) :
    AnalyticAt ℂ (complexDefect ε) q :=
  complexDefect_analytic ε hε q (KFCausalClockFloorFullGaussian.third_strip_subset ε hε q hq)

def unitState (v : Space) (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) : Hilbert :=
  physicalState (fun _ => 1) v (Real.pi*ε/3) 1 (fun _ _ => analyticAt_const)
    (by norm_num) (fun _ _ => by simp) ε hε y hy

def defectState (v : Space) (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) : Hilbert :=
  physicalState (complexDefect ε) v (Real.pi*ε/3) 2 (defect_analytic ε hε)
    (by norm_num) (complexDefect_norm_le_two ε hε) ε hε y hy

theorem unitState_zero (v : Space) (h0 : |(0:ℝ)| ≤ Real.pi*ε/3) :
    unitState ε hε v 0 h0 = (KFCausalClockFloorGaussianCore.packet ε hε hbar v).1 :=
  physicalState_one_eq_packet ε hε hbar v (Real.pi*ε/3) h0

theorem unitState_shift (v : Space) :
    unitState ε hε v (-hbar/2) (shift_bound ε hbar hh) =
      (KFCausalClockFloorGaussianCore.packet ε hε hbar v).2 := by
  have h0 : |(0:ℝ)| ≤ Real.pi*ε/3 := by simp; positivity
  exact (longitudinalExponential ε hε hbar (1/2)).mem_graph_snd_inj'
    (physicalState_half_graph (fun _ => 1) v (Real.pi*ε/3) 1 (fun _ _ => analyticAt_const)
      (by norm_num) (fun _ _ => by simp) ε hε hbar h0 (shift_bound ε hbar hh))
    (KFCausalClockFloorGaussianCore.packet_mem_graph ε hε hbar v)
    (unitState_zero ε hε hbar v h0)

theorem defect_unitState (v : Space) (h0 : |(0:ℝ)| ≤ Real.pi*ε/3) :
    defectOperator ε hε (unitState ε hε v 0 h0) = defectState ε hε v 0 h0 := by
  apply (straightening ε hε).injective
  apply Lp.ext
  filter_upwards [straightening_defect_coe ε hε (unitState ε hε v 0 h0),
    physicalState_coe (fun _ => 1) v (Real.pi*ε/3) 1 (fun _ _ => analyticAt_const)
      (by norm_num) (fun _ _ => by simp) ε hε 0 h0,
    physicalState_coe (complexDefect ε) v (Real.pi*ε/3) 2 (defect_analytic ε hε)
      (by norm_num) (complexDefect_norm_le_two ε hε) ε hε 0 h0] with x hd hu hf
  change (straightening ε hε (unitState ε hε v 0 h0)) x = _ at hu
  change (straightening ε hε (defectState ε hε v 0 h0)) x = _ at hf
  rw [hd,hu,hf]
  simp only [spectralLine,Function.comp_apply,euclideanSplit_apply,line,trial,
    Complex.ofReal_zero,zero_mul,add_zero,one_mul,complexDefect_real ε hε,mul_assoc]

theorem shifted_unitState (v : Space) :
    shiftedDefect ε hε hbar hh (unitState ε hε v (-hbar/2) (shift_bound ε hbar hh)) =
      defectState ε hε v (-hbar/2) (shift_bound ε hbar hh) := by
  apply (straightening ε hε).injective
  apply Lp.ext
  filter_upwards [shiftedDefect_coe ε hε hbar hh (unitState ε hε v (-hbar/2) (shift_bound ε hbar hh)),
    physicalState_coe (fun _ => 1) v (Real.pi*ε/3) 1 (fun _ _ => analyticAt_const)
      (by norm_num) (fun _ _ => by simp) ε hε (-hbar/2) (shift_bound ε hbar hh),
    physicalState_coe (complexDefect ε) v (Real.pi*ε/3) 2 (defect_analytic ε hε)
      (by norm_num) (complexDefect_norm_le_two ε hε) ε hε (-hbar/2) (shift_bound ε hbar hh)] with x hd hu hf
  change (straightening ε hε (unitState ε hε v (-hbar/2) (shift_bound ε hbar hh))) x = _ at hu
  change (straightening ε hε (defectState ε hε v (-hbar/2) (shift_bound ε hbar hh))) x = _ at hf
  rw [hd,hu,hf]
  simp only [spectralLine,Function.comp_apply,euclideanSplit_apply,line,trial,symbol,one_mul,mul_assoc]

theorem packet_defect_graph (v : Space) :
    (defectOperator ε hε (KFCausalClockFloorGaussianCore.packet ε hε hbar v).1,
      shiftedDefect ε hε hbar hh (KFCausalClockFloorGaussianCore.packet ε hε hbar v).2) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph := by
  have h0 : |(0:ℝ)| ≤ Real.pi*ε/3 := by simp; positivity
  have hg := physicalState_half_graph (complexDefect ε) v (Real.pi*ε/3) 2
    (defect_analytic ε hε) (by norm_num) (complexDefect_norm_le_two ε hε)
    ε hε hbar h0 (shift_bound ε hbar hh)
  change (defectState ε hε v 0 h0,defectState ε hε v (-hbar/2) (shift_bound ε hbar hh)) ∈ _ at hg
  rw [← defect_unitState ε hε v h0,← shifted_unitState ε hε hbar hh v,
    unitState_zero ε hε hbar v h0,unitState_shift ε hε hbar hh v] at hg
  exact hg

theorem graph_defect (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε hbar (1/2)).graph) :
    (defectOperator ε hε f,shiftedDefect ε hε hbar hh g) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph := by
  let T := (defectOperator ε hε).prodMap (shiftedDefect ε hε hbar hh)
  have hS : Submodule.span ℂ (Set.range (KFCausalClockFloorGaussianCore.packet ε hε hbar)) ≤
      (longitudinalExponential ε hε hbar (1/2)).graph.comap T.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v,rfl⟩
    exact packet_defect_graph ε hε hbar hh v
  have hc := Submodule.topologicalClosure_minimal _ hS
    ((longitudinal_exponential_closed ε hε hbar (1/2)).preimage T.continuous)
  rw [KFCausalClockFloorGaussianCore.graph_core] at hc
  exact hc hfg

include hh in
theorem defect_domain (f : Hilbert) (hf : f ∈ (longitudinalExponential ε hε hbar (1/2)).domain) :
    defectOperator ε hε f ∈ (longitudinalExponential ε hε hbar (1/2)).domain :=
  LinearPMap.mem_domain_of_mem_graph (graph_defect ε hε hbar hh f _
    ((longitudinalExponential ε hε hbar (1/2)).mem_graph ⟨f,hf⟩))

theorem defect_action (f : (longitudinalExponential ε hε hbar (1/2)).domain) :
    longitudinalExponential ε hε hbar (1/2) ⟨defectOperator ε hε f,defect_domain ε hε hbar hh f f.property⟩ =
      shiftedDefect ε hε hbar hh (longitudinalExponential ε hε hbar (1/2) f) :=
  (longitudinalExponential ε hε hbar (1/2)).mem_graph_snd_inj'
    ((longitudinalExponential ε hε hbar (1/2)).mem_graph _)
    (graph_defect ε hε hbar hh f _ ((longitudinalExponential ε hε hbar (1/2)).mem_graph f)) rfl

theorem full_graph_control (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε hbar (1/2)).graph) :
    (defectOperator ε hε f,shiftedDefect ε hε hbar hh g) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph ∧
    (defectOperator ε hε (defectOperator ε hε f),
      shiftedDefect ε hε hbar hh (shiftedDefect ε hε hbar hh g)) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph ∧
    ‖shiftedDefect ε hε hbar hh g-defectOperator ε hε g‖ ≤
      (2*|hbar|/ε)*‖defectOperator ε hε (defectOperator ε hε g)‖ ∧
    0 ≤ hbar*(inner ℂ g (shiftedDefect ε hε hbar hh (shiftedDefect ε hε hbar hh g))).im := by
  have h1 := graph_defect ε hε hbar hh f g hfg
  exact ⟨h1,graph_defect ε hε hbar hh _ _ h1,shiftedDefect_difference ε hε hbar hh g,
    shiftedDefect_square_form_sign ε hε hbar hh g⟩

#print axioms defect_analytic
#print axioms unitState_zero
#print axioms unitState_shift
#print axioms defect_unitState
#print axioms shifted_unitState
#print axioms packet_defect_graph
#print axioms graph_defect
#print axioms defect_domain
#print axioms defect_action
#print axioms full_graph_control

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectFullDomain
