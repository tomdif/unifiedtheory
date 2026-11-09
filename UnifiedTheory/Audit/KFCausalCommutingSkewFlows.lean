/- Commuting bounded skew-adjoint generators have a statewise flow
comparison estimate, without a bound on their operator norms. -/
import UnifiedTheory.Audit.KFCausalHilbertEvolutionStability

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalCommutingSkewFlows
noncomputable section
open Set Filter
open scoped Topology
open KFCausalHilbertEvolution KFCausalHilbertStateEvolution
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "M" => H →L[ℂ] H

def flow (A : M) (hs : star A = -A) (t : ℝ) : M :=
  evolution (fun _ => A) continuous_const (fun _ => hs) 0 t

theorem flow_initial (A : M) (hs : star A = -A) : flow A hs 0=1 :=
  evolution_initial _ _ _ 0

theorem flow_norm (A : M) (hs : star A = -A) (t : ℝ) (x : H) :
    ‖flow A hs t x‖=‖x‖ := evolution_norm _ _ _ 0 t x

theorem flow_derivative (A : M) (hs : star A = -A) (t : ℝ) (x : H) :
    HasDerivAt (fun u => flow A hs u x) (A (flow A hs t x)) t :=
  evolution_state_derivative _ _ _ 0 t x

theorem commutes (A L : M) (hs : star A = -A) (hc : L*A=A*L) (t : ℝ) (x : H) :
    L (flow A hs t x)=flow A hs t (L x) := by
  have he := evolution_state_unique (fun _ => A) continuous_const (fun _ => hs) 0 (L x)
    (fun u => L (flow A hs u x)) (by change L (flow A hs 0 x)=L x; rw [flow_initial,ContinuousLinearMap.one_apply])
    (fun u => by
      have hd := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt u (flow_derivative A hs u x)
      have hv := congrArg (fun Q : M => Q (flow A hs u x)) hc
      exact hd.congr_deriv hv)
  exact congrFun he t

theorem flow_add (A : M) (hs : star A = -A) (s t : ℝ) (x : H) :
    flow A hs (s+t) x=flow A hs t (flow A hs s x) := by
  have he := evolution_state_unique (fun _ => A) continuous_const (fun _ => hs) 0
    (flow A hs s x) (fun u => flow A hs (s+u) x) (by simp only [add_zero])
    (fun u => by
      simpa only [Function.comp_def,one_smul] using
        (flow_derivative A hs (s+u) x).scomp u ((hasDerivAt_id u).const_add s))
  exact congrFun he t

theorem difference_bound (A B : M) (hsA : star A = -A) (hsB : star B = -B)
    (hc : A*B=B*A) (t : ℝ) (x : H) :
    ‖flow A hsA t x-flow B hsB t x‖ ≤ ‖(B-A) x‖*|t| := by
  have hm : (B-A)*B=B*(B-A) := by rw [sub_mul,mul_sub,hc]
  have he := KFCausalHilbertEvolutionStability.evolution_difference_bound
    (fun _ => A) (fun _ => B) continuous_const continuous_const (fun _ => hsA) (fun _ => hsB)
    0 t ‖(B-A) x‖ x (fun u _ => by
      change ‖(B-A) (flow B hsB u x)‖ ≤ ‖(B-A) x‖
      rw [commutes B (B-A) hsB hm,flow_norm])
  simpa only [sub_zero] using he

theorem dense_comparison (A B : M) (hsA : star A = -A) (hsB : star B = -B)
    (hc : A*B=B*A) (t : ℝ) (x y : H) :
    ‖flow A hsA t x-flow B hsB t x‖ ≤ 2*‖x-y‖+‖(B-A) y‖*|t| := by
  have he : flow A hsA t x-flow B hsB t x =
      flow A hsA t (x-y)+(flow A hsA t y-flow B hsB t y)-flow B hsB t (x-y) := by
    rw [map_sub,map_sub]; abel
  rw [he]
  calc
    _ ≤ ‖flow A hsA t (x-y)+(flow A hsA t y-flow B hsB t y)‖+‖flow B hsB t (x-y)‖ := norm_sub_le _ _
    _ ≤ (‖flow A hsA t (x-y)‖+‖flow A hsA t y-flow B hsB t y‖)+‖flow B hsB t (x-y)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (‖x-y‖+‖(B-A) y‖*|t|)+‖x-y‖ := by
      rw [flow_norm,flow_norm]
      exact add_le_add (add_le_add le_rfl (difference_bound A B hsA hsB hc t y)) le_rfl
    _ = _ := by ring

#print axioms flow_initial
#print axioms flow_norm
#print axioms flow_derivative
#print axioms commutes
#print axioms flow_add
#print axioms difference_bound
#print axioms dense_comparison
end
end UnifiedTheory.Audit.KFCausalCommutingSkewFlows
