/- Identification of the strong derivative of the constructed limit,
and preservation of bounded operators commuting with every approximant. -/
import UnifiedTheory.Audit.KFCausalCommutingSkewFlowLimit
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalCommutingSkewFlowGenerator
noncomputable section
open Set Filter
open scoped Topology
open KFCausalCommutingSkewFlows KFCausalCommutingSkewFlowLimit
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (D : Data H)
local notation "U" => fun n t => flow (D.generator n) (D.skew n) t

theorem uniform_moving_input (x : ℕ → H) (y : H) (hx : Tendsto x atTop (𝓝 y))
    (T : ℝ) (hT : 0 ≤ T) :
    TendstoUniformlyOn (fun n t => U n t (x n)) (fun t => value D t y) atTop (Icc (-T) T) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro δ hδ
  have hy := Metric.tendstoUniformlyOn_iff.mp (uniform_limit D y T hT) (δ/2) (by positivity)
  have hx' := (tendsto_iff_norm_sub_tendsto_zero.mp hx).eventually
    (gt_mem_nhds (show 0 < δ/2 by positivity))
  filter_upwards [hy,hx'] with n hn hxn t ht
  have he : ‖U n t (x n)-U n t y‖=‖x n-y‖ := by rw [← map_sub,flow_norm]
  have hb := norm_sub_le_norm_sub_add_norm_sub (U n t (x n)) (U n t y) (value D t y)
  have hn' := hn t ht
  rw [dist_eq_norm,norm_sub_rev] at hn' ⊢
  rw [he] at hb
  linarith

theorem derivative (x y : H) (hx : Tendsto (fun n => D.generator n x) atTop (𝓝 y)) (t : ℝ) :
    HasDerivAt (fun u => value D u x) (value D t y) t := by
  have hu := uniform_moving_input D (fun n => D.generator n x) y hx (|t|+1) (by positivity)
  apply hasDerivAt_of_tendstoUniformlyOn (s := Ioo (-(|t|+1)) (|t|+1)) isOpen_Ioo
    (hu.mono Ioo_subset_Icc_self)
  · exact Eventually.of_forall (fun n u _ => (flow_derivative (D.generator n) (D.skew n) u x).congr_deriv
      (commutes (D.generator n) (D.generator n) (D.skew n) rfl u x))
  · exact fun u _ => tendsto_value D u x
  · exact ⟨by linarith [neg_abs_le t],by linarith [le_abs_self t]⟩

theorem commutes (L : H →L[ℂ] H) (hc : ∀ n, L*D.generator n=D.generator n*L) (t : ℝ) (x : H) :
    L (value D t x)=value D t (L x) := by
  apply tendsto_nhds_unique ((L.continuous.tendsto (value D t x)).comp (tendsto_value D t x))
  exact (tendsto_value D t (L x)).congr' (Eventually.of_forall (fun n =>
    (KFCausalCommutingSkewFlows.commutes (D.generator n) L (D.skew n) (hc n) t x).symm))

#print axioms uniform_moving_input
#print axioms derivative
#print axioms commutes
end
end UnifiedTheory.Audit.KFCausalCommutingSkewFlowGenerator
