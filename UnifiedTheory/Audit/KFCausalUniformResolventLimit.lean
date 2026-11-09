/- Strong scaled-resolvent convergence, uniform over a time window, from
a common dense domain and bounded generator outputs on that domain. -/
import UnifiedTheory.Audit.KFCausalEventualResolventApproximation
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalUniformResolventLimit
noncomputable section
open Set Filter Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem error_from_left (R : V →L[ℂ] V) (b C : ℝ) (x y : V)
    (hb : 0 < b) (hbound : ∀ f, ‖b • R f‖ ≤ C*‖f‖)
    (hleft : R (b • x-y) = x) : ‖b • R x-x‖ ≤ b⁻¹*C*‖y‖ := by
  rw [map_sub,ContinuousLinearMap.map_smul_of_tower] at hleft
  have he : b • R x-x = R y :=
    sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hleft).trans (add_comm _ _))
  rw [he,mul_assoc]
  apply (le_inv_mul_iff₀ hb).mpr
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hb] using hbound y

theorem uniform_limit (D : Submodule ℂ V) (H : ℝ → D → V)
    (R : ℝ → ℝ → V →L[ℂ] V) (I : Set ℝ) (b₀ C : ℝ)
    (hb₀ : 0 < b₀) (hC : 0 ≤ C) (hdense : Dense (D : Set V))
    (hbound : ∀ b, b₀ ≤ b → ∀ t ∈ I, ∀ f, ‖b • R b t f‖ ≤ C*‖f‖)
    (hleft : ∀ b, b₀ ≤ b → ∀ t ∈ I, ∀ x : D, R b t (b • (x:V)-H t x) = x)
    (houtput : ∀ x : D, ∃ M : ℝ, ∀ t ∈ I, ‖H t x‖ ≤ M) (f : V) :
    TendstoUniformlyOn (fun b t => b • R b t f) (fun _ => f) atTop I := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  have hCp : 0 < C+1 := by linarith
  obtain ⟨x,hx,hfx⟩ := hdense.exists_dist_lt f (ε := eps/(4*(C+1))) (by positivity)
  let y : D := ⟨x,hx⟩
  obtain ⟨M,hM⟩ := houtput y
  filter_upwards [eventually_ge_atTop (max b₀ (4*C*|M|/eps))] with b hb
  have hb0 : b₀ ≤ b := (le_max_left _ _).trans hb
  have hbp : 0 < b := hb₀.trans_le hb0
  have hbl : 4*C*|M|/eps ≤ b := (le_max_right _ _).trans hb
  have hsmall : b⁻¹*C*|M| ≤ eps/4 := by
    rw [mul_assoc]
    apply (inv_mul_le_iff₀ hbp).mpr
    have hm := (div_le_iff₀ heps).mp hbl
    nlinarith
  have hclose : (C+1)*‖f-(y:V)‖ < eps/4 := by
    rw [dist_eq_norm] at hfx
    have hm := (lt_div_iff₀ (show 0 < 4*(C+1) by positivity)).mp hfx
    change ‖f-(y:V)‖*(4*(C+1)) < eps at hm
    nlinarith
  intro t ht
  have hy : ‖b • R b t (y:V)-(y:V)‖ ≤ eps/4 :=
    (error_from_left (R b t) b C y (H t y) hbp (hbound b hb0 t ht)
      (hleft b hb0 t ht y)).trans
      ((mul_le_mul_of_nonneg_left ((hM t ht).trans (le_abs_self M))
        (mul_nonneg (inv_nonneg.mpr hbp.le) hC)).trans hsmall)
  have he : b • R b t f-f = b • R b t (f-(y:V))+
      (b • R b t (y:V)-(y:V))+((y:V)-f) := by
    rw [map_sub,smul_sub]
    abel
  have hn : ‖b • R b t f-f‖ ≤ (C+1)*‖f-(y:V)‖+eps/4 := by
    rw [he]
    calc
      _ ≤ (‖b • R b t (f-(y:V))‖+‖b • R b t (y:V)-(y:V)‖)+‖(y:V)-f‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (C*‖f-(y:V)‖+eps/4)+‖(y:V)-f‖ :=
        add_le_add (add_le_add (hbound b hb0 t ht _) hy) le_rfl
      _ = _ := by rw [norm_sub_rev (y:V) f]; ring
  rw [dist_eq_norm,norm_sub_rev]
  linarith

#print axioms error_from_left
#print axioms uniform_limit
end
end UnifiedTheory.Audit.KFCausalUniformResolventLimit
