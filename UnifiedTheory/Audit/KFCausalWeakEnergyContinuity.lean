/- Weak lower semicontinuity of squared Hilbert norms, and strong
convergence from a weak limit and an asymptotically sharp upper bound.
These lemmas do not assume convergence of the energy itself. -/
import UnifiedTheory.Audit.KFCausalWeakLimitTransport
import UnifiedTheory.Audit.KFCausalWeakNormStrongLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalWeakEnergyContinuity
open Filter
open scoped Topology

variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem weak_norm_sq_le {u : ℕ → H} {x : H} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, ‖u n‖^2 ≤ C)
    (hw : ∀ y, Tendsto (fun n => inner ℂ (u n) y) atTop (𝓝 (inner ℂ x y))) :
    ‖x‖^2 ≤ C := by
  have hn : ‖x‖ ≤ Real.sqrt C := KFCausalWeakLimitTransport.weak_norm_le
    (fun n => (Real.le_sqrt (norm_nonneg _) hC).mpr (hb n)) hw
  exact (Real.le_sqrt (norm_nonneg _) hC).mp hn

/-- Lower semicontinuity of any squared bounded-output norm under a weak limit. -/
theorem weak_output_energy_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [CompleteSpace H] (A : V →L[ℂ] H) (q : V → ℝ)
    (hq : ∀ v, ‖A v‖^2 = q v) {u : ℕ → V} {x : V} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, q (u n) ≤ C)
    (hw : ∀ y, Tendsto (fun n => inner ℂ (u n) y) atTop (𝓝 (inner ℂ x y))) :
    q x ≤ C := by
  have hm := KFCausalWeakLimitTransport.weak_map A hw
  have hn := weak_norm_sq_le hC (fun n => (hq (u n)).le.trans (hb n)) hm
  exact (hq x).symm.le.trans hn

theorem strong_of_weak_sq_bound {u : α → H} {x : H} {l : Filter α}
    {B : α → ℝ}
    (hw : ∀ y, Tendsto (fun n => inner ℂ (u n) y) l (𝓝 (inner ℂ x y)))
    (hb : ∀ n, ‖u n‖^2 ≤ B n)
    (hB : Tendsto B l (𝓝 (‖x‖^2))) : Tendsto u l (𝓝 x) := by
  have hr := Complex.continuous_re.continuousAt.tendsto.comp (hw x)
  have hu : Tendsto (fun n => B n - 2*(inner ℂ (u n) x).re + ‖x‖^2) l (𝓝 0) := by
    have hs : (inner ℂ x x).re = ‖x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    have hh := (hB.sub (hr.const_mul 2)).add_const (‖x‖^2)
    change Tendsto (fun n => B n-2*(inner ℂ (u n) x).re+‖x‖^2) l
      (𝓝 (‖x‖^2-2*(inner ℂ x x).re+‖x‖^2)) at hh
    rw [hs] at hh
    convert hh using 1
    congr 1
    ring
  have hd : Tendsto (fun n => ‖u n-x‖^2) l (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) _ hu
    intro n
    have hs : ‖u n-x‖^2 = ‖u n‖^2-2*(inner ℂ (u n) x).re+‖x‖^2 := norm_sub_sq (𝕜 := ℂ) _ _
    rw [hs]
    linarith [hb n]
  have hn : Tendsto (fun n => ‖u n-x‖) l (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero]
      using (Real.continuous_sqrt.tendsto 0).comp hd
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

#print axioms weak_norm_sq_le
#print axioms weak_output_energy_le
#print axioms strong_of_weak_sq_bound

end UnifiedTheory.Audit.KFCausalWeakEnergyContinuity
