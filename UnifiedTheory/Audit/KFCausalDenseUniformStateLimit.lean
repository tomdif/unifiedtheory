/- Extend uniform trajectory convergence from a dense set of initial states
using a derived common initial-state stability bound. -/
import UnifiedTheory.Audit.KFCausalCoerciveCauchyLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDenseUniformStateLimit
noncomputable section
open Set Filter Topology
variable {V : Type*} [NormedAddCommGroup V]

theorem uniform_cauchy_of_dense (w : ℕ → V → ℝ → V) (D : Set V) (I : Set ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hD : Dense D)
    (hstable : ∀ n x y t, t ∈ I → ‖w n x t-w n y t‖ ≤ L*‖x-y‖)
    (hDconv : ∀ x ∈ D, UniformCauchySeqOn (fun n => w n x) atTop I) (x : V) :
    UniformCauchySeqOn (fun n => w n x) atTop I := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro eps heps
  have hLp : 0 < L+1 := by linarith
  obtain ⟨y,hy,hxy⟩ := hD.exists_dist_lt x (ε := eps/(3*(L+1))) (div_pos heps (mul_pos (by norm_num) hLp))
  obtain ⟨N,hN⟩ := (Metric.uniformCauchySeqOn_iff.mp (hDconv y hy)) (eps/3) (by positivity)
  have hclose : L*‖x-y‖ < eps/3 := by
    rw [dist_eq_norm] at hxy
    have hh := (lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<3) hLp)).mp hxy
    have hn := norm_nonneg (x-y)
    linarith
  refine ⟨N,fun m hm n hn t ht => ?_⟩
  have hfirst := (hstable m x y t ht).trans_lt hclose
  have hlast : ‖w n y t-w n x t‖ < eps/3 := by
    simpa only [norm_sub_rev] using (hstable n x y t ht).trans_lt hclose
  have hmid : ‖w m y t-w n y t‖ < eps/3 := by simpa only [dist_eq_norm] using hN m hm n hn t ht
  have htri := dist_triangle (w m x t) (w m y t) (w n x t)
  have htri' := dist_triangle (w m y t) (w n y t) (w n x t)
  simp only [dist_eq_norm] at htri htri'
  rw [dist_eq_norm]
  linarith

theorem exists_uniform_limits [CompleteSpace V] (w : ℕ → V → ℝ → V) (l r : ℝ)
    (hwc : ∀ n x, ContinuousOn (w n x) (Icc l r))
    (hc : ∀ x, UniformCauchySeqOn (fun n => w n x) atTop (Icc l r)) :
    ∃ u : V → ℝ → V, ∀ x,
      ContinuousOn (u x) (Icc l r) ∧ TendstoUniformlyOn (fun n => w n x) (u x) atTop (Icc l r) := by
  let u : V → ℝ → V := fun x t => limUnder atTop (fun n => w n x t)
  have hu (x : V) : TendstoUniformlyOn (fun n => w n x) (u x) atTop (Icc l r) :=
    (hc x).tendstoUniformlyOn_of_tendsto (fun t ht => ((hc x).cauchySeq ht).tendsto_limUnder)
  exact ⟨u,fun x => ⟨(hu x).continuousOn (Eventually.of_forall (fun n => hwc n x)).frequently,hu x⟩⟩

theorem limit_stability (w : ℕ → V → ℝ → V) (u : V → ℝ → V) (I : Set ℝ) (L : ℝ)
    (hu : ∀ x, TendstoUniformlyOn (fun n => w n x) (u x) atTop I)
    (hstable : ∀ n x y t, t ∈ I → ‖w n x t-w n y t‖ ≤ L*‖x-y‖) :
    ∀ x y t, t ∈ I → ‖u x t-u y t‖ ≤ L*‖x-y‖ := by
  intro x y t ht
  exact le_of_tendsto_of_tendsto (((hu x).tendsto_at ht).sub ((hu y).tendsto_at ht)).norm
    tendsto_const_nhds (Eventually.of_forall (fun n => hstable n x y t ht))

#print axioms uniform_cauchy_of_dense
#print axioms exists_uniform_limits
#print axioms limit_stability
end
end UnifiedTheory.Audit.KFCausalDenseUniformStateLimit
