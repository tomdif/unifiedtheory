/- Locally bounded curves inherit weak continuity from a dense family
of continuous scalar pairings. A varying strongly continuous test vector
can then be paired with such a curve. -/
import UnifiedTheory.Audit.KFCausalWeakContinuity
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalLocalWeakContinuity
noncomputable section
open Filter TopologicalSpace Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalWeakContinuity

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem weak_continuous_of_locally_bounded_dense_tests (J : D → E) (hJ : DenseRange J)
    (u : ℝ → E) (M : ℝ → ℝ)
    (hb : ∀ T t, 0 ≤ T → |t| ≤ T → ‖u t‖ ≤ M T)
    (hc : ∀ y, Continuous (fun t => inner ℂ (u t) (J y))) :
    ∀ y, Continuous (fun t => inner ℂ (u t) y) := by
  intro y
  apply continuous_iff_continuousAt.mpr
  intro t
  let T := |t|+1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have ht1 : -T < t := by dsimp [T]; linarith [neg_abs_le t]
  have ht2 : t < T := by dsimp [T]; linarith [le_abs_self t]
  have hs : ContinuousOn (fun z => inner ℂ (u z) y) (Ioo (-T) T) := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact weak_continuous_of_dense_tests J hJ (fun z : Ioo (-T) T => u z) (M T)
      (fun z => hb T z hT (abs_le.mpr ⟨z.property.1.le,z.property.2.le⟩))
      (fun v => (hc v).comp continuous_subtype_val) y
  exact hs.continuousAt (Ioo_mem_nhds ht1 ht2)

theorem weak_strong_pairing_continuous (u v : ℝ → E) (M : ℝ → ℝ)
    (hb : ∀ T t, 0 ≤ T → |t| ≤ T → ‖u t‖ ≤ M T)
    (hu : ∀ y, Continuous (fun t => inner ℂ (u t) y)) (hv : Continuous v) :
    Continuous (fun t => inner ℂ (u t) (v t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let T := |t|+1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have ht1 : -T < t := by dsimp [T]; linarith [neg_abs_le t]
  have ht2 : t < T := by dsimp [T]; linarith [le_abs_self t]
  have hlocal : ∀ᶠ z in 𝓝 t, ‖u z‖ ≤ M T := by
    filter_upwards [Ioo_mem_nhds ht1 ht2] with z hz
    exact hb T z hT (abs_le.mpr ⟨hz.1.le,hz.2.le⟩)
  have hnorm : Tendsto (fun z => M T*‖v z-v t‖) (𝓝 t) (𝓝 0) := by
    simpa only [sub_self,norm_zero,mul_zero] using ((hv.tendsto t).sub_const (v t)).norm.const_mul (M T)
  have he : Tendsto (fun z => inner ℂ (u z) (v z-v t)) (𝓝 t) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall (fun z => norm_nonneg _)) _ hnorm
    exact hlocal.mono (fun z hz => (norm_inner_le_norm (u z) (v z-v t)).trans
      (mul_le_mul_of_nonneg_right hz (norm_nonneg _)))
  have hh := ((hu (v t)).tendsto t).add he
  simp only [add_zero] at hh
  have heq : (fun z => inner ℂ (u z) (v t)+inner ℂ (u z) (v z-v t)) =
      (fun z => inner ℂ (u z) (v z)) := by
    funext z
    rw [inner_sub_right]
    abel
  rw [heq] at hh
  exact hh

omit [InnerProductSpace ℂ E] in
theorem continuous_of_window_lipschitz (u : ℝ → E) (C : ℝ → ℝ)
    (hC : ∀ T, 0 ≤ T → 0 ≤ C T)
    (hb : ∀ T x y, 0 ≤ T → |x| ≤ T → |y| ≤ T → ‖u y-u x‖ ≤ C T*|y-x|) :
    Continuous u := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let T := |t|+1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have ht1 : -T < t := by dsimp [T]; linarith [neg_abs_le t]
  have ht2 : t < T := by dsimp [T]; linarith [le_abs_self t]
  have hL : LipschitzOnWith ⟨C T,hC T hT⟩ u (Icc (-T) T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [dist_eq_norm,Real.norm_eq_abs] using hb T y x hT (abs_le.mpr hy) (abs_le.mpr hx)
  exact hL.continuousOn.continuousAt (Icc_mem_nhds ht1 ht2)

#print axioms weak_continuous_of_locally_bounded_dense_tests
#print axioms weak_strong_pairing_continuous
#print axioms continuous_of_window_lipschitz

end
end UnifiedTheory.Audit.KFCausalLocalWeakContinuity
