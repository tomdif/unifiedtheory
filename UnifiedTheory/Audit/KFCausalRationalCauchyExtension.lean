/- A locally uniform Lipschitz bound extends the Cauchy property of a
sequence of curves from rational times to every real time. -/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRationalCauchyExtension
open Filter

variable {X : Type*} [PseudoMetricSpace X]

theorem rational_cauchy_extension (F : ℕ → ℝ → X)
    (hl : ∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, 0 ≤ C ∧
      ∀ n x y, |x| ≤ T → |y| ≤ T → dist (F n x) (F n y) ≤ C*|x-y|)
    (hq : ∀ q : ℚ, CauchySeq (fun n => F n (q:ℝ))) (t : ℝ) :
    CauchySeq (fun n => F n t) := by
  let T := |t|+1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨C,hC,hL⟩ := hl T hT
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hC1 : 0 < C+1 := by linarith
  have hδ : 0 < min 1 (ε/(4*(C+1))) := lt_min (by norm_num) (by positivity)
  obtain ⟨q,hqt⟩ := (Rat.denseRange_cast (𝕜 := ℝ)).exists_dist_lt t hδ
  rw [Real.dist_eq] at hqt
  have hq1 : |t-(q:ℝ)| < 1 := hqt.trans_le (min_le_left _ _)
  have hqδ : |t-(q:ℝ)| < ε/(4*(C+1)) := hqt.trans_le (min_le_right _ _)
  have htT : |t| ≤ T := by dsimp [T]; linarith
  have hqT : |(q:ℝ)| ≤ T := by
    have ht : |(q:ℝ)| ≤ |t-(q:ℝ)|+|t| := by
      simpa only [sub_zero,abs_sub_comm (q:ℝ) t] using abs_sub_le (q:ℝ) t 0
    dsimp [T]
    linarith
  have herr : C*|t-(q:ℝ)| < ε/4 := by
    have hh := mul_lt_mul_of_pos_left hqδ hC1
    have he : (C+1)*(ε/(4*(C+1))) = ε/4 := by field_simp
    rw [he] at hh
    nlinarith [abs_nonneg (t-(q:ℝ))]
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (hq q) (ε/2) (by positivity)
  refine ⟨N,?_⟩
  intro m hm n hn
  have hleft : dist (F m t) (F m (q:ℝ)) < ε/4 := (hL m t q htT hqT).trans_lt herr
  have hright : dist (F n (q:ℝ)) (F n t) < ε/4 := by
    rw [dist_comm]
    exact (hL n t q htT hqT).trans_lt herr
  have hmid := hN m hm n hn
  have htri := dist_triangle (F m t) (F m (q:ℝ)) (F n t)
  have htri' := dist_triangle (F m (q:ℝ)) (F n (q:ℝ)) (F n t)
  linarith

#print axioms rational_cauchy_extension

end UnifiedTheory.Audit.KFCausalRationalCauchyExtension
