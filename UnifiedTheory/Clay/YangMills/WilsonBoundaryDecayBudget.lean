/- Bounds on the actual tilted connected covariance pass through the source
rectangle and the nonlinear four-boundary-message ratio. No decay estimate
for that covariance is assumed implicitly. -/
import UnifiedTheory.Clay.YangMills.WilsonBoundaryConnected

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonBoundaryDecayBudget
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonBoundaryConnected
open WilsonBoundaryMixedLimit

/-- Bounded logarithmic increments can be exponentiated without losing their
spatial decay rate. The factor depends on the local cap, not the volume. -/
theorem exp_increment (x M : ℝ) (hx : |x| ≤ M) :
    |Real.exp x - 1| ≤ Real.exp M * |x| := by
  have hM : 0 ≤ M := (abs_nonneg x).trans hx
  have h1 : 1 ≤ Real.exp M := Real.one_le_exp_iff.mpr hM
  by_cases h : 0 ≤ x
  · rw [abs_of_nonneg h] at hx ⊢
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr h))]
    have hm := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
    have he : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]; simp
    have hb := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx) h
    nlinarith only [hm, he, hb]
  · have hx0 : x ≤ 0 := le_of_not_ge h
    rw [abs_of_nonpos hx0]
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hx0))]
    have hm := mul_le_mul_of_nonneg_right h1 (neg_nonneg.mpr hx0)
    linarith [Real.add_one_le_exp x]

/-- A rectangle-uniform bound is required only for source strengths from zero to one. -/
theorem rectangle_bound (F : ℝ → ℝ → ℝ) (C : ℝ)
    (hF : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, |F s t| ≤ C) :
    |∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, F s t| ≤ C := by
  have hinner (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      ‖∫ t in (0 : ℝ)..1, F s t‖ ≤ C := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (f := F s) (C := C) (fun t ht => by
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        simpa only [Real.norm_eq_abs] using hF s hs t ⟨ht.1.le, ht.2⟩)
    simpa using h
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun s => ∫ t in (0 : ℝ)..1, F s t) (C := C)
    (fun s hs => by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      exact hinner s ⟨hs.1.le, hs.2⟩)
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h

variable (n : ℕ) [NeZero n]

def connected (β : ℝ) (j : ℕ) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (u : Slice n) (s t : ℝ) : ℝ :=
  CompactGibbsSource.covariance (WilsonSlabOperator.measure n)
    (CompactGibbsSource.action (boundaryAction n β j u) (source n β e q u) s)
    (source n β d r u) (source n β e q u) (source n β d r u) t

/-- This concerns the literal finite Wilson message, including its endpoint weight. -/
theorem mixedLog_of_connected (β : ℝ) (j : ℕ) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (hed : e ≠ d) (u : Slice n) (C : ℝ)
    (hcov : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |connected n β j e d q r u s t| ≤ C) :
    |mixedLog n β j e d q r u| ≤ C := by
  rw [mixedLog_integral n β j e d q r hed]
  exact rectangle_bound (connected n β j e d q r u) C hcov

/-- The local bound is proved, with the same shrinking-rotation scaling as the Gram cap. -/
theorem mixedLog_scaled (β : ℝ) (hβ : 0 ≤ β) (j : ℕ)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (hed : e ≠ d) (u : Slice n)
    (hscaleq : β * ‖(q : Quaternion ℝ) - 1‖ ≤ 1)
    (hscaler : β * ‖(r : Quaternion ℝ) - 1‖ ≤ 1) :
    |mixedLog n β j e d q r u| ≤ 4 := by
  have h := mul_le_mul hscaleq hscaler
    (mul_nonneg hβ (norm_nonneg _)) (by norm_num : (0 : ℝ) ≤ 1)
  have hb := mixedLog_bound n β hβ j e d q r hed u
  nlinarith only [h, hb]

/-- This retains the nonlinear ratio, rather than replacing it by its logarithm. -/
theorem boundaryRatio_bound (β : ℝ) (j : ℕ) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (hed : e ≠ d)
    (hd : Disjoint (WilsonSlabLocalComparison.affected n e.1 e.2)
      (WilsonSlabLocalComparison.affected n d.1 d.2)) (u : Slice n) (M : ℝ)
    (hlocal : |mixedLog n β j e d q r u| ≤ M) :
    |boundaryRatio n β j e d q r u| ≤
      Real.exp M * |mixedLog n β j e d q r u| := by
  rw [boundaryRatio_eq_exp n β j e d q r hed hd]
  exact exp_increment _ M hlocal

end
end UnifiedTheory.Clay.YangMills.WilsonBoundaryDecayBudget
