/- Actual neighboring physical-cell coefficients satisfy a volume-uniform
translation bound. The estimate uses the true floor/ZMod sampler and a proved
finite Schwartz derivative seminorm, with periodic wrapping included exactly. -/
import UnifiedTheory.Clay.YangMills.WilsonPhysicalCellWeights
import UnifiedTheory.Clay.YangMills.CellSpacetimeTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCellTranslation
noncomputable section
open MeasureTheory LocalFields PeriodicLattice4 FiniteCellSmearing
open PeriodicCellSampling CellSpacetimeTranslation PeriodicSpacetimeTranslation
open SchwartzTranslations

/-- A fixed finite derivative-seminorm budget, independent of the lattice. -/
def derivativeBudget (f : TestFunction) : ℝ :=
  2 ^ (volume : Measure Spacetime).integrablePower *
    (∫ x : Spacetime, (1 + ‖x‖) ^ (-((volume : Measure Spacetime).integrablePower : ℝ))) *
      (derivativeBound f 0 0 + derivativeBound f (volume : Measure Spacetime).integrablePower 0)

theorem derivativeBudget_nonneg (f : TestFunction) : 0 ≤ derivativeBudget f := by
  have hi : 0 ≤ ∫ x : Spacetime,
      (1 + ‖x‖) ^ (-((volume : Measure Spacetime).integrablePower : ℝ)) :=
    integral_nonneg (fun x => Real.rpow_nonneg (by positivity) _)
  have h0 := derivativeBound_nonneg f 0 0
  have hk := derivativeBound_nonneg f (volume : Measure Spacetime).integrablePower 0
  unfold derivativeBudget
  positivity

/-- The L1 translation modulus is bounded by an actual finite derivative budget. -/
theorem translation_l1_bound (f : TestFunction) (v : Spacetime) (hv : ‖v‖ ≤ 1) :
    (∫ x, ‖translationCLM v f x - f x‖) ≤ derivativeBudget f * ‖v‖ := by
  have h := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℂ
    (volume : Measure Spacetime) (translationCLM v f - f) 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero, zero_add, SchwartzMap.sub_apply] at h
  have h0 := seminorm_translation_difference f 0 0 v hv
  have hk := seminorm_translation_difference f (volume : Measure Spacetime).integrablePower 0 v hv
  have hc : 0 ≤ 2 ^ (volume : Measure Spacetime).integrablePower *
      (∫ x : Spacetime, (1 + ‖x‖) ^ (-((volume : Measure Spacetime).integrablePower : ℝ))) :=
    mul_nonneg (by positivity) (integral_nonneg (fun x => Real.rpow_nonneg (by positivity) _))
  apply h.trans
  unfold derivativeBudget
  calc
    _ ≤ _ * (derivativeBound f 0 0 * ‖v‖ +
        derivativeBound f (volume : Measure Spacetime).integrablePower 0 * ‖v‖) :=
      mul_le_mul_of_nonneg_left (add_le_add h0 hk) hc
    _ = _ := by ring

variable (n : ℕ) [NeZero n] (a : ℝ)

/-- The common spatial cell coefficient, before choosing a plaquette plane. -/
def siteWeight (f : TestFunction) (x : Vertex n) : ℝ :=
  (coefficient volume (vertexSample n a) x f).re

omit [NeZero n] in
/-- This is precisely the repository's physical plaquette weight on its chosen plane. -/
theorem weight_on_plane (plane : Plane) (f : TestFunction) (x : Vertex n) :
    WilsonPhysicalCellWeights.weight n a plane f (x, plane) = siteWeight n a f x := by
  simp [WilsonPhysicalCellWeights.weight, siteWeight, coefficient, cellFunction, sample]

theorem siteWeight_sub (f g : TestFunction) (x : Vertex n) :
    siteWeight n a (f - g) x = siteWeight n a f x - siteWeight n a g x := by
  unfold siteWeight coefficient
  have he : cellFunction (vertexSample n a) x (f - g : TestFunction) =
      fun y => cellFunction (vertexSample n a) x f y - cellFunction (vertexSample n a) x g y := by
    funext y
    by_cases hy : vertexSample n a y = x <;> simp [cellFunction, hy]
  rw [he, integral_sub
    (cellFunction_integrable volume _ (vertexSample_measurable n a) x f f.integrable)
    (cellFunction_integrable volume _ (vertexSample_measurable n a) x g g.integrable)]
  rfl

theorem siteWeight_budget (f : TestFunction) :
    (∑ x, |siteWeight n a f x|) ≤ ∫ y, ‖f y‖ :=
  FiniteCellWeightBudget.coefficient_re_budget volume _ (vertexSample_measurable n a) f f.integrable

/-- Spatial smoothness does not remove this plane-to-plane coefficient difference. -/
theorem siteWeight_difference_budget (f g : TestFunction) :
    (∑ x, |siteWeight n a f x - siteWeight n a g x|) ≤ ∫ y, ‖f y - g y‖ := by
  simpa only [siteWeight_sub, SchwartzMap.sub_apply] using siteWeight_budget n a (f - g)

omit [NeZero n] in
/-- Cell translation remains exact across every periodic seam. -/
theorem siteWeight_translation (ha : a ≠ 0) (k : Fin 4 → ℤ)
    (f : TestFunction) (x : Vertex n) :
    siteWeight n a (translationCLM (cellVector a k) f)
      (shiftVertex n (integerVertex n k) x) = siteWeight n a f x := by
  unfold siteWeight coefficient
  congr 1
  rw [← integral_add_right_eq_self
    (cellFunction (vertexSample n a) (shiftVertex n (integerVertex n k) x)
      (translationCLM (cellVector a k) f)) (cellVector a k)]
  apply integral_congr_ae
  filter_upwards with y
  change (if vertexSample n a (pointTranslate (cellVector a k) y) =
    shiftVertex n (integerVertex n k) x then f ((y + cellVector a k) - cellVector a k) else 0) = _
  rw [vertexSample_translate n a ha]
  simp [cellFunction, shiftVertex]

/-- Summed neighboring-weight variation is controlled independently of the period. -/
theorem shifted_difference_budget (ha : a ≠ 0) (k : Fin 4 → ℤ)
    (f : TestFunction) :
    (∑ x, |siteWeight n a f (shiftVertex n (integerVertex n k) x) - siteWeight n a f x|) ≤
      ∫ y, ‖translationCLM (cellVector a k) f y - f y‖ := by
  have he (x : Vertex n) :
      |siteWeight n a f (shiftVertex n (integerVertex n k) x) - siteWeight n a f x| =
      |siteWeight n a (translationCLM (cellVector a k) f - f)
        (shiftVertex n (integerVertex n k) x)| := by
    rw [siteWeight_sub, siteWeight_translation n a ha]
    exact abs_sub_comm _ _
  simp_rw [he]
  have hs := Equiv.sum_comp (vertexShiftEquiv n (integerVertex n k))
    (fun x => |siteWeight n a (translationCLM (cellVector a k) f - f) x|)
  change (∑ x, |siteWeight n a (translationCLM (cellVector a k) f - f)
    (shiftVertex n (integerVertex n k) x)|) = _ at hs
  rw [hs]
  simpa only [SchwartzMap.sub_apply] using
    siteWeight_budget n a (translationCLM (cellVector a k) f - f)

/-- A genuine first-order cell-translation gain, with no hidden support-size factor. -/
theorem shifted_derivative_budget (ha : a ≠ 0) (k : Fin 4 → ℤ)
    (f : TestFunction) (hk : ‖cellVector a k‖ ≤ 1) :
    (∑ x, |siteWeight n a f (shiftVertex n (integerVertex n k) x) - siteWeight n a f x|) ≤
      derivativeBudget f * ‖cellVector a k‖ :=
  (shifted_difference_budget n a ha k f).trans (translation_l1_bound f _ hk)

omit [NeZero n] in
/-- One negative coordinate step in physical units. -/
theorem cellVector_backward (ν : Fin 4) :
    cellVector a (Pi.single ν (-1)) = WithLp.toLp 2 (Pi.single ν (-a)) := by
  ext μ
  by_cases h : μ = ν
  · subst μ
    simp [cellVector]
  · simp [cellVector, Pi.single_apply, h]

omit [NeZero n] in
theorem integerVertex_backward (ν : Fin 4) :
    integerVertex n (Pi.single ν (-1)) = -Pi.single ν 1 := by
  funext μ
  by_cases h : μ = ν
  · subst μ
    simp [integerVertex]
  · simp [integerVertex, h]

omit [NeZero n] in
theorem cellVector_backward_norm (ν : Fin 4) :
    ‖cellVector a (Pi.single ν (-1))‖ = |a| := by
  rw [cellVector_backward, PiLp.norm_toLp_single]
  simp

/-- The actual preceding cell has a uniform O(a) total-variation budget. -/
theorem backward_difference_budget (ha : a ≠ 0) (ha₁ : |a| ≤ 1)
    (ν : Fin 4) (f : TestFunction) :
    (∑ x, |siteWeight n a f (x - Pi.single ν 1) - siteWeight n a f x|) ≤
      derivativeBudget f * |a| := by
  have h := shifted_derivative_budget n a ha (Pi.single ν (-1)) f
    (by simpa only [cellVector_backward_norm] using ha₁)
  simpa only [cellVector_backward_norm, integerVertex_backward, shiftVertex, sub_eq_add_neg] using h

end
end UnifiedTheory.Clay.YangMills.WilsonCellTranslation
