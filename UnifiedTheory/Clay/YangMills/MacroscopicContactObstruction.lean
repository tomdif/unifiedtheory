/- Formalized macroscopic rank-one positive-semidefinite kernel counterexample
for diagonal contact subtraction. On a fixed closed ball of radius R in R^4,
the kernel K_a(x, y) = a^(-8) 1_B(x) 1_B(y) is measurable, symmetric, positive
semidefinite, bounded by 1 / a^8, and strictly vanishes for |x - y| > 2R. Yet
on any diagonal-disjoint Schwartz product tensor f ⊗ g, the degree-four
diagonal contact subtraction vanishes identically while the contact-subtracted
pairing equals a^(-8) (∫_B f) (∫_B g), diverging to +∞ as a → 0+ whenever both
ball integrals are positive. This proves that macroscopic coarse stages require
genuine decay or cancellation properties beyond positivity, amplitude bounds,
and diagonal contact subtraction alone. -/
import UnifiedTheory.Clay.YangMills.FiniteRangeSchwartzContact
import UnifiedTheory.Clay.YangMills.SchwartzProductTensor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.MacroscopicContactObstruction
noncomputable section
open MeasureTheory Filter LocalFields FiniteRangeSchwartzContact SchwartzProductTensor
open scoped Topology

local instance pairVolumeHaar :
    (volume : Measure (Spacetime × Spacetime)).IsAddHaarMeasure := by
  change (volume.prod volume).IsAddHaarMeasure
  infer_instance

/-- Indicator function of the closed ball of radius R centered at the origin in R^4. -/
def boxIndicator (R : ℝ) (x : Spacetime) : ℝ :=
  (Metric.closedBall (0 : Spacetime) R).indicator (fun _ => 1) x

/-- Rank-one macroscopic kernel K_a(x, y) = a^(-8) 1_{B_R}(x) 1_{B_R}(y). -/
def boxKernel (a R : ℝ) (z : Spacetime × Spacetime) : ℝ :=
  (a ^ 8)⁻¹ * boxIndicator R z.1 * boxIndicator R z.2

theorem boxIndicator_measurable (R : ℝ) : Measurable (boxIndicator R) :=
  measurable_const.indicator measurableSet_closedBall

theorem boxKernel_measurable (a R : ℝ) : Measurable (boxKernel a R) :=
  (measurable_const.mul ((boxIndicator_measurable R).comp measurable_fst)).mul
    ((boxIndicator_measurable R).comp measurable_snd)

theorem boxKernel_symm (a R : ℝ) (x y : Spacetime) :
    boxKernel a R (x, y) = boxKernel a R (y, x) := by
  unfold boxKernel
  ring

theorem boxIndicator_bounds (R : ℝ) (x : Spacetime) :
    0 ≤ boxIndicator R x ∧ boxIndicator R x ≤ 1 := by
  by_cases hx : x ∈ Metric.closedBall (0 : Spacetime) R <;>
    simp [boxIndicator, hx]

theorem boxIndicator_abs_le (R : ℝ) (x : Spacetime) : |boxIndicator R x| ≤ 1 := by
  rw [abs_of_nonneg (boxIndicator_bounds R x).1]
  exact (boxIndicator_bounds R x).2

theorem boxKernel_nonneg (a R : ℝ) (z : Spacetime × Spacetime) :
    0 ≤ boxKernel a R z := by
  unfold boxKernel
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (by positivity)) (boxIndicator_bounds R z.1).1)
    (boxIndicator_bounds R z.2).1

/-- The macroscopic rank-one kernel satisfies the standard B / a^8 amplitude bound with B = 1. -/
theorem boxKernel_abs_le (a R : ℝ) (z : Spacetime × Spacetime) :
    |boxKernel a R z| ≤ 1 / a ^ 8 := by
  rw [abs_of_nonneg (boxKernel_nonneg a R z)]
  unfold boxKernel
  have h1 := (boxIndicator_bounds R z.1).1
  have h2 := (boxIndicator_bounds R z.1).2
  have h3 := (boxIndicator_bounds R z.2).1
  have h4 := (boxIndicator_bounds R z.2).2
  have ha : 0 ≤ (a ^ 8)⁻¹ := inv_nonneg.mpr (by positivity)
  calc
    (a ^ 8)⁻¹ * boxIndicator R z.1 * boxIndicator R z.2
      ≤ (a ^ 8)⁻¹ * 1 * 1 := by gcongr
    _ = 1 / a ^ 8 := by ring

/-- The macroscopic kernel has finite physical range 2R. -/
theorem boxKernel_zero_of_far (a R : ℝ) (z : Spacetime × Spacetime)
    (hfar : 2 * R < ‖z.1 - z.2‖) : boxKernel a R z = 0 := by
  by_cases hz1 : z.1 ∈ Metric.closedBall (0 : Spacetime) R
  · by_cases hz2 : z.2 ∈ Metric.closedBall (0 : Spacetime) R
    · have hn1 : ‖z.1‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz1
      have hn2 : ‖z.2‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz2
      have hle : ‖z.1 - z.2‖ ≤ 2 * R := by
        calc
          ‖z.1 - z.2‖ ≤ ‖z.1‖ + ‖z.2‖ := norm_sub_le z.1 z.2
          _ ≤ R + R := add_le_add hn1 hn2
          _ = 2 * R := by ring
      linarith
    · simp [boxKernel, boxIndicator, Set.indicator_of_notMem hz2]
  · simp [boxKernel, boxIndicator, Set.indicator_of_notMem hz1]

/-- Real integral of a function over the closed ball of radius R. -/
def boxFunctional (R : ℝ) (f : Spacetime → ℝ) : ℝ :=
  ∫ x : Spacetime, boxIndicator R x * f x

/-- Complex integral of a Schwartz test function over the closed ball of radius R. -/
def boxComplexFunctional (R : ℝ) (f : TestFunction) : ℂ :=
  ∫ x : Spacetime, (boxIndicator R x : ℂ) * f x

theorem boxIndicator_mul_integrable (R : ℝ) (f : TestFunction) :
    Integrable (fun x : Spacetime => (boxIndicator R x : ℂ) * f x) := by
  apply SchwartzWeightedTail.bounded_mul_integrable volume
    (fun x : Spacetime => (boxIndicator R x : ℂ))
    (Complex.continuous_ofReal.measurable.comp (boxIndicator_measurable R)).aestronglyMeasurable
    1 (by norm_num) _ f
  intro x
  simpa only [Complex.norm_real, Real.norm_eq_abs] using boxIndicator_abs_le R x

theorem boxComplexFunctional_real (R : ℝ) (f : TestFunction) (hf : ∀ x, (f x).im = 0) :
    boxComplexFunctional R f = (boxFunctional R (fun x => (f x).re) : ℂ) := by
  unfold boxComplexFunctional boxFunctional
  have he (x : Spacetime) :
      (boxIndicator R x : ℂ) * f x = ((boxIndicator R x * (f x).re : ℝ) : ℂ) := by
    have hfx : f x = ((f x).re : ℂ) := Complex.ext rfl (hf x)
    nth_rw 1 [hfx]
    rw [← Complex.ofReal_mul]
  simp_rw [he]
  exact integral_ofReal

/-- Exact rank-one factorization of the macroscopic kernel pairing on Schwartz product tensors. -/
theorem boxKernel_tensor_pairing (a R : ℝ) (f g : TestFunction) :
    (∫ z : Spacetime × Spacetime, (boxKernel a R z : ℂ) * tensor f g z) =
      ((a ^ 8)⁻¹ : ℂ) * (boxComplexFunctional R f * boxComplexFunctional R g) := by
  have hi := boxIndicator_mul_integrable R f
  have hj := boxIndicator_mul_integrable R g
  have he (z : Spacetime × Spacetime) :
      (boxKernel a R z : ℂ) * tensor f g z =
        ((a ^ 8)⁻¹ : ℂ) * (((boxIndicator R z.1 : ℂ) * f z.1) *
          ((boxIndicator R z.2 : ℂ) * g z.2)) := by
    unfold boxKernel
    rw [tensor_apply]
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  change (∫ z : Spacetime × Spacetime,
    ((boxIndicator R z.1 : ℂ) * f z.1) * ((boxIndicator R z.2 : ℂ) * g z.2)
    ∂volume.prod volume) = boxComplexFunctional R f * boxComplexFunctional R g
  rw [integral_prod _ (hi.mul_prod hj)]
  simp_rw [integral_const_mul, integral_mul_const]
  rfl

/-- Real rank-one factorization of the macroscopic kernel pairing on real Schwartz tests. -/
theorem boxKernel_real_tensor_pairing (a R : ℝ) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    (∫ z : Spacetime × Spacetime, (boxKernel a R z : ℂ) * tensor f g z) =
      (((a ^ 8)⁻¹ * (boxFunctional R (fun x => (f x).re) *
        boxFunctional R (fun y => (g y).re)) : ℝ) : ℂ) := by
  rw [boxKernel_tensor_pairing, boxComplexFunctional_real R f hf,
    boxComplexFunctional_real R g hg]
  push_cast
  rfl

/-- Positive semidefiniteness of the macroscopic kernel on real Schwartz tests. -/
theorem boxKernel_positive_semidefinite (a R : ℝ) (f : TestFunction)
    (hf : ∀ x, (f x).im = 0) :
    0 ≤ (∫ z : Spacetime × Spacetime, (boxKernel a R z : ℂ) * tensor f f z).re := by
  rw [boxKernel_real_tensor_pairing a R f f hf hf, Complex.ofReal_re]
  exact mul_nonneg (inv_nonneg.mpr (by positivity)) (mul_self_nonneg _)

/-- On any diagonal-disjoint Schwartz tensor, the contact subtraction vanishes identically,
leaving the full macroscopic rank-one pairing intact. -/
theorem boxKernel_repaired_eq_pairing_of_disjoint (a R R₀ c : ℝ) (f g : TestFunction)
    (hdiag : ∀ x : Spacetime, (x, x) ∉ tsupport (tensor f g)) :
    (∫ z : Spacetime × Spacetime, (boxKernel a R z : ℂ) * tensor f g z) -
      contact (boxKernel a R) a R₀ c (tensor f g) =
      ((a ^ 8)⁻¹ : ℂ) * (boxComplexFunctional R f * boxComplexFunctional R g) := by
  rw [contact_diagonal_support (boxKernel a R) a R₀ c (tensor f g) hdiag, sub_zero,
    boxKernel_tensor_pairing]

/-- As the lattice spacing a → 0+, the contact-repaired macroscopic kernel pairing on any
diagonal-disjoint real Schwartz tensor with positive ball integrals diverges to +∞. -/
theorem boxKernel_repaired_tendsto_atTop {ι : Type*} (l : Filter ι)
    (a R₀ c : ι → ℝ) (R : ℝ) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0)
    (hdiag : ∀ x : Spacetime, (x, x) ∉ tsupport (tensor f g))
    (hf_pos : 0 < boxFunctional R (fun x => (f x).re))
    (hg_pos : 0 < boxFunctional R (fun y => (g y).re))
    (ha : ∀ᶠ k in l, 0 < a k) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun k =>
      ((∫ z : Spacetime × Spacetime, (boxKernel (a k) R z : ℂ) * tensor f g z) -
        contact (boxKernel (a k) R) (a k) (R₀ k) (c k) (tensor f g)).re)
      l atTop := by
  have hw : Tendsto (fun k => a k ^ 8) l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using ha0.pow 8,
      ha.mono (fun _ hk => pow_pos hk 8)⟩
  have hinv := (tendsto_inv_nhdsGT_zero.comp hw).const_mul_atTop
    (mul_pos hf_pos hg_pos)
  apply hinv.congr'
  filter_upwards with k
  rw [boxKernel_repaired_eq_pairing_of_disjoint (a k) R (R₀ k) (c k) f g hdiag,
    boxComplexFunctional_real R f hf, boxComplexFunctional_real R g hg]
  have hcast :
      (((a k) ^ 8)⁻¹ : ℂ) *
        ((boxFunctional R (fun x => (f x).re) : ℂ) *
          (boxFunctional R (fun y => (g y).re) : ℂ)) =
      ((((a k) ^ 8)⁻¹ *
        (boxFunctional R (fun x => (f x).re) *
          boxFunctional R (fun y => (g y).re)) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.ofReal_re]
  dsimp only [Function.comp_def]
  ring

/-- Consequently, the contact-repaired macroscopic kernel pairing cannot converge to zero
or to any finite limit along a nontrivial filter with a → 0+. -/
theorem boxKernel_repaired_not_tendsto_nhds {ι : Type*} (l : Filter ι) [l.NeBot]
    (a R₀ c : ι → ℝ) (R q : ℝ) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0)
    (hdiag : ∀ x : Spacetime, (x, x) ∉ tsupport (tensor f g))
    (hf_pos : 0 < boxFunctional R (fun x => (f x).re))
    (hg_pos : 0 < boxFunctional R (fun y => (g y).re))
    (ha : ∀ᶠ k in l, 0 < a k) (ha0 : Tendsto a l (𝓝 0)) :
    ¬ Tendsto (fun k =>
      ((∫ z : Spacetime × Spacetime, (boxKernel (a k) R z : ℂ) * tensor f g z) -
        contact (boxKernel (a k) R) (a k) (R₀ k) (c k) (tensor f g)).re)
      l (𝓝 q) :=
  not_tendsto_nhds_of_tendsto_atTop
    (boxKernel_repaired_tendsto_atTop l a R₀ c R f g hf hg hdiag hf_pos hg_pos ha ha0) q

end
end UnifiedTheory.Clay.YangMills.MacroscopicContactObstruction
