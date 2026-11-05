/- Quantitative finite Taylor jets of Schwartz tests and integrated contact remainders.
The analytic bounds use explicit displacement and total-variation estimates.
They do not assert that a full Wilson covariance has finite range. -/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SchwartzDiagonalTaylor
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine directional Taylor jet, including its constant term. -/
def jet (f : SchwartzMap E ℂ) (n : ℕ) (x h : E) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), (j.factorial : ℝ)⁻¹ •
    iteratedFDeriv ℝ j f x (fun _ => h)

/-- Restriction to the actual affine line, with no derivative premise supplied. -/
theorem iteratedDeriv_line (f : SchwartzMap E ℂ) (n : ℕ) (x h : E) (t : ℝ) :
    iteratedDeriv n (fun s : ℝ => f (x + s • h)) t =
      iteratedFDeriv ℝ n f (x + t • h) (fun _ => h) := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight h
  have hf : ContDiff ℝ n (fun y : E => f (x + y)) :=
    (f.smooth n).comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ n ((fun y : E => f (x + y)) ∘ L) t (fun _ => 1) = _
  rw [L.iteratedFDeriv_comp_right hf t le_rfl, iteratedFDeriv_comp_add_left,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [L, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul]

theorem line_taylor_eq_jet (f : SchwartzMap E ℂ) (n : ℕ) (x h : E) :
    taylorWithinEval (fun s : ℝ => f (x + s • h)) n (Icc 0 1) 0 1 = jet f n x h := by
  rw [taylor_within_apply]
  unfold jet
  apply Finset.sum_congr rfl
  intro j _
  have hf : ContDiff ℝ j (fun s : ℝ => f (x + s • h)) :=
    (f.smooth j).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    hf.contDiffAt (by norm_num), iteratedDeriv_line]
  simp

/-- The Schwartz seminorm supplies an explicit all-direction Taylor remainder. -/
theorem norm_sub_jet_le (f : SchwartzMap E ℂ) (n : ℕ) (x h : E) :
    ‖f (x + h) - jet f n x h‖ ≤
      SchwartzMap.seminorm ℝ 0 (n + 1) f * ‖h‖ ^ (n + 1) / n.factorial := by
  have hf : ContDiff ℝ (n + 1 : ℕ) (fun s : ℝ => f (x + s • h)) :=
    (f.smooth (n + 1 : ℕ)).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin (n + 1) (fun s : ℝ => f (x + s • h)) (Icc 0 1) t‖ ≤
        SchwartzMap.seminorm ℝ 0 (n + 1) f * ‖h‖ ^ (n + 1) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := n + 1) (uniqueDiffOn_Icc (by norm_num))
      hf.contDiffAt ht, iteratedDeriv_line]
    calc
      _ ≤ ‖iteratedFDeriv ℝ (n + 1) f (x + t • h)‖ * ∏ _ : Fin (n + 1), ‖h‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ SchwartzMap.seminorm ℝ 0 (n + 1) f * ‖h‖ ^ (n + 1) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_right
          (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f (n + 1) (x + t • h))
          (by positivity)
  have ht := taylor_mean_remainder_bound (by norm_num : (0 : ℝ) ≤ 1)
    hf.contDiffOn (by norm_num : (1 : ℝ) ∈ Icc 0 1) hc
  simpa only [one_smul, sub_zero, one_pow, mul_one, line_taylor_eq_jet] using ht

/-- Every jet is supported at its base point, including its zeroth-order term. -/
theorem jet_eq_zero_of_not_mem_tsupport (f : SchwartzMap E ℂ) (n : ℕ) (x h : E)
    (hx : x ∉ tsupport f) : jet f n x h = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hj : iteratedFDeriv ℝ j f x = 0 := by
    by_contra hj
    exact hx (support_iteratedFDeriv_subset j hj)
  simp only [hj, ContinuousMultilinearMap.zero_apply, smul_zero]

section Weighted
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Integrating a signed local stencil retains the quantitative Taylor error.
Only nonzero weights need satisfy the displacement bound. -/
theorem weighted_remainder_bound (μ : Measure Ω) (w : Ω → ℂ) (base disp : Ω → E)
    (hw : Integrable (fun z => ‖w z‖) μ) (f : SchwartzMap E ℂ) (n : ℕ)
    (r : ℝ) (hr : 0 ≤ r) (hdisp : ∀ z, w z ≠ 0 → ‖disp z‖ ≤ r) :
    ‖∫ z, w z * (f (base z + disp z) - jet f n (base z) (disp z)) ∂μ‖ ≤
      (SchwartzMap.seminorm ℝ 0 (n + 1) f * r ^ (n + 1) / n.factorial) *
        ∫ z, ‖w z‖ ∂μ := by
  let C := SchwartzMap.seminorm ℝ 0 (n + 1) f * r ^ (n + 1) / n.factorial
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp (z : Ω) : ‖w z * (f (base z + disp z) - jet f n (base z) (disp z))‖ ≤
      C * ‖w z‖ := by
    by_cases hz : w z = 0
    · simp only [hz, zero_mul, norm_zero, mul_zero, le_refl]
    have he : ‖f (base z + disp z) - jet f n (base z) (disp z)‖ ≤ C := by
      apply (norm_sub_jet_le f n (base z) (disp z)).trans
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hdisp z hz) (n + 1))
          (apply_nonneg _ _)) (Nat.cast_nonneg _)
    rw [norm_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left he (norm_nonneg (w z))
  have h := norm_integral_le_of_norm_le (hw.const_mul C) (Eventually.of_forall hp)
  rw [integral_const_mul] at h
  exact h

/-- Exact subtraction of a variable-coefficient finite jet under an integrable stencil. -/
theorem subtraction_bound (μ : Measure Ω) (w : Ω → ℂ) (base disp : Ω → E)
    (hw : Integrable (fun z => ‖w z‖) μ) (f : SchwartzMap E ℂ) (n : ℕ)
    (hF : Integrable (fun z => w z * f (base z + disp z)) μ)
    (hJ : Integrable (fun z => w z * jet f n (base z) (disp z)) μ)
    (r : ℝ) (hr : 0 ≤ r) (hdisp : ∀ z, w z ≠ 0 → ‖disp z‖ ≤ r) :
    ‖(∫ z, w z * f (base z + disp z) ∂μ) -
      (∫ z, w z * jet f n (base z) (disp z) ∂μ)‖ ≤
      (SchwartzMap.seminorm ℝ 0 (n + 1) f * r ^ (n + 1) / n.factorial) *
        ∫ z, ‖w z‖ ∂μ := by
  rw [← integral_sub hF hJ]
  simpa only [mul_sub] using weighted_remainder_bound μ w base disp hw f n r hr hdisp

/-- Degree-four diagonal subtraction turns an a^-4 total-variation mass into an O(a) remainder. -/
theorem fourth_order_subtraction_bound (μ : Measure Ω) (w : Ω → ℂ) (base disp : Ω → E)
    (hw : Integrable (fun z => ‖w z‖) μ) (f : SchwartzMap E ℂ)
    (hF : Integrable (fun z => w z * f (base z + disp z)) μ)
    (hJ : Integrable (fun z => w z * jet f 4 (base z) (disp z)) μ)
    (a C M : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (hdisp : ∀ z, w z ≠ 0 → ‖disp z‖ ≤ C * a)
    (hmass : (∫ z, ‖w z‖ ∂μ) ≤ M / a ^ 4) :
    ‖(∫ z, w z * f (base z + disp z) ∂μ) -
      (∫ z, w z * jet f 4 (base z) (disp z) ∂μ)‖ ≤
      (M * C ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 f * a := by
  have h := subtraction_bound μ w base disp hw f 4 hF hJ (C * a) (by positivity) hdisp
  norm_num at h
  apply h.trans
  calc
    _ ≤ (SchwartzMap.seminorm ℝ 0 5 f * (C * a) ^ 5 / 24) * (M / a ^ 4) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by field_simp [ha.ne']

end Weighted

end
end UnifiedTheory.Clay.YangMills.SchwartzDiagonalTaylor
