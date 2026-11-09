/- The positive contact majorant cannot vanish when an included stage reaches a
fixed physical radius. This is a limitation of that estimator, not a no-go theorem
for Yang--Mills. A weighted-displacement bound states the stronger estimate that
can replace the crude amplitude-times-volume argument. -/
import UnifiedTheory.Clay.YangMills.GrowingStageContact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ContactScaleBarrier
noncomputable section
open MeasureTheory Filter SchwartzDiagonalTaylor
open scoped Topology

/-- The fourth-order geometric cost in physical-radius variables. -/
theorem fourth_factor_eq (a R c : ℝ) (ha : a ≠ 0) :
    a * R ^ 4 * c ^ 9 = R ^ 4 * (a * c) ^ 9 / a ^ 8 := by
  field_simp

/-- Every fixed Taylor order has the same inverse-eighth-power cutoff cost
when the physical displacement a*c is held fixed. -/
theorem order_factor_eq (N : ℕ) (a c : ℝ) (ha : a ≠ 0) :
    (c ^ 4 / a ^ 4) * (c * a) ^ (N + 1) = (a * c) ^ (N + 5) / a ^ 8 := by
  rw [show N + 5 = (N + 1) + 4 by omega, pow_add]
  field_simp
  ring

/-- A nontrivial physical pair ball and an included macroscopic radius force a large cost. -/
theorem stage_factor_lower (a R c R₀ ell : ℝ) (ha : 0 < a)
    (hR₀ : 0 < R₀) (hell : 0 < ell) (hR : R₀ ≤ R) (hc : ell ≤ a * c) :
    R₀ ^ 4 * ell ^ 9 / a ^ 8 ≤ a * R ^ 4 * c ^ 9 := by
  rw [fourth_factor_eq a R c ha.ne']
  apply div_le_div_of_nonneg_right _ (pow_nonneg ha.le 8)
  exact mul_le_mul (pow_le_pow_left₀ hR₀.le hR 4) (pow_le_pow_left₀ hell.le hc 9)
    (pow_nonneg hell.le 9) (pow_nonneg (hR₀.le.trans hR) 4)

/-- One macroscopic included stage suffices; adding nonnegative stage costs cannot help. -/
theorem accumulated_factor_lower (J j : ℕ) (a R : ℝ) (c : ℕ → ℝ)
    (R₀ ell : ℝ) (ha : 0 < a) (hR₀ : 0 < R₀) (hell : 0 < ell)
    (hR : R₀ ≤ R) (hj : j < J) (hc : ∀ i < J, 0 ≤ c i) (hphys : ell ≤ a * c j) :
    R₀ ^ 4 * ell ^ 9 / a ^ 8 ≤ a * R ^ 4 * ∑ i ∈ Finset.range J, c i ^ 9 := by
  apply (stage_factor_lower a R (c j) R₀ ell ha hR₀ hell hR hphys).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg ha.le (pow_nonneg (hR₀.le.trans hR) 4))
  exact Finset.single_le_sum (fun i hi => pow_nonneg (hc i (Finset.mem_range.mp hi)) 9)
    (Finset.mem_range.mpr hj)

/-- A fixed Taylor order cannot repair the crude absolute majorant at a fixed physical radius. -/
theorem fixed_order_factor_tendsto {ι : Type*} (l : Filter ι) (p : ℕ)
    (a R c : ι → ℝ) (R₀ ell : ℝ) (hR₀ : 0 < R₀) (hell : 0 < ell)
    (ha : ∀ᶠ k in l, 0 < a k) (ha0 : Tendsto a l (𝓝 0))
    (hR : ∀ᶠ k in l, R₀ ≤ R k) (hphys : ∀ᶠ k in l, ell ≤ a k * c k) :
    Tendsto (fun k => R k ^ 4 * (a k * c k) ^ p / a k ^ 8) l atTop := by
  have hw : Tendsto (fun k => a k ^ 8) l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using ha0.pow 8,
      ha.mono (fun _ hk => pow_pos hk 8)⟩
  have hl := (tendsto_inv_nhdsGT_zero.comp hw).const_mul_atTop
    (show 0 < R₀ ^ 4 * ell ^ p by positivity)
  apply tendsto_atTop_mono' l _ hl
  filter_upwards [ha, hR, hphys] with k hak hRk hpk
  change R₀ ^ 4 * ell ^ p * (a k ^ 8)⁻¹ ≤ _
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_right _ (pow_nonneg hak.le 8)
  exact mul_le_mul (pow_le_pow_left₀ hR₀.le hRk 4) (pow_le_pow_left₀ hell.le hpk p)
    (pow_nonneg hell.le p) (pow_nonneg (hR₀.le.trans hRk) 4)

/-- The precise growth hypothesis used by GrowingStageContact is incompatible
with an included stage whose physical radius stays bounded away from zero. -/
theorem accumulated_factor_tendsto {ι : Type*} (l : Filter ι)
    (J j : ι → ℕ) (a R : ι → ℝ) (c : ι → ℕ → ℝ)
    (R₀ ell : ℝ) (hR₀ : 0 < R₀) (hell : 0 < ell)
    (ha : ∀ᶠ k in l, 0 < a k) (ha0 : Tendsto a l (𝓝 0))
    (hR : ∀ᶠ k in l, R₀ ≤ R k) (hj : ∀ᶠ k in l, j k < J k)
    (hc : ∀ᶠ k in l, ∀ i < J k, 0 ≤ c k i)
    (hphys : ∀ᶠ k in l, ell ≤ a k * c k (j k)) :
    Tendsto (fun k => a k * R k ^ 4 * ∑ i ∈ Finset.range (J k), c k i ^ 9) l atTop := by
  have h := fixed_order_factor_tendsto l 9 a R (fun k => c k (j k))
    R₀ ell hR₀ hell ha ha0 hR hphys
  apply tendsto_atTop_mono' l _ h
  filter_upwards [ha, hR, hj, hc] with k hak hRk hjk hck
  rw [← fourth_factor_eq _ _ _ hak.ne']
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hak.le (pow_nonneg (hR₀.le.trans hRk) 4))
  exact Finset.single_le_sum (fun i hi => pow_nonneg (hck i (Finset.mem_range.mp hi)) 9)
    (Finset.mem_range.mpr hjk)

/-- This rejects only the vanishing-majorant route, not convergence of the actual remainder. -/
theorem accumulated_factor_not_tendsto_zero {ι : Type*} (l : Filter ι) [l.NeBot]
    (J j : ι → ℕ) (a R : ι → ℝ) (c : ι → ℕ → ℝ)
    (R₀ ell : ℝ) (hR₀ : 0 < R₀) (hell : 0 < ell)
    (ha : ∀ᶠ k in l, 0 < a k) (ha0 : Tendsto a l (𝓝 0))
    (hR : ∀ᶠ k in l, R₀ ≤ R k) (hj : ∀ᶠ k in l, j k < J k)
    (hc : ∀ᶠ k in l, ∀ i < J k, 0 ≤ c k i)
    (hphys : ∀ᶠ k in l, ell ≤ a k * c k (j k)) :
    ¬ Tendsto (fun k => a k * R k ^ 4 * ∑ i ∈ Finset.range (J k), c k i ^ 9) l (𝓝 0) :=
  not_tendsto_nhds_of_tendsto_atTop
    (accumulated_factor_tendsto l J j a R c R₀ ell hR₀ hell ha ha0 hR hj hc hphys) 0

section Weighted
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Scale-free replacement: use the actual weighted displacement moment instead
of multiplying a worst-case amplitude by the whole support volume. -/
theorem weighted_displacement_bound (μ : Measure Ω) (w : Ω → ℂ) (base disp : Ω → E)
    (f : SchwartzMap E ℂ) (N : ℕ)
    (hm : Integrable (fun z => ‖w z‖ * ‖disp z‖ ^ (N + 1)) μ) :
    ‖∫ z, w z * (f (base z + disp z) - jet f N (base z) (disp z)) ∂μ‖ ≤
      (SchwartzMap.seminorm ℝ 0 (N + 1) f / N.factorial) *
        ∫ z, ‖w z‖ * ‖disp z‖ ^ (N + 1) ∂μ := by
  let C := SchwartzMap.seminorm ℝ 0 (N + 1) f / N.factorial
  have hp (z : Ω) : ‖w z * (f (base z + disp z) - jet f N (base z) (disp z))‖ ≤
      C * (‖w z‖ * ‖disp z‖ ^ (N + 1)) := by
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_left (norm_sub_jet_le f N (base z) (disp z))
      (norm_nonneg (w z))
    convert h using 1
    dsimp [C]
    ring
  have h := norm_integral_le_of_norm_le (hm.const_mul C) (Eventually.of_forall hp)
  rw [integral_const_mul] at h
  exact h

/-- The same weighted moment controls a literal difference of two convergent integrals. -/
theorem weighted_displacement_subtraction_bound (μ : Measure Ω) (w : Ω → ℂ)
    (base disp : Ω → E) (f : SchwartzMap E ℂ) (N : ℕ)
    (hm : Integrable (fun z => ‖w z‖ * ‖disp z‖ ^ (N + 1)) μ)
    (hF : Integrable (fun z => w z * f (base z + disp z)) μ)
    (hJ : Integrable (fun z => w z * jet f N (base z) (disp z)) μ) :
    ‖(∫ z, w z * f (base z + disp z) ∂μ) -
      (∫ z, w z * jet f N (base z) (disp z) ∂μ)‖ ≤
      (SchwartzMap.seminorm ℝ 0 (N + 1) f / N.factorial) *
        ∫ z, ‖w z‖ * ‖disp z‖ ^ (N + 1) ∂μ := by
  rw [← integral_sub hF hJ]
  simpa only [mul_sub] using weighted_displacement_bound μ w base disp f N hm


/-- The actual displacement moments, rather than radius suprema, accumulate linearly. -/
theorem weighted_displacement_sum_bound (μ : Measure Ω) (J : ℕ)
    (w : ℕ → Ω → ℂ) (base disp : ℕ → Ω → E) (f : SchwartzMap E ℂ) (N : ℕ)
    (hm : ∀ j < J, Integrable (fun z => ‖w j z‖ * ‖disp j z‖ ^ (N + 1)) μ)
    (hF : ∀ j < J, Integrable (fun z => w j z * f (base j z + disp j z)) μ)
    (hJ : ∀ j < J, Integrable (fun z => w j z * jet f N (base j z) (disp j z)) μ) :
    ‖∑ j ∈ Finset.range J, ((∫ z, w j z * f (base j z + disp j z) ∂μ) -
      (∫ z, w j z * jet f N (base j z) (disp j z) ∂μ))‖ ≤
      (SchwartzMap.seminorm ℝ 0 (N + 1) f / N.factorial) *
        ∑ j ∈ Finset.range J, ∫ z, ‖w j z‖ * ‖disp j z‖ ^ (N + 1) ∂μ := by
  calc
    _ ≤ ∑ j ∈ Finset.range J, ‖(∫ z, w j z * f (base j z + disp j z) ∂μ) -
        (∫ z, w j z * jet f N (base j z) (disp j z) ∂μ)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J,
        (SchwartzMap.seminorm ℝ 0 (N + 1) f / N.factorial) *
          ∫ z, ‖w j z‖ * ‖disp j z‖ ^ (N + 1) ∂μ := by
      apply Finset.sum_le_sum
      intro j hj
      have hj := Finset.mem_range.mp hj
      exact weighted_displacement_subtraction_bound μ (w j) (base j) (disp j) f N
        (hm j hj) (hF j hj) (hJ j hj)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- A precise scale-free sufficient estimate for growing-stage contact convergence.
Establishing these actual weighted moments is a separate interacting-field obligation. -/
theorem subtraction_tendsto_of_weighted_moments {ι : Type*} (l : Filter ι)
    (μ : Measure Ω) (J : ι → ℕ) (w : ι → ℕ → Ω → ℂ)
    (base disp : ι → ℕ → Ω → E) (f : SchwartzMap E ℂ) (N : ℕ)
    (hm : ∀ k, ∀ j < J k, Integrable (fun z => ‖w k j z‖ * ‖disp k j z‖ ^ (N + 1)) μ)
    (hF : ∀ k, ∀ j < J k, Integrable (fun z => w k j z * f (base k j z + disp k j z)) μ)
    (hJ : ∀ k, ∀ j < J k,
      Integrable (fun z => w k j z * jet f N (base k j z) (disp k j z)) μ)
    (hsmall : Tendsto (fun k => ∑ j ∈ Finset.range (J k),
      ∫ z, ‖w k j z‖ * ‖disp k j z‖ ^ (N + 1) ∂μ) l (𝓝 0)) :
    Tendsto (fun k => ∑ j ∈ Finset.range (J k),
      ((∫ z, w k j z * f (base k j z + disp k j z) ∂μ) -
        (∫ z, w k j z * jet f N (base k j z) (disp k j z) ∂μ))) l (𝓝 0) := by
  apply squeeze_zero_norm (fun k => weighted_displacement_sum_bound μ (J k)
    (w k) (base k) (disp k) f N (hm k) (hF k) (hJ k))
  simpa only [mul_zero] using
    hsmall.const_mul (SchwartzMap.seminorm ℝ 0 (N + 1) f / N.factorial)

end Weighted
end
end UnifiedTheory.Clay.YangMills.ContactScaleBarrier
