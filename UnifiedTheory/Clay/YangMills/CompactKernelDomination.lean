/- Pointwise kernel domination gives actual L2 operator domination.
The estimates are derived on continuous inputs and extended by density. -/
import UnifiedTheory.Clay.YangMills.WilsonPositiveGroundState

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactKernelDomination
noncomputable section
open MeasureTheory CompactKernelOperator WilsonPositiveGroundState
open scoped ENNReal InnerProductSpace

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem embedding_le (f : C(X, ℂ)) (g : C(X, ℝ)) (h : ∀ x, ‖f x‖ ≤ g x) :
    ‖ContinuousMap.toLp 2 μ ℂ f‖ ≤ ‖ContinuousMap.toLp 2 μ ℂ (complexify g)‖ := by
  have hi := integral_mono
    ((f.continuous.norm.pow 2).integrable_of_hasCompactSupport (μ := μ)
      (HasCompactSupport.of_compactSpace _))
    ((g.continuous.pow 2).integrable_of_hasCompactSupport (μ := μ)
      (HasCompactSupport.of_compactSpace _))
    (fun x => pow_le_pow_left₀ (norm_nonneg _) (h x) 2)
  rw [← embedding_norm_sq, ← real_embedding_norm_sq] at hi
  nlinarith [norm_nonneg (ContinuousMap.toLp 2 μ ℂ f),
    norm_nonneg (ContinuousMap.toLp 2 μ ℂ (complexify g))]

theorem real_output_sq (K : C(X × X, ℝ)) (f : C(X, ℝ)) :
    (∫ x, (realSmoothing μ K f x)^2 ∂μ) ≤
      ‖operator μ K‖^2*(∫ x, (f x)^2 ∂μ) := by
  rw [← real_embedding_norm_sq, complexify_realSmoothing, ← real_embedding_norm_sq]
  have h := pow_le_pow_left₀ (norm_nonneg _)
    ((operator μ K).le_opNorm (ContinuousMap.toLp 2 μ ℂ (complexify f))) 2
  simpa only [mul_pow] using h

/-- This also applies to an individual input vanishing outside a region. -/
theorem input_domination (K L : C(X × X, ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (f : C(X, ℂ))
    (h : ∀ x y, ‖(K (x, y) : ℂ) * f y‖ ≤ c * L (x, y) * ‖f y‖) :
    ‖operator μ K (ContinuousMap.toLp 2 μ ℂ f)‖ ≤
      c*‖operator μ L‖*‖ContinuousMap.toLp 2 μ ℂ f‖ := by
  let g := c • realSmoothing μ L (modulus f)
  have hp (x : X) : ‖smoothing μ K (ContinuousMap.toLp 2 μ ℂ f) x‖ ≤ g x := by
    rw [smoothing_continuous_input]
    have hi := integral_mono
      (((Complex.continuous_ofReal.comp (K.continuous.comp
        (continuous_const.prodMk continuous_id))).mul f.continuous).norm
        |>.integrable_of_hasCompactSupport
        (μ := μ)
        (HasCompactSupport.of_compactSpace _))
      (((continuous_const.mul (L.continuous.comp (continuous_const.prodMk continuous_id))).mul
        f.continuous.norm).integrable_of_hasCompactSupport
        (μ := μ)
      (HasCompactSupport.of_compactSpace _))
      (h x)
    apply (norm_integral_le_integral_norm _).trans
    apply hi.trans_eq
    change (∫ y, c * L (x, y) * ‖f y‖ ∂μ) = c*realSmoothing μ L (modulus f) x
    rw [realSmoothing_integral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    change c * L (x, y) * ‖f y‖ = c*(L (x, y) * ‖f y‖)
    ring
  have hn := embedding_le μ _ g hp
  change ‖operator μ K (ContinuousMap.toLp 2 μ ℂ f)‖ ≤ _ at hn
  have hg : ‖ContinuousMap.toLp 2 μ ℂ (complexify g)‖ =
      c*‖operator μ L (ContinuousMap.toLp 2 μ ℂ (complexify (modulus f)))‖ := by
    simp only [g, complexify_smul, map_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hc, complexify_realSmoothing]
    rfl
  rw [hg] at hn
  have ho := mul_le_mul_of_nonneg_left
    ((operator μ L).le_opNorm (ContinuousMap.toLp 2 μ ℂ (complexify (modulus f)))) hc
  rw [modulus_embedding_norm] at ho
  exact hn.trans (by simpa only [mul_assoc] using ho)

variable [NormalSpace X] [μ.WeaklyRegular]

theorem norm_le_of_continuous (K : C(X × X, ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ f : C(X, ℂ), ‖operator μ K (ContinuousMap.toLp 2 μ ℂ f)‖ ≤
      c*‖ContinuousMap.toLp 2 μ ℂ f‖) : ‖operator μ K‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro f
  apply (ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).induction_on
    (p := fun f => ‖operator μ K f‖ ≤ c*‖f‖)
  · exact isClosed_le (operator μ K).continuous.norm (continuous_const.mul continuous_norm)
  · exact h

/-- No operator-positivity premise is needed: positivity is pointwise. -/
theorem norm_domination (K L : C(X × X, ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x y, |K (x, y)| ≤ c * L (x, y)) :
    ‖operator μ K‖ ≤ c*‖operator μ L‖ := by
  apply norm_le_of_continuous μ K _ (mul_nonneg hc (norm_nonneg _))
  intro f
  exact input_domination μ K L c hc f (fun x y => by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc] using
      mul_le_mul_of_nonneg_right (h x y) (norm_nonneg (f y)))

/-- A real-input L2 bound suffices to control the actual complex operator. -/
theorem norm_le_of_real_sq (K : C(X × X, ℝ)) (hK : ∀ x y, 0 ≤ K (x, y))
    (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ f : C(X, ℝ), (∫ x, (realSmoothing μ K f x)^2 ∂μ) ≤
      c^2*(∫ x, (f x)^2 ∂μ)) : ‖operator μ K‖ ≤ c := by
  apply norm_le_of_continuous μ K c hc
  intro f
  have hp (x : X) : ‖smoothing μ K (ContinuousMap.toLp 2 μ ℂ f) x‖ ≤
      realSmoothing μ K (modulus f) x := by
    rw [smoothing_continuous_input, realSmoothing_integral]
    have ht := norm_integral_le_integral_norm (fun y => (K (x, y) : ℂ) * f y) (μ := μ)
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK x _),
      modulus, ContinuousMap.coe_mk] using ht
  have hn := embedding_le μ _ _ hp
  have hs := h (modulus f)
  rw [← real_embedding_norm_sq, ← real_embedding_norm_sq, modulus_embedding_norm] at hs
  have hh : ‖ContinuousMap.toLp 2 μ ℂ (complexify (realSmoothing μ K (modulus f)))‖ ≤
      c*‖ContinuousMap.toLp 2 μ ℂ f‖ := by
    rw [← mul_pow] at hs
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp hs
  exact hn.trans hh

end
end UnifiedTheory.Clay.YangMills.CompactKernelDomination
