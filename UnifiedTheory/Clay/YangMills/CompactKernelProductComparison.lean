/- A block average controls the exterior operator norm without introducing
an exterior ground state. Only normalized reference measures factorize. -/
import UnifiedTheory.Clay.YangMills.CompactKernelWeightedSchur

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactKernelProductComparison
noncomputable section
open MeasureTheory CompactKernelOperator WilsonPositiveGroundState CompactDensityEntropy
open CompactKernelDomination

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

def productKernel (A : C(X × X, ℝ)) (B : C(Y × Y, ℝ)) :
    C((X × Y) × (X × Y), ℝ) :=
  ⟨fun z => A (z.1.1,z.2.1)*B (z.1.2,z.2.2),
    (A.continuous.comp (by fun_prop)).mul (B.continuous.comp (by fun_prop))⟩

def lift (f : C(X, ℝ)) : C(X × Y, ℝ) := ⟨fun z => f z.1, f.continuous.comp continuous_fst⟩

def average (f : C(X × Y, ℝ)) : C(X, ℝ) :=
  ⟨fun x => ∫ y, f (x, y) ∂ν, GibbsMarginalTower.fiber_integral_continuous ν f f.continuous⟩

theorem average_sq_le (f : C(X × Y, ℝ)) :
    (∫ x, (average ν f x)^2 ∂μ) ≤ ∫ z, (f z)^2 ∂μ.prod ν := by
  have hi := integral_mono (continuous_integrable μ _ ((average ν f).continuous.pow 2))
    (continuous_integrable μ _ (GibbsMarginalTower.fiber_integral_continuous ν
      (fun z => (f z)^2) (f.continuous.pow 2))) (fun x => by
        have h := integral_product_sq ν (fun y => f (x, y)) (fun _ => 1)
          (f.continuous.comp (continuous_const.prodMk continuous_id)) continuous_const
        simpa only [average, ContinuousMap.coe_mk, mul_one, one_pow, integral_const,
          probReal_univ, smul_eq_mul, one_mul] using h)
  rw [← integral_prod _ (continuous_integrable (μ.prod ν) _ (f.continuous.pow 2))] at hi
  exact hi

omit [CompactSpace X] [BorelSpace X] [CompactSpace Y] [BorelSpace Y] in
theorem lift_square (f : C(X, ℝ)) :
    (∫ z, (lift (Y := Y) f z)^2 ∂μ.prod ν) = ∫ x, (f x)^2 ∂μ := by
  change (∫ z : X × Y, (f z.1)^2 ∂μ.prod ν) = _
  rw [integral_fun_fst (fun x => (f x)^2)]
  simp only [probReal_univ, one_smul]

theorem lifted_output (A : C(X × X, ℝ)) (f : C(X × Y, ℝ)) (z : X × Y) :
    realSmoothing (μ.prod ν) (productKernel A 1) f z = realSmoothing μ A (average ν f) z.1 := by
  rw [realSmoothing_integral, realSmoothing_integral]
  change (∫ w, (A (z.1,w.1)*1)*f w ∂μ.prod ν) = _
  simp only [mul_one]
  have hi : Integrable (fun w : X × Y => A (z.1,w.1)*f w) (μ.prod ν) :=
    continuous_integrable (μ.prod ν) _
      ((A.continuous.comp (continuous_const.prodMk continuous_fst)).mul f.continuous)
  rw [integral_prod _ hi]
  simp_rw [integral_const_mul]
  rfl

theorem product_lift_output (A : C(X × X, ℝ)) (B : C(Y × Y, ℝ)) (f : C(X, ℝ))
    (z : X × Y) :
    realSmoothing (μ.prod ν) (productKernel A B) (lift f) z =
      realSmoothing μ A f z.1*realSmoothing ν B 1 z.2 := by
  rw [realSmoothing_integral, realSmoothing_integral, realSmoothing_integral]
  change (∫ w, (A (z.1,w.1)*B (z.2,w.2))*f w.1 ∂μ.prod ν) = _
  have he (w : X × Y) : (A (z.1,w.1)*B (z.2,w.2))*f w.1 =
      (A (z.1,w.1)*f w.1)*(B (z.2,w.2)*1) := by ring
  simp_rw [he]
  exact integral_prod_mul (fun x => A (z.1, x)*f x) (fun y => B (z.2, y)*1)

omit [SecondCountableTopology Y] in
theorem block_mean_sq (B : C(Y × Y, ℝ)) :
    (∫ y, realSmoothing ν B 1 y ∂ν)^2 ≤ ∫ y, (realSmoothing ν B 1 y)^2 ∂ν := by
  have h := integral_product_sq ν (realSmoothing ν B 1) (fun _ => 1)
    (realSmoothing ν B 1).continuous continuous_const
  simpa only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

variable [NormalSpace X] [NormalSpace (X × Y)] [μ.WeaklyRegular] [(μ.prod ν).WeaklyRegular]

omit [NormalSpace X] [μ.WeaklyRegular] in
/-- Adding an unused block does not increase the exterior norm. -/
theorem lifted_norm_le (A : C(X × X, ℝ)) (hA : ∀ x y, 0 ≤ A (x, y)) :
    ‖operator (μ.prod ν) (productKernel (Y := Y) A 1)‖ ≤ ‖operator μ A‖ := by
  apply norm_le_of_real_sq (μ.prod ν) _ (fun z w => by simpa only
    [productKernel, ContinuousMap.coe_mk, ContinuousMap.one_apply, mul_one] using hA z.1 w.1)
    _ (norm_nonneg _)
  intro f
  simp_rw [lifted_output]
  rw [integral_fun_fst (fun x => (realSmoothing μ A (average ν f) x)^2)]
  simp only [probReal_univ, one_smul]
  exact (real_output_sq μ A (average ν f)).trans
    (mul_le_mul_of_nonneg_left (average_sq_le μ ν f) (sq_nonneg _))

omit [NormalSpace (X × Y)] [(μ.prod ν).WeaklyRegular] in
/-- Averaging only the block leaves its mean kernel mass times the exterior
norm. This is the normalization factor needed for cancellation. -/
theorem mean_mul_norm_le (A : C(X × X, ℝ)) (hA : ∀ x y, 0 ≤ A (x, y))
    (B : C(Y × Y, ℝ)) (hq : 0 < ∫ y, realSmoothing ν B 1 y ∂ν) :
    (∫ y, realSmoothing ν B 1 y ∂ν)*‖operator μ A‖ ≤
      ‖operator (μ.prod ν) (productKernel A B)‖ := by
  let q := ∫ y, realSmoothing ν B 1 y ∂ν
  let C := ‖operator (μ.prod ν) (productKernel A B)‖
  have hc : ‖operator μ A‖ ≤ C/q := by
    apply norm_le_of_real_sq μ A hA _ (div_nonneg (norm_nonneg _) hq.le)
    intro f
    have ho := real_output_sq (μ.prod ν) (productKernel A B) (lift f)
    simp_rw [product_lift_output, mul_pow] at ho
    rw [integral_prod_mul (fun x => (realSmoothing μ A f x)^2)
      (fun y => (realSmoothing ν B 1 y)^2), lift_square] at ho
    have hb := mul_le_mul_of_nonneg_left (block_mean_sq ν B)
      (integral_nonneg (μ := μ) (fun x => sq_nonneg (realSmoothing μ A f x)))
    have hh := hb.trans ho
    change (∫ x, (realSmoothing μ A f x)^2 ∂μ)*q^2 ≤ C^2*(∫ x, (f x)^2 ∂μ) at hh
    have hd := (le_div_iff₀ (sq_pos_of_pos hq)).mpr hh
    convert hd using 1
    field_simp
    ring
  have h := (le_div_iff₀ hq).mp hc
  simpa only [mul_comm] using h

end
end UnifiedTheory.Clay.YangMills.CompactKernelProductComparison
