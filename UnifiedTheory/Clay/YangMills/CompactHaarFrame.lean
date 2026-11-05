/- A continuous family of correlated scores, with finitely many channels.
The integral-frame estimate has no channel-count loss and retains the
quadratic-form hypothesis rather than replacing it by an absolute sum. -/
import UnifiedTheory.Clay.YangMills.CompactGramResponse
import UnifiedTheory.Clay.YangMills.GibbsMarginalTower

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactHaarFrame
noncomputable section
open MeasureTheory CompactDensityEntropy

variable {I Q X : Type*} [Fintype I]
  [TopologicalSpace Q] [CompactSpace Q] [SecondCountableTopology Q]
  [MeasurableSpace Q] [BorelSpace Q]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (ν : Measure Q) (μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

def mixture (s : I → Q × X → ℝ) (a : I → C(Q, ℝ)) (x : X) : ℝ :=
  ∑ i, ∫ q, a i q * s i (q,x) ∂ν

omit μ [IsProbabilityMeasure μ] [SecondCountableTopology Q] [MeasurableSpace X]
  [BorelSpace X] in
theorem mixture_continuous (s : I → Q × X → ℝ) (hs : ∀ i, Continuous (s i))
    (a : I → C(Q, ℝ)) : Continuous (mixture ν s a) := by
  apply continuous_finset_sum
  intro i _
  exact GibbsMarginalTower.fiber_integral_continuous ν _
    (((a i).continuous.comp continuous_snd).mul ((hs i).comp continuous_swap))

def size (a : I → C(Q, ℝ)) : ℝ := ∑ i, ∫ q, (a i q)^2 ∂ν

omit μ [IsProbabilityMeasure μ] [CompactSpace Q] [SecondCountableTopology Q]
  [BorelSpace Q] [IsProbabilityMeasure ν] in
theorem size_nonneg (a : I → C(Q, ℝ)) : 0 ≤ size ν a :=
  Finset.sum_nonneg (fun i _ => integral_nonneg (fun q => sq_nonneg (a i q)))

def pairing (s : I → Q × X → ℝ) (f : X → ℝ) (i : I) (q : Q) : ℝ :=
  ∫ x, s i (q,x)*f x ∂μ

omit ν [IsProbabilityMeasure ν] [Fintype I] [MeasurableSpace Q] [BorelSpace Q]
  [SecondCountableTopology X] in
theorem pairing_continuous (s : I → Q × X → ℝ) (hs : ∀ i, Continuous (s i))
    (f : X → ℝ) (hf : Continuous f) (i : I) : Continuous (pairing μ s f i) :=
  GibbsMarginalTower.fiber_integral_continuous μ _ ((hs i).mul (hf.comp continuous_snd))

/-- Exact adjoint identity, including the integral over rotations. -/
theorem mixture_pairing (s : I → Q × X → ℝ) (hs : ∀ i, Continuous (s i))
    (a : I → C(Q, ℝ)) (f : X → ℝ) (hf : Continuous f) :
    (∫ x, mixture ν s a x * f x ∂μ) =
      ∑ i, ∫ q, a i q * pairing μ s f i q ∂ν := by
  have hi (i : I) : Continuous (fun x : X => ∫ q, a i q*s i (q,x) ∂ν) :=
    GibbsMarginalTower.fiber_integral_continuous ν _
      (((a i).continuous.comp continuous_snd).mul ((hs i).comp continuous_swap))
  simp only [mixture, Finset.sum_mul]
  rw [integral_finset_sum _ (fun i _ => continuous_integrable μ
    (fun x => (∫ q, a i q*s i (q,x) ∂ν)*f x) ((hi i).mul hf))]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [← integral_mul_const]
  have hc : Continuous (fun z : X × Q => a i z.2 * s i (z.2,z.1) * f z.1) :=
    (((a i).continuous.comp continuous_snd).mul ((hs i).comp continuous_swap)).mul
      (hf.comp continuous_fst)
  rw [integral_integral_swap (f := fun x q => a i q*s i (q,x)*f x)
    (continuous_integrable (μ.prod ν) _ hc)]
  simp only [mul_assoc, integral_const_mul, pairing]

def kernel (s : I → Q × X → ℝ) (i : I) (q : Q) (j : I) (r : Q) : ℝ :=
  ∫ x, s i (q,x)*s j (r,x) ∂μ

omit ν [IsProbabilityMeasure ν] [Fintype I] [CompactSpace Q] [SecondCountableTopology Q]
  [MeasurableSpace Q] [BorelSpace Q] [CompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [IsProbabilityMeasure μ] [TopologicalSpace Q] [TopologicalSpace X] in
theorem kernel_symm (s : I → Q × X → ℝ) (i j : I) (q r : Q) :
    kernel μ s i q j r = kernel μ s j r i q := by
  simp only [kernel, mul_comm]

theorem pairing_mixture (s : I → Q × X → ℝ) (hs : ∀ i, Continuous (s i))
    (a : I → C(Q, ℝ)) (i : I) (q : Q) :
    pairing μ s (mixture ν s a) i q =
      ∑ j, ∫ r, a j r * kernel μ s i q j r ∂ν := by
  have h := mixture_pairing ν μ s hs a (fun x => s i (q,x))
    ((hs i).comp (continuous_const.prodMk continuous_id))
  simpa only [pairing, kernel, mul_comm] using h

/-- The mixture norm is the quadratic form of the actual continuous Gram kernel. -/
theorem mixture_quadratic (s : I → Q × X → ℝ) (hs : ∀ i, Continuous (s i))
    (a : I → C(Q, ℝ)) :
    (∫ x, (mixture ν s a x)^2 ∂μ) =
      ∑ i, ∫ q, ∑ j, ∫ r, a i q*a j r*kernel μ s i q j r ∂ν ∂ν := by
  have h := mixture_pairing ν μ s hs a (mixture ν s a) (mixture_continuous ν s hs a)
  simp_rw [pairing_mixture ν μ s hs a, Finset.mul_sum, ← integral_const_mul] at h
  simpa only [pow_two, mul_assoc] using h

/-- A bound on continuous score mixtures gives the full integral Bessel bound.
There is no factor equal to the number of channels or sampled rotations. -/
theorem response_le (s : I → Q × X → ℝ) (hs : ∀ i, Continuous (s i))
    (f : X → ℝ) (hf : Continuous f) (κ : ℝ) (hκ : 0 ≤ κ)
    (hform : ∀ a : I → C(Q, ℝ), (∫ x, (mixture ν s a x)^2 ∂μ) ≤ κ * size ν a) :
    (∑ i, ∫ q, (pairing μ s (fun x => f x-∫ y, f y ∂μ) i q)^2 ∂ν) ≤
      κ * ProbabilityTheory.variance f μ := by
  let c : X → ℝ := fun x => f x-∫ y, f y ∂μ
  have hc : Continuous c := hf.sub continuous_const
  let a : I → C(Q, ℝ) := fun i => ⟨pairing μ s c i, pairing_continuous μ s hs c hc i⟩
  have he : (∫ x, mixture ν s a x*c x ∂μ) = size ν a := by
    rw [mixture_pairing ν μ s hs a c hc]
    simp only [size, a, ContinuousMap.coe_mk, pow_two]
  have h := integral_product_sq μ (mixture ν s a) c (mixture_continuous ν s hs a) hc
  rw [he] at h
  have hv : (∫ x, (c x)^2 ∂μ) = ProbabilityTheory.variance f μ := by
    rw [ProbabilityTheory.variance_eq_integral hf.measurable.aemeasurable]
  rw [hv] at h
  have hvar : 0 ≤ ProbabilityTheory.variance f μ := by
    rw [← hv]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hh := h.trans (mul_le_mul_of_nonneg_right (hform a) hvar)
  have hsize := size_nonneg ν a
  change size ν a ≤ κ * ProbabilityTheory.variance f μ
  by_cases hz : size ν a = 0
  · rw [hz]
    exact mul_nonneg hκ hvar
  · have hp : 0 < size ν a := lt_of_le_of_ne hsize (Ne.symm hz)
    nlinarith

end
end UnifiedTheory.Clay.YangMills.CompactHaarFrame
