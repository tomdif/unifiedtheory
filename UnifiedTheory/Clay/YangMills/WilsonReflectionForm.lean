/- Integral positivity for finite-feature and Wilson crossing kernels on compact
configuration spaces. The reflection here swaps two independent copies of the
half-configuration space. Identifying this product split with the periodic lattice
and its crossing plaquettes remains a separate geometric obligation. -/
import UnifiedTheory.Clay.YangMills.WilsonCrossingKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonReflectionForm
noncomputable section
open MeasureTheory Filter WilsonCrossingKernel
open scoped Topology

variable {X D : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [Fintype D]
  (μ : Measure X) [IsFiniteMeasure μ]

def reflectionForm (K : X → X → ℝ) (f : X → ℂ) : ℂ :=
  ∫ z : X × X, star (f z.1) * (K z.1 z.2 : ℂ) * f z.2 ∂μ.prod μ

omit [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem continuous_featureKernel (φ : X → D → ℝ) (hφ : ∀ k, Continuous (fun x => φ x k)) :
    Continuous (fun z : X × X => featureKernel φ z.1 z.2) := by
  apply continuous_finset_sum
  intro k _
  exact ((hφ k).comp continuous_fst).mul ((hφ k).comp continuous_snd)

omit [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem continuous_reflectionIntegrand (K : X → X → ℝ)
    (hK : Continuous (fun z : X × X => K z.1 z.2)) (f : X → ℂ) (hf : Continuous f) :
    Continuous (fun z : X × X => star (f z.1) * (K z.1 z.2 : ℂ) * f z.2) :=
  (((continuous_star.comp hf).comp continuous_fst).mul
    (Complex.continuous_ofReal.comp hK)).mul (hf.comp continuous_snd)

/-- Finite sums of separated reflected products integrate to sums of squared moduli. -/
theorem separated_integral (ψ : D → X → ℂ) (hψ : ∀ k, Continuous (ψ k)) :
    (∫ z : X × X, ∑ k, star (ψ k z.1) * ψ k z.2 ∂μ.prod μ) =
      ∑ k, (Complex.normSq (∫ x, ψ k x ∂μ) : ℂ) := by
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_prod_mul (fun x => star (ψ k x)) (ψ k)]
    simp only [Complex.star_def, integral_conj, Complex.normSq_eq_conj_mul_self]
  · intro k _
    exact (((continuous_star.comp (hψ k)).comp continuous_fst).mul
      ((hψ k).comp continuous_snd)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

theorem reflectionForm_feature (φ : X → D → ℝ) (hφ : ∀ k, Continuous (fun x => φ x k))
    (f : X → ℂ) (hf : Continuous f) :
    reflectionForm μ (featureKernel φ) f =
      ∑ k, (Complex.normSq (∫ x, f x * (φ x k : ℂ) ∂μ) : ℂ) := by
  rw [← separated_integral μ (fun k x => f x * (φ x k : ℂ))
    (fun k => hf.mul (Complex.continuous_ofReal.comp (hφ k)))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  simp only [featureKernel, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  simp [mul_assoc, mul_left_comm, mul_comm]

theorem reflectionForm_feature_nonneg (φ : X → D → ℝ)
    (hφ : ∀ k, Continuous (fun x => φ x k)) (f : X → ℂ) (hf : Continuous f) :
    0 ≤ (reflectionForm μ (featureKernel φ) f).re ∧
      (reflectionForm μ (featureKernel φ) f).im = 0 := by
  rw [reflectionForm_feature μ φ hφ f hf]
  constructor
  · simp only [Complex.re_sum, Complex.ofReal_re]
    exact Finset.sum_nonneg (fun k _ => Complex.normSq_nonneg _)
  · simp

theorem reflectionForm_power_nonneg (φ : X → D → ℝ)
    (hφ : ∀ k, Continuous (fun x => φ x k)) (f : X → ℂ) (hf : Continuous f) (m : ℕ) :
    0 ≤ (reflectionForm μ (fun x y => featureKernel φ x y ^ m) f).re ∧
      (reflectionForm μ (fun x y => featureKernel φ x y ^ m) f).im = 0 := by
  simp only [feature_power]
  apply reflectionForm_feature_nonneg μ _ _ f hf
  intro p
  exact continuous_finset_prod _ (fun t _ => hφ (p t))

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [BorelSpace X] [IsFiniteMeasure μ] in
theorem reflectionForm_scale (K : X → X → ℝ) (f : X → ℂ) (a : ℝ) :
    reflectionForm μ (fun x y => a * K x y) f = (a : ℂ) * reflectionForm μ K f := by
  unfold reflectionForm
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  push_cast
  ring

theorem reflectionForm_sum {J : Type*} (s : Finset J) (K : J → X → X → ℝ)
    (hK : ∀ j ∈ s, Continuous (fun z : X × X => K j z.1 z.2))
    (f : X → ℂ) (hf : Continuous f) :
    reflectionForm μ (fun x y => ∑ j ∈ s, K j x y) f =
      ∑ j ∈ s, reflectionForm μ (K j) f := by
  unfold reflectionForm
  simp only [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  apply integral_finset_sum
  intro j hj
  exact (continuous_reflectionIntegrand (K j) (hK j hj) f hf).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def expPolynomial (N : ℕ) (t : ℝ) : ℝ := ∑ m ∈ Finset.range N, t ^ m / (m.factorial : ℝ)

theorem continuous_expPolynomial (N : ℕ) : Continuous (expPolynomial N) := by
  apply continuous_finset_sum
  intro m _
  exact (continuous_id.pow m).div_const _

theorem expPolynomial_tendsto (t : ℝ) :
    Tendsto (fun N => expPolynomial N t) atTop (𝓝 (Real.exp t)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp t).tendsto_sum_nat
  rwa [← Real.exp_eq_exp_ℝ] at h

theorem expPolynomial_norm_le (N : ℕ) (t : ℝ) : ‖expPolynomial N t‖ ≤ Real.exp ‖t‖ := by
  calc
    ‖expPolynomial N t‖ ≤ ∑ m ∈ Finset.range N, ‖t ^ m / (m.factorial : ℝ)‖ := norm_sum_le _ _
    _ = ∑ m ∈ Finset.range N, ‖t‖ ^ m / (m.factorial : ℝ) := by
      simp only [norm_div, norm_pow, Real.norm_natCast]
    _ ≤ Real.exp ‖t‖ := Real.sum_le_exp_of_nonneg (norm_nonneg _) N

theorem reflectionForm_expPolynomial_nonneg (φ : X → D → ℝ)
    (hφ : ∀ k, Continuous (fun x => φ x k)) (f : X → ℂ) (hf : Continuous f)
    (β : ℝ) (hβ : 0 ≤ β) (N : ℕ) :
    0 ≤ (reflectionForm μ (fun x y => expPolynomial N (β * featureKernel φ x y)) f).re ∧
      (reflectionForm μ (fun x y => expPolynomial N (β * featureKernel φ x y)) f).im = 0 := by
  have hrewrite (x y : X) : expPolynomial N (β * featureKernel φ x y) =
      ∑ m ∈ Finset.range N, (β ^ m / (m.factorial : ℝ)) * featureKernel φ x y ^ m := by
    apply Finset.sum_congr rfl
    intro m _
    rw [mul_pow]
    ring
  simp only [hrewrite]
  rw [reflectionForm_sum μ _ _ (fun m _ =>
    continuous_const.mul ((continuous_featureKernel φ hφ).pow m)) f hf]
  simp only [reflectionForm_scale, Complex.re_sum, Complex.im_sum, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  constructor
  · apply Finset.sum_nonneg
    intro m _
    exact mul_nonneg (div_nonneg (pow_nonneg hβ _) (Nat.cast_nonneg _))
      (reflectionForm_power_nonneg μ φ hφ f hf m).1
  · apply Finset.sum_eq_zero
    intro m _
    rw [(reflectionForm_power_nonneg μ φ hφ f hf m).2, mul_zero]

theorem reflectionForm_expPolynomial_tendsto (K : X → X → ℝ)
    (hK : Continuous (fun z : X × X => K z.1 z.2)) (f : X → ℂ) (hf : Continuous f) :
    Tendsto (fun N => reflectionForm μ (fun x y => expPolynomial N (K x y)) f) atTop
      (𝓝 (reflectionForm μ (fun x y => Real.exp (K x y)) f)) := by
  let B : X × X → ℝ := fun z => ‖f z.1‖ * Real.exp ‖K z.1 z.2‖ * ‖f z.2‖
  have hB : Continuous B :=
    ((hf.norm.comp continuous_fst).mul (Real.continuous_exp.comp hK.norm)).mul
      (hf.norm.comp continuous_snd)
  apply tendsto_integral_of_dominated_convergence B
  · intro N
    exact (continuous_reflectionIntegrand (fun x y => expPolynomial N (K x y))
      ((continuous_expPolynomial N).comp hK) f hf).aestronglyMeasurable
  · exact hB.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro N
    apply Filter.Eventually.of_forall
    intro z
    simp only [norm_mul, norm_star, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (expPolynomial_norm_le N (K z.1 z.2)) (norm_nonneg _))
      (norm_nonneg _)
  · apply Filter.Eventually.of_forall
    intro z
    have hz := (Complex.continuous_ofReal.tendsto _).comp (expPolynomial_tendsto (K z.1 z.2))
    exact (hz.const_mul (star (f z.1))).mul_const (f z.2)

/-- Integral reflection positivity for the full exponential crossing interaction. -/
theorem reflectionForm_exp_feature_nonneg (φ : X → D → ℝ)
    (hφ : ∀ k, Continuous (fun x => φ x k)) (f : X → ℂ) (hf : Continuous f)
    (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ (reflectionForm μ (fun x y => Real.exp (β * featureKernel φ x y)) f).re ∧
      (reflectionForm μ (fun x y => Real.exp (β * featureKernel φ x y)) f).im = 0 := by
  have ht := reflectionForm_expPolynomial_tendsto μ (fun x y => β * featureKernel φ x y)
    (continuous_const.mul (continuous_featureKernel φ hφ)) f hf
  constructor
  · apply ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp ht)
    exact Filter.Eventually.of_forall (fun N =>
      (reflectionForm_expPolynomial_nonneg μ φ hφ f hf β hβ N).1)
  · have heq (N : ℕ) := (reflectionForm_expPolynomial_nonneg μ φ hφ f hf β hβ N).2
    have hz : Tendsto (fun N =>
        (reflectionForm μ (fun x y => expPolynomial N (β * featureKernel φ x y)) f).im)
        atTop (𝓝 0) := by
      simpa only [heq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique (Complex.continuous_im.tendsto _ |>.comp ht) hz

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [BorelSpace X] [IsFiniteMeasure μ] in
theorem reflectionForm_weights (K : X → X → ℝ) (f : X → ℂ) (w : X → ℝ) :
    reflectionForm μ (fun x y => w x * K x y * w y) f =
      reflectionForm μ K (fun x => (w x : ℂ) * f x) := by
  unfold reflectionForm
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  simp [mul_assoc, mul_left_comm, mul_comm]

/-- Independent half-actions can be absorbed into the positive-half test function. -/
theorem reflectionForm_split_nonneg (φ : X → D → ℝ)
    (hφ : ∀ k, Continuous (fun x => φ x k)) (A : X → ℝ) (hA : Continuous A)
    (f : X → ℂ) (hf : Continuous f) (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ (reflectionForm μ
      (fun x y => Real.exp (-A x - A y + β * featureKernel φ x y)) f).re ∧
      (reflectionForm μ
        (fun x y => Real.exp (-A x - A y + β * featureKernel φ x y)) f).im = 0 := by
  have heq (x y : X) : Real.exp (-A x - A y + β * featureKernel φ x y) =
      Real.exp (-A x) * Real.exp (β * featureKernel φ x y) * Real.exp (-A y) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]
    ring
  simp only [heq, reflectionForm_weights]
  exact reflectionForm_exp_feature_nonneg μ φ hφ _
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp hA.neg)).mul hf) β hβ

variable {d G : Type*} [Fintype d] [DecidableEq d] [Group G]

omit [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem continuous_unitary_features (ρ : G →* Matrix.unitaryGroup d ℂ) (h : X → G)
    (hρh : Continuous (fun x => (ρ (h x) : Matrix d d ℂ))) :
    ∀ k, Continuous (fun x => matrixFeatures (ρ (h x) : Matrix d d ℂ) k) := by
  intro k
  cases k with
  | inl p =>
    exact Complex.continuous_re.comp
      ((continuous_apply p.2).comp ((continuous_apply p.1).comp hρh))
  | inr p =>
    exact Complex.continuous_im.comp
      ((continuous_apply p.2).comp ((continuous_apply p.1).comp hρh))

/-- Wilson crossing weights give a positive integral form for every continuous test. -/
theorem unitary_crossing_reflection_nonneg (ρ : G →* Matrix.unitaryGroup d ℂ) (h : X → G)
    (hρh : Continuous (fun x => (ρ (h x) : Matrix d d ℂ)))
    (f : X → ℂ) (hf : Continuous f) (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ (reflectionForm μ (fun x y => crossingKernel ρ β (h x) (h y)) f).re ∧
      (reflectionForm μ (fun x y => crossingKernel ρ β (h x) (h y)) f).im = 0 := by
  simp only [crossingKernel_eq_exp_feature]
  exact reflectionForm_exp_feature_nonneg μ _ (continuous_unitary_features ρ h hρh) f hf β hβ

/-- Finite products of Wilson crossing plaquettes remain positive after integration. -/
theorem unitary_crossing_product_reflection_nonneg {P : Type*} [Fintype P]
    (ρ : G →* Matrix.unitaryGroup d ℂ) (h : P → X → G)
    (hρh : ∀ p, Continuous (fun x => (ρ (h p x) : Matrix d d ℂ)))
    (f : X → ℂ) (hf : Continuous f) (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ (reflectionForm μ (fun x y => ∏ p, crossingKernel ρ β (h p x) (h p y)) f).re ∧
      (reflectionForm μ (fun x y => ∏ p, crossingKernel ρ β (h p x) (h p y)) f).im = 0 := by
  let φ : X → P × ((d × d) ⊕ (d × d)) → ℝ :=
    fun x p => matrixFeatures (ρ (h p.1 x) : Matrix d d ℂ) p.2
  have heq (x y : X) : (∏ p, crossingKernel ρ β (h p x) (h p y)) =
      Real.exp (β * featureKernel φ x y) := by
    simp only [crossingKernel_eq_exp_feature, ← Real.exp_sum, ← Finset.mul_sum]
    congr 2
    simp only [featureKernel, Fintype.sum_prod_type, φ]
  simp only [heq]
  apply reflectionForm_exp_feature_nonneg μ φ _ f hf β hβ
  intro p
  exact continuous_unitary_features ρ (h p.1) (hρh p.1) p.2

end
end UnifiedTheory.Clay.YangMills.WilsonReflectionForm
