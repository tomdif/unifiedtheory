/- The heat-bath two-edge comparison from explicit conditional densities.
No domination of the singular heat-bath edge measure by a transfer edge law
is assumed. The comparison is derived by integrating two transfer legs. -/
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.HeatBathTwoEdge
noncomputable section
open MeasureTheory Set

variable {X A O : Type*}

/-- The optimized elementary two-leg square inequality. -/
theorem weighted_square (a b c t : ℝ) (ht : 0 < t) :
    (a - b) ^ 2 ≤ (1 + t) * (a - c) ^ 2 + (1 + 1 / t) * (b - c) ^ 2 := by
  apply (mul_le_mul_iff_right₀ ht).mp
  have he : ((1 + t) * (a - c) ^ 2 + (1 + 1 / t) * (b - c) ^ 2) * t -
      (a - b) ^ 2 * t = (t * (a - c) + (b - c)) ^ 2 := by
    field_simp [ht.ne']
    ring
  nlinarith [sq_nonneg (t * (a - c) + (b - c))]

section Parametric
variable [TopologicalSpace O] [LocallyCompactSpace O] [SecondCountableTopology O]
  [TopologicalSpace A] [CompactSpace A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A] (ν : Measure A) [IsProbabilityMeasure ν]

omit [SecondCountableTopology A] in
/-- Compact parameter integrals used below are genuinely continuous. -/
theorem integral_continuous (F : O × A → ℝ) (hF : Continuous F) :
    Continuous (fun r => ∫ a, F (r, a) ∂ν) := by
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ := ν)
      (f := fun r a => F (r, a)) hF isCompact_univ)
end Parametric

section Transfer
variable [TopologicalSpace X] [CompactSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Twice the one-step conditional Dirichlet contribution at x. -/
def increment (P : C(X × X, ℝ)) (f : C(X, ℝ)) (x : X) : ℝ :=
  ∫ y, P (x, y) * (f x - f y) ^ 2 ∂μ

theorem increment_continuous (P : C(X × X, ℝ)) (f : C(X, ℝ)) :
    Continuous (increment μ P f) := by
  unfold increment
  apply integral_continuous μ (fun xy => P xy * (f xy.1 - f xy.2) ^ 2)
  fun_prop

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The two-edge estimate is derived from actual row densities and their mass one. -/
theorem pointwise_two_edge (P : C(X × X, ℝ)) (f : C(X, ℝ))
    (hP : ∀ z, 0 ≤ P z) (hmass : ∀ x, (∫ y, P (x, y) ∂μ) = 1)
    (x z : X) (R t : ℝ) (ht : 0 < t)
    (hrow : ∀ y, P (x, y) ≤ R * P (z, y)) :
    (f x - f z) ^ 2 ≤ (1 + t) * increment μ P f x +
      (1 + 1 / t) * R * increment μ P f z := by
  have hi1 : Integrable (fun y => P (x, y) * (f x - f z) ^ 2) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  have hi2 : Integrable (fun y => (1 + t) * (P (x, y) * (f x - f y) ^ 2)) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  have hi3 : Integrable (fun y => ((1 + 1 / t) * R) * (P (z, y) * (f z - f y) ^ 2)) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  have hp : 0 ≤ 1 + 1 / t := by positivity
  have h := integral_mono hi1 (hi2.add hi3) (fun y => by
    change P (x, y) * (f x - f z) ^ 2 ≤
      (1 + t) * (P (x, y) * (f x - f y) ^ 2) +
        ((1 + 1 / t) * R) * (P (z, y) * (f z - f y) ^ 2)
    have hs := mul_le_mul_of_nonneg_left (weighted_square (f x) (f z) (f y) t ht) (hP (x, y))
    have hr := mul_le_mul_of_nonneg_right (hrow y) (mul_nonneg hp (sq_nonneg (f z - f y)))
    nlinarith)
  simp only [Pi.add_apply] at h
  rw [integral_mul_const, hmass, one_mul, integral_add hi2 hi3,
    integral_const_mul, integral_const_mul] at h
  exact h
end Transfer

section Conditional
variable [TopologicalSpace A] [CompactSpace A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A] (ν : Measure A) [IsProbabilityMeasure ν]

/-- The exact symmetric heat-bath pair average for one conditional density. -/
def pairAverage (p : C(A, ℝ)) (H : C(A × A, ℝ)) : ℝ :=
  ∫ ab, (p ab.1 * p ab.2 / (∫ a, p a ∂ν)) * H ab ∂ν.prod ν

omit [SecondCountableTopology A] in
theorem mass_pos (p : C(A, ℝ)) (hp : ∀ a, 0 < p a) : 0 < ∫ a, p a ∂ν := by
  apply (integral_pos_iff_support_of_nonneg (fun a => (hp a).le)
    (p.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mpr
  have he : Function.support p = univ := by
    ext a
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hp a).ne'
  simp [he]

theorem pairAverage_nested (p : C(A, ℝ)) (H : C(A × A, ℝ)) :
    pairAverage ν p H = ∫ a, ∫ b, (p a * p b / (∫ c, p c ∂ν)) * H (a, b) ∂ν ∂ν := by
  apply integral_prod
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  fun_prop

/-- Both conditional-pair marginals are exactly the original unnormalized fiber density. -/
theorem pairAverage_affine (p D : C(A, ℝ)) (hp : ∀ a, 0 < p a) (a b : ℝ) :
    pairAverage ν p
      ⟨fun xy => a * D xy.1 + b * D xy.2, by fun_prop⟩ =
      (a + b) * ∫ x, p x * D x ∂ν := by
  let Z := ∫ x, p x ∂ν
  let J := ∫ x, p x * D x ∂ν
  have hZ : Z ≠ 0 := (mass_pos ν p hp).ne'
  have hip := p.continuous.integrable_of_hasCompactSupport (μ := ν)
    (HasCompactSupport.of_compactSpace _)
  have hiD : Integrable (fun x => p x * D x) ν :=
    (p.continuous.mul D.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [pairAverage_nested]
  change (∫ x, ∫ y, (p x * p y / Z) * (a * D x + b * D y) ∂ν ∂ν) = (a + b) * J
  have he (x : A) : (∫ y, (p x * p y / Z) * (a * D x + b * D y) ∂ν) =
      a * (p x * D x) + (b / Z * J) * p x := by
    have hf : (fun y => (p x * p y / Z) * (a * D x + b * D y)) =
        (fun y => (a * p x * D x / Z) * p y + (b * p x / Z) * (p y * D y)) := by
      funext y
      ring
    rw [hf, integral_add (hip.const_mul _) (hiD.const_mul _), integral_const_mul,
      integral_const_mul]
    change (a * p x * D x / Z) * Z + (b * p x / Z) * J = _
    field_simp [hZ]
  simp_rw [he]
  rw [integral_add (hiD.const_mul _) (hip.const_mul _), integral_const_mul, integral_const_mul]
  change a * J + (b / Z * J) * Z = (a + b) * J
  field_simp [hZ]

/-- The comparison uses the explicit conditional pair density and derives its marginals. -/
theorem pairAverage_le (p D : C(A, ℝ)) (hp : ∀ a, 0 < p a)
    (H : C(A × A, ℝ)) (a b : ℝ)
    (hH : ∀ x y, H (x, y) ≤ a * D x + b * D y) :
    pairAverage ν p H ≤ (a + b) * ∫ x, p x * D x ∂ν := by
  rw [← pairAverage_affine ν p D hp a b]
  apply integral_mono
  · apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  · apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  intro xy
  exact mul_le_mul_of_nonneg_left (hH xy.1 xy.2)
    (div_nonneg (mul_nonneg (hp xy.1).le (hp xy.2).le) (mass_pos ν p hp).le)
end Conditional


section Product
variable [TopologicalSpace O] [CompactSpace O] [LocallyCompactSpace O]
  [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
  [TopologicalSpace A] [CompactSpace A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace X] [CompactSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure O) (ν : Measure A) (ξ : Measure X)
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]

/-- Exact conditional-density heat-bath comparison with the optimized two-edge constant.
The displayed left side is the actual conditional resampling energy. -/
theorem comparison (p : C(O × A, ℝ)) (hp : ∀ z, 0 < p z)
    (e : O × A → X) (he : Continuous e) (P : C(X × X, ℝ)) (f : C(X, ℝ))
    (hP : ∀ z, 0 ≤ P z) (hmass : ∀ x, (∫ y, P (x, y) ∂ξ) = 1)
    (t : ℝ) (ht : 0 < t)
    (hrow : ∀ r a b y, P (e (r, a), y) ≤ t ^ 2 * P (e (r, b), y)) :
    (1 / 2 : ℝ) * (∫ r, ∫ a, ∫ b,
      (p (r, a) * p (r, b) / (∫ c, p (r, c) ∂ν)) *
        (f (e (r, a)) - f (e (r, b))) ^ 2 ∂ν ∂ν ∂μ) ≤
      (1 + t) ^ 2 * ((1 / 2 : ℝ) * ∫ r, ∫ a,
        p (r, a) * increment ξ P f (e (r, a)) ∂ν ∂μ) := by
  let pr (r : O) : C(A, ℝ) :=
    ⟨fun a => p (r, a), p.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hD := increment_continuous ξ P f
  let Dr (r : O) : C(A, ℝ) :=
    ⟨fun a => increment ξ P f (e (r, a)), by fun_prop⟩
  let Hr (r : O) : C(A × A, ℝ) :=
    ⟨fun ab => (f (e (r, ab.1)) - f (e (r, ab.2))) ^ 2, by fun_prop⟩
  let Z (r : O) := ∫ a, p (r, a) ∂ν
  have hZ (r : O) : 0 < Z r := mass_pos ν (pr r) (fun a => hp (r, a))
  have hZc : Continuous Z := integral_continuous ν p p.continuous
  let L (r : O) := pairAverage ν (pr r) (Hr r)
  let J (r : O) := ∫ a, p (r, a) * increment ξ P f (e (r, a)) ∂ν
  have hLc : Continuous L := by
    change Continuous (fun r => ∫ ab : A × A,
      (p (r, ab.1) * p (r, ab.2) / Z r) *
        (f (e (r, ab.1)) - f (e (r, ab.2))) ^ 2 ∂ν.prod ν)
    apply integral_continuous (ν.prod ν) (fun z : O × (A × A) =>
      (p (z.1, z.2.1) * p (z.1, z.2.2) / Z z.1) *
        (f (e (z.1, z.2.1)) - f (e (z.1, z.2.2))) ^ 2)
    have hn : Continuous (fun z : O × (A × A) => p (z.1, z.2.1) * p (z.1, z.2.2)) := by
      fun_prop
    have hd : Continuous (fun z : O × (A × A) => Z z.1) := hZc.comp continuous_fst
    exact (hn.div hd (fun z => (hZ z.1).ne')).mul (by fun_prop)
  have hJc : Continuous J := by
    change Continuous (fun r => ∫ a, p (r, a) * increment ξ P f (e (r, a)) ∂ν)
    apply integral_continuous ν (fun z : O × A => p z * increment ξ P f (e z))
    fun_prop
  have hpoint (r : O) : L r ≤ (1 + t) ^ 2 * J r := by
    have h := pairAverage_le ν (pr r) (Dr r) (fun a => hp (r, a)) (Hr r)
      (1 + t) ((1 + 1 / t) * t ^ 2) (fun a b =>
        pointwise_two_edge ξ P f hP hmass (e (r, a)) (e (r, b)) (t ^ 2) t ht (hrow r a b))
    have hc : (1 + t) + (1 + 1 / t) * t ^ 2 = (1 + t) ^ 2 := by
      field_simp [ht.ne']
      ring
    rw [hc] at h
    exact h
  have hi := integral_mono
    (hLc.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _))
    ((continuous_const.mul hJc).integrable_of_hasCompactSupport (μ := μ)
      (HasCompactSupport.of_compactSpace _)) hpoint
  simp only [Pi.mul_apply] at hi
  rw [integral_const_mul] at hi
  have heL : (∫ r, L r ∂μ) = ∫ r, ∫ a, ∫ b,
      (p (r, a) * p (r, b) / (∫ c, p (r, c) ∂ν)) *
        (f (e (r, a)) - f (e (r, b))) ^ 2 ∂ν ∂ν ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with r
    exact pairAverage_nested ν (pr r) (Hr r)
  calc
    _ = (1 / 2 : ℝ) * ∫ r, L r ∂μ := by rw [heL]
    _ ≤ (1 / 2 : ℝ) * ((1 + t) ^ 2 * ∫ r, J r ∂μ) :=
      mul_le_mul_of_nonneg_left hi (by norm_num)
    _ = _ := by dsimp only [J]; ring
end Product

end
end UnifiedTheory.Clay.YangMills.HeatBathTwoEdge
