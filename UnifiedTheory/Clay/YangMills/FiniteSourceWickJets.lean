/- Constructed mixed derivatives of a finite-source quadratic renormalization.
The polynomial recurrence is evaluated under the original compact probability law. -/
import UnifiedTheory.Clay.YangMills.CompactQuadraticJets
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteSourceWickJets
noncomputable section
open MeasureTheory MvPolynomial

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- Chain rule for an evaluated multivariate polynomial, proved by polynomial induction. -/
theorem polynomial_hasDerivAt (P : MvPolynomial I ℝ) (v : ℝ → I → ℝ)
    (dv : I → ℝ) (t : ℝ) (hv : ∀ i, HasDerivAt (fun s => v s i) (dv i) t) :
    HasDerivAt (fun s => eval (v s) P) (∑ i, eval (v t) (pderiv i P) * dv i) t := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add P Q hP hQ =>
    simpa only [map_add, add_mul, Finset.sum_add_distrib] using hP.add hQ
  | mul_X P j hP =>
    have h := hP.mul (hv j)
    convert h using 1
    · funext s
      simp
    · simp [Pi.single_apply, mul_add, Finset.sum_add_distrib, mul_left_comm, mul_comm]
      simp only [apply_ite, map_zero, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, ← Finset.mul_sum]
      ring

/-- The exact mixed Hermite/Wick recurrence, for the covariance correction C. -/
def wickWord (C : I → I → ℝ) : List I → MvPolynomial I ℝ
  | [] => 1
  | i :: w => X i * wickWord C w - ∑ j, MvPolynomial.C (C i j) * pderiv j (wickWord C w)

omit [DecidableEq I] in
@[simp] theorem wickWord_nil (C : I → I → ℝ) : wickWord C [] = 1 := rfl

omit [DecidableEq I] in
@[simp] theorem wickWord_one (C : I → I → ℝ) (i : I) : wickWord C [i] = X i := by
  simp [wickWord]

omit [DecidableEq I] in
@[simp] theorem wickWord_two (C : I → I → ℝ) (i j : I) :
    wickWord C [i,j] = X i * X j - MvPolynomial.C (C i j) := by
  classical
  simp [wickWord, pderiv_X, Pi.single_apply]

omit [Fintype I] in
/-- One coordinate path has its actual Kronecker derivative. -/
theorem coordinate_hasDerivAt (t : I → ℝ) (i j : I) (s : ℝ) :
    HasDerivAt (fun r => Function.update t i r j) (if j = i then 1 else 0) s := by
  by_cases h : j = i
  · subst j
    simpa using hasDerivAt_id s
  · simpa only [Function.update_of_ne h, if_neg h] using hasDerivAt_const s (t j)

theorem weightedSum_hasDerivAt (w t : I → ℝ) (i : I) (s : ℝ) :
    HasDerivAt (fun r => ∑ j, w j * Function.update t i r j) (w i) s := by
  have h := HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) =>
    (coordinate_hasDerivAt t i j s).const_mul (w j))
  convert h using 1
  · funext r
    simp only [Finset.sum_apply]
  · simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Half the symmetric quadratic form, matching covariance subtraction C. -/
def quadratic (C : I → I → ℝ) (t : I → ℝ) : ℝ :=
  (1/2) * ∑ j, ∑ k, C j k * t j * t k

theorem quadratic_hasDerivAt (C : I → I → ℝ) (hC : ∀ i j, C i j = C j i)
    (t : I → ℝ) (i : I) (s : ℝ) :
    HasDerivAt (fun r => quadratic C (Function.update t i r))
      (∑ j, C i j * Function.update t i s j) s := by
  have h := (HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) =>
    HasDerivAt.sum (fun k (_ : k ∈ Finset.univ) =>
      ((coordinate_hasDerivAt t i j s).const_mul (C j k)).mul
        (coordinate_hasDerivAt t i k s)))).const_mul (1/2)
  convert h using 1
  · funext r
    simp [quadratic, Finset.sum_apply]
  · simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp_rw [← hC i]
    ring

omit [DecidableEq I] in
/-- Polynomial form of each mixed integrand, including every cross contraction. -/
theorem eval_wickWord_cons (C : I → I → ℝ) (w : List I) (i : I) (y : I → ℝ) :
    eval y (wickWord C (i::w)) =
      y i * eval y (wickWord C w) - ∑ j, C i j * eval y (pderiv j (wickWord C w)) := by
  simp [wickWord]

section Sources
variable {X : Type*}

def shifted (F : I → X → ℝ) (C : I → I → ℝ) (t : I → ℝ) (x : X) (i : I) : ℝ :=
  F i x - ∑ j, C i j * t j

def exponent (F : I → X → ℝ) (C : I → I → ℝ) (t : I → ℝ) (x : X) : ℝ :=
  (∑ i, F i x * t i) - quadratic C t

def integrand (F : I → X → ℝ) (C : I → I → ℝ) (w : List I)
    (t : I → ℝ) (x : X) : ℝ :=
  eval (shifted F C t x) (wickWord C w) * Real.exp (exponent F C t x)

theorem shifted_hasDerivAt (F : I → X → ℝ) (C : I → I → ℝ)
    (hC : ∀ i j, C i j = C j i) (t : I → ℝ) (x : X) (i j : I) (s : ℝ) :
    HasDerivAt (fun r => shifted F C (Function.update t i r) x j) (-C i j) s := by
  have h := (hasDerivAt_const s (F j x)).sub (weightedSum_hasDerivAt (C j) t i s)
  simpa only [shifted, hC j i, zero_sub] using h

theorem exponent_hasDerivAt (F : I → X → ℝ) (C : I → I → ℝ)
    (hC : ∀ i j, C i j = C j i) (t : I → ℝ) (x : X) (i : I) (s : ℝ) :
    HasDerivAt (fun r => exponent F C (Function.update t i r) x)
      (shifted F C (Function.update t i s) x i) s :=
  (weightedSum_hasDerivAt (fun j => F j x) t i s).sub
    (quadratic_hasDerivAt C hC t i s)

theorem integrand_hasDerivAt (F : I → X → ℝ) (C : I → I → ℝ)
    (hC : ∀ i j, C i j = C j i) (w : List I) (t : I → ℝ) (x : X) (i : I) (s : ℝ) :
    HasDerivAt (fun r => integrand F C w (Function.update t i r) x)
      (integrand F C (i::w) (Function.update t i s) x) s := by
  have hp := polynomial_hasDerivAt (wickWord C w)
    (fun r => shifted F C (Function.update t i r) x) (fun j => -C i j) s
    (fun j => shifted_hasDerivAt F C hC t x i j s)
  have he := (exponent_hasDerivAt F C hC t x i s).exp
  convert hp.mul he using 1
  unfold integrand
  rw [eval_wickWord_cons]
  have hh : (∑ j, eval (shifted F C (Function.update t i s) x)
      (pderiv j (wickWord C w)) * (-C i j)) =
      -(∑ j, C i j * eval (shifted F C (Function.update t i s) x)
        (pderiv j (wickWord C w))) := by
    simp only [mul_neg, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hh]
  ring

variable [TopologicalSpace X]

omit [DecidableEq I] in
theorem shifted_continuous (F : I → X → ℝ) (hF : ∀ i, Continuous (F i))
    (C : I → I → ℝ) : Continuous (fun z : (I → ℝ) × X => shifted F C z.1 z.2) := by
  apply continuous_pi
  intro i
  unfold shifted
  fun_prop

omit [DecidableEq I] in
theorem exponent_continuous (F : I → X → ℝ) (hF : ∀ i, Continuous (F i))
    (C : I → I → ℝ) : Continuous (fun z : (I → ℝ) × X => exponent F C z.1 z.2) := by
  unfold exponent quadratic
  fun_prop

omit [DecidableEq I] in
theorem integrand_continuous (F : I → X → ℝ) (hF : ∀ i, Continuous (F i))
    (C : I → I → ℝ) (w : List I) :
    Continuous (fun z : (I → ℝ) × X => integrand F C w z.1 z.2) :=
  ((MvPolynomial.continuous_eval (wickWord C w)).comp
    (shifted_continuous F hF C)).mul
      (Real.continuous_exp.comp (exponent_continuous F hF C))

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

def generating (F : I → X → ℝ) (C : I → I → ℝ) (t : I → ℝ) : ℝ :=
  Real.exp (-quadratic C t) * ∫ x, Real.exp (∑ i, F i x * t i) ∂μ

def jet (F : I → X → ℝ) (C : I → I → ℝ) (w : List I) (t : I → ℝ) : ℝ :=
  ∫ x, integrand F C w t x ∂μ

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ]
  [DecidableEq I] in
theorem jet_nil (F : I → X → ℝ) (C : I → I → ℝ) (t : I → ℝ) :
    jet μ F C [] t = generating μ F C t := by
  unfold jet integrand generating
  simp only [wickWord_nil, map_one, one_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [← Real.exp_add]
    congr 1
    unfold exponent
    ring)

/-- Compact domination proves the mixed coordinate derivative under the actual integral. -/
theorem jet_hasDerivAt (F : I → X → ℝ) (hF : ∀ i, Continuous (F i))
    (C : I → I → ℝ) (hC : ∀ i j, C i j = C j i) (w : List I)
    (t : I → ℝ) (i : I) (s : ℝ) :
    HasDerivAt (fun r => jet μ F C w (Function.update t i r))
      (jet μ F C (i::w) (Function.update t i s)) s := by
  have hu : Continuous (fun z : ℝ × X => Function.update t i z.1) :=
    (continuous_const : Continuous (fun _ : ℝ × X => t)).update i continuous_fst
  have hm : Continuous (fun z : ℝ × X => (Function.update t i z.1, z.2)) :=
    hu.prodMk continuous_snd
  have h1 : Continuous (fun z : ℝ × X => integrand F C w (Function.update t i z.1) z.2) := by
    simpa only [Function.comp_apply] using (integrand_continuous F hF C w).comp hm
  have h2 : Continuous (fun z : ℝ × X =>
      integrand F C (i::w) (Function.update t i z.1) z.2) := by
    simpa only [Function.comp_apply] using (integrand_continuous F hF C (i::w)).comp hm
  exact CompactGibbsSource.integral_hasDerivAt μ
    (fun r x => integrand F C w (Function.update t i r) x)
    (fun r x => integrand F C (i::w) (Function.update t i r) x)
    h1 h2 (fun r x => integrand_hasDerivAt F C hC w t x i r) s

end Sources

/-- Ordered genuine coordinate differentiation, with repeated directions allowed. -/
def mixedDeriv : List I → ((I → ℝ) → ℝ) → (I → ℝ) → ℝ
  | [], H, t => H t
  | i::w, H, t => deriv (fun s => mixedDeriv w H (Function.update t i s)) (t i)

section Compact
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Every mixed source derivative is the explicitly constructed polynomial insertion. -/
theorem mixedDeriv_eq_jet (F : I → X → ℝ) (hF : ∀ i, Continuous (F i))
    (C : I → I → ℝ) (hC : ∀ i j, C i j = C j i) (w : List I) :
    mixedDeriv w (generating μ F C) = jet μ F C w := by
  induction w with
  | nil => exact funext (fun t => (jet_nil μ F C t).symm)
  | cons i w ih =>
    funext t
    change deriv (fun s => mixedDeriv w (generating μ F C) (Function.update t i s))
      (t i) = jet μ F C (i::w) t
    simp_rw [ih]
    simpa only [Function.update_eq_self] using
      (jet_hasDerivAt μ F hF C hC w t i (t i)).deriv

/-- The all-order finite-source differentiated hierarchy, at zero source. -/
theorem mixedDeriv_zero (F : I → X → ℝ) (hF : ∀ i, Continuous (F i))
    (C : I → I → ℝ) (hC : ∀ i j, C i j = C j i) (w : List I) :
    mixedDeriv w (generating μ F C) 0 = ∫ x, eval (fun i => F i x) (wickWord C w) ∂μ := by
  rw [mixedDeriv_eq_jet μ F hF C hC w]
  simp only [jet, integrand, exponent, quadratic, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    sub_self, Real.exp_zero, mul_one]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    have hs : shifted F C 0 x = (fun i => F i x) := by
      funext i
      simp [shifted]
    exact congrArg (fun y => eval y (wickWord C w)) hs)

/-- The mixed second derivative subtracts C_ij, not a freely chosen raywise number. -/
theorem mixed_second (F : I → X → ℝ) (hF : ∀ i, Continuous (F i))
    (C : I → I → ℝ) (hC : ∀ i j, C i j = C j i) (i j : I) :
    mixedDeriv [i,j] (generating μ F C) 0 = (∫ x, F i x * F j x ∂μ) - C i j := by
  rw [mixedDeriv_zero μ F hF C hC]
  simp only [wickWord_two, map_sub, map_mul, eval_X, eval_C]
  have hi : Integrable (fun x => F i x * F j x) μ :=
    ((hF i).mul (hF j)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub hi (integrable_const (C i j))]
  simp

end Compact


end
end UnifiedTheory.Clay.YangMills.FiniteSourceWickJets
