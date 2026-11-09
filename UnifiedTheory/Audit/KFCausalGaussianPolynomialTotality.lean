/- Completeness of polynomial Gaussian functions in scalar L2. Fourier
uniqueness and dominated convergence derive totality from actual Gaussian
integrability; no completeness or spectral hypothesis is assumed. -/
import UnifiedTheory.Audit.KFCausalGaussianQuadraticFourier
import UnifiedTheory.Audit.KFCausalFourierUniqueness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Polynomial.Basis

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalGaussianPolynomialTotality
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform Topology
open KFCausalGaussianQuadraticFourier (moment moment_real moment_memLp moment_continuous)
open KFCausalGaussianSliceDomain (gaussian)

abbrev ScalarHilbert := Lp ℂ 2 (volume : Measure ℝ)

def monomialState (a : ℝ) (ha : 0 < a) (n : ℕ) : ScalarHilbert :=
  (moment_memLp a ha n).toLp (moment a n)

theorem monomialState_coe (a : ℝ) (ha : 0 < a) (n : ℕ) :
    monomialState a ha n =ᵐ[volume] moment a n := (moment_memLp a ha n).coeFn_toLp

theorem moment_star (a : ℝ) (n : ℕ) (x : ℝ) : star (moment a n x) = moment a n x := by
  rw [moment_real]
  exact Complex.conj_ofReal _

theorem moment_zero_norm (a x : ℝ) : ‖moment a 0 x‖ = Real.exp (-a*x^2) := by
  rw [moment_real]
  simp only [pow_zero,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

def expPartial (z : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n, z^j/(j.factorial:ℂ)

theorem expPartial_tendsto (z : ℂ) :
    Tendsto (expPartial z) atTop (𝓝 (Complex.exp z)) := by
  simpa only [expPartial,← Complex.exp_eq_exp_ℂ] using
    (NormedSpace.expSeries_div_hasSum_exp z).tendsto_sum_nat

theorem expPartial_norm (z : ℂ) (n : ℕ) : ‖expPartial z n‖ ≤ Real.exp ‖z‖ := by
  apply (norm_sum_le _ _).trans
  have he : (∑ j ∈ Finset.range n, ‖z^j/(j.factorial:ℂ)‖) =
      ∑ j ∈ Finset.range n, ‖z‖^j/(j.factorial:ℝ) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [norm_div,norm_pow,Complex.norm_natCast]
  rw [he]
  exact Real.sum_le_exp_of_nonneg (norm_nonneg z) n

private theorem exponent_bound (a : ℝ) (ha : 0 < a) (r x : ℝ) :
    r*|x|-a*x^2 ≤ r^2/(2*a)-(a/2)*x^2 := by
  have hs : 0 ≤ a^2*x^2-2*a*|x| *r+r^2 := by
    have hs := sq_nonneg (a*|x|-r)
    have he : (a*|x|-r)^2 = a^2*x^2-2*a*|x| *r+r^2 := by
      calc
        _ = a^2*|x|^2-2*a*|x| *r+r^2 := by ring
        _ = _ := by rw [sq_abs]
    rwa [he] at hs
  have he : r*|x|-(a/2)*x^2 ≤ r^2/(2*a) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*a)).mpr
    nlinarith
  linarith

theorem expPartial_gaussian_bound (a : ℝ) (ha : 0 < a) (z : ℂ) (n : ℕ) (x : ℝ) :
    ‖expPartial (z*(x:ℂ)) n*moment a 0 x‖ ≤
      Real.exp (‖z‖^2/(2*a))*‖moment (a/2) 0 x‖ := by
  rw [norm_mul,moment_zero_norm,moment_zero_norm]
  calc
    _ ≤ Real.exp ‖z*(x:ℂ)‖*Real.exp (-a*x^2) :=
      mul_le_mul_of_nonneg_right (expPartial_norm _ n) (Real.exp_pos _).le
    _ = Real.exp (‖z‖*|x|-a*x^2) := by
      rw [← Real.exp_add,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      congr 1
      ring
    _ ≤ Real.exp (‖z‖^2/(2*a)-(a/2)*x^2) :=
      Real.exp_le_exp.mpr (exponent_bound a ha ‖z‖ x)
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add,neg_mul]

/-- All Gaussian moments determine the weighted exponential transform. -/
theorem exponential_integral_zero (a : ℝ) (ha : 0 < a) (f : ℝ → ℂ) (hf : MemLp f 2)
    (hzero : ∀ n : ℕ, (∫ x, moment a n x*f x) = 0) (z : ℂ) :
    (∫ x : ℝ, Complex.exp (z*(x:ℂ))*moment a 0 x*f x) = 0 := by
  let F : ℕ → ℝ → ℂ := fun n x => expPartial (z*(x:ℂ)) n*moment a 0 x*f x
  let bound : ℝ → ℝ := fun x => Real.exp (‖z‖^2/(2*a))*
    (‖moment (a/2) 0 x‖*‖f x‖)
  have hi : Integrable bound :=
    (((moment_memLp (a/2) (by positivity) 0).norm).integrable_mul hf.norm).const_mul _
  have hm (n : ℕ) : AEStronglyMeasurable (F n) volume := by
    have hc : Continuous (fun x : ℝ => expPartial (z*(x:ℂ)) n*moment a 0 x) := by
      unfold expPartial
      exact (continuous_finset_sum _ (fun j _ => by fun_prop)).mul (moment_continuous a 0)
    exact hc.aestronglyMeasurable.mul hf.1
  have hb (n : ℕ) : ∀ᵐ x, ‖F n x‖ ≤ bound x := by
    filter_upwards [] with x
    exact (show ‖F n x‖ ≤ _ by
      dsimp only [F,bound]
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (expPartial_gaussian_bound a ha z n x)
        (norm_nonneg (f x))).trans_eq (mul_assoc _ _ _))
  have hl : ∀ᵐ x : ℝ, Tendsto (fun n => F n x) atTop
      (𝓝 (Complex.exp (z*(x:ℂ))*moment a 0 x*f x)) := by
    filter_upwards [] with x
    exact ((expPartial_tendsto (z*(x:ℂ))).mul_const (moment a 0 x)).mul_const (f x)
  have ht := tendsto_integral_of_dominated_convergence bound hm hi hb hl
  have hz (n : ℕ) : (∫ x, F n x) = 0 := by
    have he (x : ℝ) : F n x =
        ∑ j ∈ Finset.range n, (z^j/(j.factorial:ℂ))*(moment a j x*f x) := by
      simp only [F,expPartial,Finset.sum_mul,moment,pow_zero,one_mul,mul_pow]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [he]
    have hj (j : ℕ) : Integrable (fun x => (z^j/(j.factorial:ℂ))*(moment a j x*f x)) :=
      ((moment_memLp a ha j).integrable_mul hf).const_mul _
    rw [integral_finset_sum _ (fun j _ => hj j)]
    simp only [integral_const_mul,hzero,mul_zero,Finset.sum_const_zero]
  exact tendsto_nhds_unique ht (by simpa only [hz] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0)))

theorem zero_of_gaussian_moments (a : ℝ) (ha : 0 < a) (f : ℝ → ℂ) (hf : MemLp f 2)
    (hzero : ∀ n : ℕ, (∫ x, moment a n x*f x) = 0) : f =ᵐ[volume] 0 := by
  let g : ℝ → ℂ := fun x => moment a 0 x*f x
  have hg : Integrable g := (moment_memLp a ha 0).integrable_mul hf
  have hF (p : ℝ) : (𝓕 g) p = 0 := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    have he := exponential_integral_zero a ha f hf hzero ((-2*Real.pi*p:ℝ)*Complex.I)
    convert he using 1
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [g,smul_eq_mul,mul_assoc]
    congr 2
    push_cast
    ring
  have hz := KFCausalFourierUniqueness.integrable_zero_of_fourier_zero g hg hF
  filter_upwards [hz] with x hx
  apply (mul_eq_zero.mp hx).resolve_left
  simp only [moment,pow_zero,one_mul,gaussian]
  exact Complex.exp_ne_zero _

theorem dense_monomial_span (a : ℝ) (ha : 0 < a) :
    (Submodule.span ℂ (Set.range (monomialState a ha))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff,Submodule.eq_bot_iff]
  intro f hf
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  apply zero_of_gaussian_moments a ha f (Lp.memLp f)
  intro n
  have hp : monomialState a ha n ∈ Submodule.span ℂ (Set.range (monomialState a ha)) :=
    Submodule.subset_span ⟨n,rfl⟩
  have hi := Submodule.inner_right_of_mem_orthogonal hp hf
  rw [L2.inner_def] at hi
  convert hi using 1
  apply integral_congr_ae
  filter_upwards [monomialState_coe a ha n] with x hx
  rw [hx,RCLike.inner_apply']
  change moment a n x*f x = star (moment a n x)*f x
  rw [moment_star]

def polynomialState (a : ℝ) (ha : 0 < a) : Polynomial ℂ →ₗ[ℂ] ScalarHilbert :=
  (Polynomial.basisMonomials ℂ).constr ℂ (monomialState a ha)

theorem polynomialState_monomial (a : ℝ) (ha : 0 < a) (n : ℕ) :
    polynomialState a ha (Polynomial.monomial n 1) = monomialState a ha n := by
  simpa only [Polynomial.coe_basisMonomials] using
    (Polynomial.basisMonomials ℂ).constr_basis ℂ (monomialState a ha) n

/-- The algebraic linear map represents the actual polynomial Gaussian function. -/
theorem polynomialState_coe (a : ℝ) (ha : 0 < a) (P : Polynomial ℂ) :
    polynomialState a ha P =ᵐ[volume] fun x : ℝ => P.eval (x:ℂ)*gaussian a x := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add]
    filter_upwards [Lp.coeFn_add (polynomialState a ha P) (polynomialState a ha Q),hP,hQ]
      with x hx hp hq
    simpa only [Pi.add_apply,hp,hq,Polynomial.eval_add,add_mul] using hx
  | monomial n c =>
    have he : Polynomial.monomial n c = c • Polynomial.monomial n (1:ℂ) := by
      rw [Polynomial.smul_monomial,smul_eq_mul,mul_one]
    rw [he,map_smul,polynomialState_monomial]
    filter_upwards [Lp.coeFn_smul c (monomialState a ha n),monomialState_coe a ha n]
      with x hx hm
    simpa only [Pi.smul_apply,smul_eq_mul,hm,Polynomial.eval_smul,
      Polynomial.eval_monomial,one_mul,moment,mul_assoc] using hx

#print axioms exponential_integral_zero
#print axioms zero_of_gaussian_moments
#print axioms dense_monomial_span
#print axioms polynomialState_monomial
#print axioms polynomialState_coe
end
end UnifiedTheory.Audit.KFCausalGaussianPolynomialTotality
