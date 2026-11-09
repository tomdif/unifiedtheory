/- Quantitative comparison calculus for two mass-dual Schrodinger
curves with a shared leading form and differing static coefficients. -/
import UnifiedTheory.Audit.KFCausalFormCrossDerivative

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalSplitFormComparison
noncomputable section
open KFCausalBoundedFormCurve (gram)
open KFCausalMassGram (gram_left_pairing gram_right_pairing)
variable {V H K : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def splitOperator (A B : V →L[ℂ] K) (a : ℝ) : V →L[ℂ] V := gram B+a • gram A

private theorem cross_value (A B : V →L[ℂ] K) (h a b : ℝ) (x y : V) :
    inner ℂ ((-Complex.I*((1/(2*h):ℝ):ℂ)) • splitOperator A B a x) y+
      inner ℂ x ((-Complex.I*((1/(2*h):ℝ):ℂ)) • splitOperator A B b y)=
    (Complex.I*((1/(2*h):ℝ):ℂ))*((a-b:ℝ):ℂ)*inner ℂ (A x) (A y) := by
  simp only [splitOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    inner_smul_left,inner_smul_right,inner_add_left,inner_add_right,
    inner_smul_left_eq_smul,inner_smul_right_eq_smul,gram_left_pairing,gram_right_pairing]
  simp only [map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal,neg_neg,Complex.ofReal_sub,
    Complex.real_smul]
  ring

theorem pairing_derivative (J : V →L[ℂ] H) (A B : V →L[ℂ] K)
    (u v : ℝ → V) (h a b x : ℝ) (hv : ContinuousAt v x)
    (hu' : HasDerivAt (fun t => gram J (u t))
      ((-Complex.I*((1/(2*h):ℝ):ℂ)) • splitOperator A B a (u x)) x)
    (hv' : HasDerivAt (fun t => gram J (v t))
      ((-Complex.I*((1/(2*h):ℝ):ℂ)) • splitOperator A B b (v x)) x) :
    HasDerivAt (fun t => inner ℂ (J (u t)) (J (v t)))
      ((Complex.I*((1/(2*h):ℝ):ℂ))*((a-b:ℝ):ℂ)*inner ℂ (A (u x)) (A (v x))) x := by
  have hd := KFCausalFormCrossDerivative.physical_pairing_derivative J u v _ _ x hv hu' hv'
  exact (cross_value A B h a b (u x) (v x)) ▸ hd

theorem distance_square_derivative (J : V →L[ℂ] H) (A B : V →L[ℂ] K)
    (u v : ℝ → V) (h a b x : ℝ) (hne : h ≠ 0) (hv : ContinuousAt v x)
    (hu' : HasDerivAt (fun t => gram J (u t))
      ((-Complex.I*((1/(2*h):ℝ):ℂ)) • splitOperator A B a (u x)) x)
    (hv' : HasDerivAt (fun t => gram J (v t))
      ((-Complex.I*((1/(2*h):ℝ):ℂ)) • splitOperator A B b (v x)) x)
    (hnu : ∀ t, ‖J (u t)‖=‖J (u x)‖) (hnv : ∀ t, ‖J (v t)‖=‖J (v x)‖) :
    HasDerivAt (fun t => ‖J (u t)-J (v t)‖^2)
      ((1/h)*(a-b)*(inner ℂ (A (u x)) (A (v x))).im) x := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (pairing_derivative J A B u v h a b x hv hu' hv')
  have hn := ((hd.const_mul (-2)).const_add (‖J (u x)‖^2)).add_const (‖J (v x)‖^2)
  convert hn using 1
  · funext t
    rw [norm_sub_sq (𝕜 := ℂ),hnu t,hnv t]
    simp only [Function.comp_def,Complex.reCLM_apply]
    change ‖J (u x)‖^2-2*(inner ℂ (J (u t)) (J (v t))).re+‖J (v x)‖^2=_
    ring
  · simp only [Complex.reCLM_apply,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im]
    field_simp [hne]
    ring

omit [CompleteSpace K] in
theorem slope_bound (h U u E : ℝ) (hU : 0 < U) (hu : U ≤ u) (hE : 0 ≤ E)
    (x y : K) (hx : ‖x‖^2 ≤ u*E) (hy : ‖y‖^2 ≤ U*E) :
    |(1/h)*(1/u-1/U)*(inner ℂ x y).im| ≤ E*(u-U)/(|h| *U) := by
  have hu0 : 0 < u := hU.trans_le hu
  have hdif : 0 ≤ u-U := sub_nonneg.mpr hu
  have hxy : ‖x‖*‖y‖ ≤ u*E := by
    have hym : ‖y‖^2 ≤ u*E := hy.trans (mul_le_mul_of_nonneg_right hu hE)
    nlinarith only [hx,hym,sq_nonneg (‖x‖-‖y‖)]
  have ha : |1/u-1/U|=(u-U)/(u*U) := by
    rw [abs_of_nonpos (sub_nonpos.mpr (one_div_le_one_div_of_le hU hu))]
    field_simp
    ring
  rw [abs_mul,abs_mul,abs_div,abs_one,ha]
  calc
    _ ≤ ((1/|h|)*((u-U)/(u*U)))*(‖x‖*‖y‖) :=
      mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans (norm_inner_le_norm x y))
        (by positivity)
    _ ≤ ((1/|h|)*((u-U)/(u*U)))*(u*E) :=
      mul_le_mul_of_nonneg_left hxy (by positivity)
    _ = _ := by
      by_cases hh : h=0
      · simp [hh]
      · field_simp

theorem quadratic_bound (D d : ℝ → ℝ) (U T C : ℝ) (hT : 0 ≤ T)
    (hc : ContinuousOn D (Set.Icc U (U+T))) (hi : D U=0)
    (hd : ∀ u ∈ Set.Ioo U (U+T), HasDerivAt D (d u) u)
    (hb : ∀ u ∈ Set.Ioo U (U+T), d u ≤ C*(u-U)) : D (U+T) ≤ C*T^2/2 := by
  have hq (x : ℝ) : HasDerivAt (fun u : ℝ => C*(u-U)^2/2) (C*(x-U)) x := by
    convert ((((hasDerivAt_id x).sub_const U).pow 2).const_mul C).div_const 2 using 1
    simp only [id_eq]
    ring
  have hm : AntitoneOn (fun u => D u-C*(u-U)^2/2) (Set.Icc U (U+T)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc U (U+T))
      (hc.sub (by fun_prop))
      (fun x hx => ((hd x (by simpa only [interior_Icc] using hx)).sub (hq x)).hasDerivWithinAt)
    intro x hx
    exact sub_nonpos.mpr (hb x (by simpa only [interior_Icc] using hx))
  have ht : U ≤ U+T := by linarith
  have he := hm ⟨le_rfl,ht⟩ ⟨ht,le_rfl⟩ ht
  simp only [hi,sub_self,zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_div,
    add_sub_cancel_left] at he
  linarith only [he]

#print axioms pairing_derivative
#print axioms distance_square_derivative
#print axioms slope_bound
#print axioms quadratic_bound
end
end UnifiedTheory.Audit.KFCausalSplitFormComparison
