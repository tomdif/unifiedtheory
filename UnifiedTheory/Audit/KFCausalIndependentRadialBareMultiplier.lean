/- The bare packet quotient against the actual broad Gaussian baseline.
There is no prior vacuum action and no extra inverse clock. A transverse
Gaussian margin is retained for simultaneous polynomial/source absorption. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialHolomorphicQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialBareMultiplier
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexShearPerturbation (Space flow rotatedFlow)
open KFCausalComplexShearGroup (flow_zero flow_compose flow_real)
open KFCausalIndependentRadialNormalization (normalize weights)
open KFCausalIndependentRadialHolomorphicQuotient (baselineVector baseline)
open KFCausalPhysicalReciprocalNormalization (coupling)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalComplexQuadraticPerturbation (quadratic weightedQuadratic)

def multiplier (ε a α W wL wR c : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  (4*W:ℝ)*Complex.exp (-((a/2:ℝ):ℂ)*q^2)*
    Complex.exp (-quadratic (fun i => baselineVector ε α wL wR c q x i)+
      weightedQuadratic (weights W wL wR) (fun i => baselineVector ε α wL wR c q x i))

def numerator (ε a α wL wR c : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  (Real.pi/α:ℝ)*Complex.exp (-complexInverse ε q)*Complex.exp (-(a:ℂ)*q^2)*
    Complex.exp (-quadratic (fun i => baselineVector ε α wL wR c q x i))

theorem vector_analytic (ε h α wL wR c : ℝ) (hε : 0 < ε) (hb : |h| ≤ ε/10)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) (i : Fin 5) :
    AnalyticAt ℂ (fun z => baselineVector ε α wL wR c z x i) q := by
  have hs := KFCausalComplexClockInverse.complexInverse_analytic ε hε q
    (KFCausalTwoShearClockQuotient.strip_membership ε h hε hb q hq).1
  fin_cases i <;> dsimp [baselineVector,flow] <;> fun_prop

private theorem increment_bound (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ ε/10)
    (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖complexInverse ε q-complexInverse ε (q.re:ℂ)‖ ≤ 1/5 := by
  have ht := KFCausalTwoShearClockQuotient.two_increment_bound ε h hε hb q hq
  linarith [norm_nonneg (complexInverse ε (KFCausalTwoShearClockQuotient.shift h q)-complexInverse ε q)]

theorem vector_norm_bound (ε h α wL wR c : ℝ) (hε : 0 < ε) (hb : |h| ≤ ε/10)
    (hα : 0 < α) (hR : 1 ≤ wR) (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖baselineVector ε α wL wR c q x‖ ≤
      (20/17:ℝ)*‖baselineVector ε α wL wR c (q.re:ℂ) x‖ := by
  let U : Space ≃ₗᵢ[ℂ] Space := LinearIsometryEquiv.refl ℂ Space
  have ht := KFCausalComplexShearPerturbation.baseline_norm U (coupling α wR)
    (KFCausalPhysicalReciprocalNormalization.coupling_bound α wR hα hR)
    _ (increment_bound ε h hε hb q hq) (baselineVector ε α wL wR c (q.re:ℂ) x)
  change ‖flow (coupling α wR) (complexInverse ε q-complexInverse ε (q.re:ℂ))
    (flow (coupling α wR) (complexInverse ε (q.re:ℂ)) (normalize α wL wR c x))‖ ≤ _ at ht
  rw [flow_compose,sub_add_cancel] at ht
  exact ht

theorem transverse_gaussian_bound (ε h α W wL wR c : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ ε/10) (hα : 0 < α) (hL : 1 ≤ wL) (hR : 1 ≤ wR) (hW : wL ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖Complex.exp (-quadratic (fun i => baselineVector ε α wL wR c q x i)+
      weightedQuadratic (weights W wL wR) (fun i => baselineVector ε α wL wR c q x i))‖ ≤
      Real.exp (-(78/289:ℝ)*‖baselineVector ε α wL wR c (q.re:ℂ) x‖^2) := by
  let U : Space ≃ₗᵢ[ℂ] Space := LinearIsometryEquiv.refl ℂ Space
  let ref := baselineVector ε α wL wR c (q.re:ℂ) x
  let t := complexInverse ε q-complexInverse ε (q.re:ℂ)
  have hr : ∀ i, (ref i).im=0 := by
    dsimp [ref,baselineVector]
    rw [KFCausalComplexClockInverse.complexInverse_real ε hε]
    exact flow_real _ _ _ (KFCausalIndependentRadialNormalization.normalize_real α wL wR c x)
  have ht : ‖(0:ℂ)‖+‖t‖ ≤ 1/5 := by simpa [t] using increment_bound ε h hε hb q hq
  have hm := KFCausalTwoShearTransverseQuotient.transverse_bound U U (coupling α wR)
    (KFCausalPhysicalReciprocalNormalization.coupling_bound α wR hα hR)
    (weights W wL wR) (KFCausalIndependentRadialNormalization.weights_bound W wL wR hL hR hW)
    0 t ht ref hr
  have he : flow (coupling α wR) t ref=baselineVector ε α wL wR c q x := by
    dsimp [t,ref,baselineVector]
    rw [flow_compose,sub_add_cancel]
  change ‖Complex.exp (-quadratic (fun i => flow (coupling α wR) 0 (flow (coupling α wR) t ref) i)+
    weightedQuadratic (weights W wL wR) (fun i => flow (coupling α wR) t ref i))‖ ≤ _ at hm
  rw [flow_zero,he] at hm
  exact hm

theorem multiplier_analytic (ε h a α W wL wR c : ℝ) (hε : 0 < ε) (hb : |h| ≤ ε/10)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    AnalyticAt ℂ (fun z => multiplier ε a α W wL wR c z x) q := by
  have hy := vector_analytic ε h α wL wR c hε hb q hq x
  have hqf : AnalyticAt ℂ (fun z => quadratic (fun i => baselineVector ε α wL wR c z x i)) q := by
    simp only [quadratic,Fin.sum_univ_succ,Fin.sum_univ_zero]
    exact ((hy 0).pow 2).add (((hy 1).pow 2).add (((hy 2).pow 2).add
      (((hy 3).pow 2).add (((hy 4).pow 2).add analyticAt_const))))
  have hwf : AnalyticAt ℂ (fun z => weightedQuadratic (weights W wL wR)
      (fun i => baselineVector ε α wL wR c z x i)) q := by
    simp only [weightedQuadratic,Fin.sum_univ_succ,Fin.sum_univ_zero]
    exact (analyticAt_const.mul ((hy 0).pow 2)).add
      ((analyticAt_const.mul ((hy 1).pow 2)).add
      ((analyticAt_const.mul ((hy 2).pow 2)).add
      ((analyticAt_const.mul ((hy 3).pow 2)).add
      ((analyticAt_const.mul ((hy 4).pow 2)).add analyticAt_const))))
  unfold multiplier
  fun_prop

theorem multiplier_gaussian_bound (ε h a α W wL wR c : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ ε/10) (ha : 0 ≤ a) (hα : 0 < α) (hL : 1 ≤ wL) (hR : 1 ≤ wR)
    (hW : wL ≤ W) (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖multiplier ε a α W wL wR c q x‖ ≤
      (4*W*Real.exp ((a/2)*h^2))*Real.exp (-(78/289:ℝ)*‖baselineVector ε α wL wR c (q.re:ℂ) x‖^2) := by
  have hWp : 0 < W := (zero_lt_one.trans_le hL).trans_le hW
  have hc : ‖Complex.exp (-((a/2:ℝ):ℂ)*q^2)‖ ≤ Real.exp ((a/2)*h^2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hi : q.im^2 ≤ h^2 := (sq_le_sq).mpr hq
    simp only [pow_two,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,
      Complex.ofReal_im,neg_zero,zero_mul,sub_zero]
    nlinarith [mul_nonneg ha (sq_nonneg q.re),mul_nonneg ha (sub_nonneg.mpr hi)]
  have hg := transverse_gaussian_bound ε h α W wL wR c hε hb hα hL hR hW q hq x
  rw [multiplier,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity)) hg (norm_nonneg _) (by positivity)

theorem multiplier_mul_baseline (ε a α W wL wR c : ℝ) (hW : W ≠ 0) (q : ℂ) (x : Joint 2 4) :
    multiplier ε a α W wL wR c q x*baseline ε a α W wL wR c q x =
      numerator ε a α wL wR c q x := by
  have hp : ((4*W:ℝ):ℂ)*((Real.pi/(4*W*α):ℝ):ℂ)=((Real.pi/α:ℝ):ℂ) := by
    have hWc : (W:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hW
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    field_simp [hWc]
  unfold multiplier baseline numerator
  calc
    _ = (((4*W:ℝ):ℂ)*((Real.pi/(4*W*α):ℝ):ℂ))*Complex.exp
      ((-((a/2:ℝ):ℂ)*q^2)+(-quadratic (fun i => baselineVector ε α wL wR c q x i)+
      weightedQuadratic (weights W wL wR) (fun i => baselineVector ε α wL wR c q x i))+
      (-complexInverse ε q)+(-((a/2:ℝ):ℂ)*q^2)+
      (-weightedQuadratic (weights W wL wR) (fun i => baselineVector ε α wL wR c q x i))) := by
        simp only [Complex.exp_add]
        ring
    _ = _ := by
      rw [hp]
      rw [show (-((a/2:ℝ):ℂ)*q^2)+(-quadratic (fun i => baselineVector ε α wL wR c q x i)+
        weightedQuadratic (weights W wL wR) (fun i => baselineVector ε α wL wR c q x i))+
        (-complexInverse ε q)+(-((a/2:ℝ):ℂ)*q^2)+
        (-weightedQuadratic (weights W wL wR) (fun i => baselineVector ε α wL wR c q x i)) =
        -complexInverse ε q+(-(a:ℂ)*q^2)+(-quadratic (fun i => baselineVector ε α wL wR c q x i)) by push_cast; ring]
      simp only [Complex.exp_add]
      ring

#print axioms vector_analytic
#print axioms vector_norm_bound
#print axioms transverse_gaussian_bound
#print axioms multiplier_analytic
#print axioms multiplier_gaussian_bound
#print axioms multiplier_mul_baseline
end
end UnifiedTheory.Audit.KFCausalIndependentRadialBareMultiplier
