/- Holomorphic Gaussian quotients for two independent charged radial widths.
The original physical shear and broad paired baseline are retained. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialNormalization
import UnifiedTheory.Audit.KFCausalComplexShearGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 1024

namespace UnifiedTheory.Audit.KFCausalIndependentRadialHolomorphicQuotient
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalClockFloorComplexDefect (complexClock)
open KFCausalComplexShearPerturbation (Space flow rotatedFlow)
open KFCausalIndependentRadialNormalization (normalize weights)
open KFCausalPhysicalReciprocalNormalization (coupling)
open KFCausalNormalizedComplexRotation (rotate rotationIsometry)
open KFCausalComplexQuadraticPerturbation (quadratic weightedQuadratic)
open KFCausalTwoShearClockQuotient (shift quotient)

def baselineVector (ε α wL wR c : ℝ) (q : ℂ) (x : Joint 2 4) : Space :=
  flow (coupling α wR) (complexInverse ε q) (normalize α wL wR c x)

def targetVector (ε h α wL wR c η : ℝ) (q : ℂ) (x : Joint 2 4) : Space :=
  rotatedFlow (rotationIsometry η) (coupling α wR)
    (complexInverse ε (shift h q)-complexInverse ε q) (baselineVector ε α wL wR c q x)

def baseline (ε a α W wL wR c : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  ((Real.pi/(4*W*α):ℝ):ℂ)*Complex.exp (-complexInverse ε q)*
    Complex.exp (-((a/2:ℝ):ℂ)*q^2)*
    Complex.exp (-weightedQuadratic (weights W wL wR) (fun i => baselineVector ε α wL wR c q x i))

def numerator (ε h a α wL wR c η : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  ((Real.pi/α:ℝ):ℂ)*(complexClock ε q)⁻¹*
    Complex.exp (-complexInverse ε (shift h q))*
    Complex.exp (-(a:ℂ)*(shift h q)^2)*
    Complex.exp (-quadratic (fun i => targetVector ε h α wL wR c η q x i))

def multiplier (ε h a α W wL wR c η : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  ((4*W:ℝ):ℂ)*quotient ε h a q*
    Complex.exp (-quadratic (fun i => targetVector ε h α wL wR c η q x i)+
      weightedQuadratic (weights W wL wR) (fun i => baselineVector ε α wL wR c q x i))

theorem multiplier_mul_baseline (ε h a α W wL wR c η : ℝ) (hW0 : W ≠ 0) (q : ℂ) (x : Joint 2 4) :
    multiplier ε h a α W wL wR c η q x * baseline ε a α W wL wR c q x =
      numerator ε h a α wL wR c η q x := by
  have hp : ((4*W:ℝ):ℂ)*((Real.pi/(4*W*α):ℝ):ℂ)=((Real.pi/α:ℝ):ℂ) := by
    have hWc : (W:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hW0
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    field_simp [hWc]
  unfold multiplier baseline numerator quotient
  calc
    _ = (((4*W:ℝ):ℂ)*((Real.pi/(4*W*α):ℝ):ℂ))*(complexClock ε q)⁻¹*
        Complex.exp ((complexInverse ε q-complexInverse ε (shift h q))+
          (-(a:ℂ)*(shift h q)^2+((a/2:ℝ):ℂ)*q^2)+
          (-quadratic (fun i => targetVector ε h α wL wR c η q x i)+
            weightedQuadratic (weights W wL wR) (fun i => baselineVector ε α wL wR c q x i))+
          (-complexInverse ε q)+(-((a/2:ℝ):ℂ)*q^2)+
          (-weightedQuadratic (weights W wL wR) (fun i => baselineVector ε α wL wR c q x i))) := by
      simp only [Complex.exp_add]
      ring
    _ = _ := by
      rw [hp,show (complexInverse ε q-complexInverse ε (shift h q))+
          (-(a:ℂ)*(shift h q)^2+((a/2:ℝ):ℂ)*q^2)+
          (-quadratic (fun i => targetVector ε h α wL wR c η q x i)+
            weightedQuadratic (weights W wL wR) (fun i => baselineVector ε α wL wR c q x i))+
          (-complexInverse ε q)+(-((a/2:ℝ):ℂ)*q^2)+
          (-weightedQuadratic (weights W wL wR) (fun i => baselineVector ε α wL wR c q x i)) =
          -complexInverse ε (shift h q)+(-(a:ℂ)*(shift h q)^2)+
            (-quadratic (fun i => targetVector ε h α wL wR c η q x i)) by ring]
      simp only [Complex.exp_add]
      ring

private theorem analytic_flow (σ : ℝ) (f : ℂ → ℂ) (g : ℂ → Space) (q : ℂ)
    (hf : AnalyticAt ℂ f q) (hg : ∀ i, AnalyticAt ℂ (fun z => g z i) q) :
    ∀ i, AnalyticAt ℂ (fun z => flow σ (f z) (g z) i) q := by
  intro i
  fin_cases i <;> dsimp [flow]
  all_goals fun_prop

private theorem analytic_rotate (η : ℝ) (g : ℂ → Space) (q : ℂ)
    (hg : ∀ i, AnalyticAt ℂ (fun z => g z i) q) :
    ∀ i, AnalyticAt ℂ (fun z => rotate η (g z) i) q := by
  intro i
  fin_cases i <;> dsimp [rotate]
  all_goals fun_prop

private theorem analytic_vectors (ε h α wL wR c η : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    (∀ i, AnalyticAt ℂ (fun z => baselineVector ε α wL wR c z x i) q) ∧
    (∀ i, AnalyticAt ℂ (fun z => targetVector ε h α wL wR c η z x i) q) := by
  have hm := KFCausalTwoShearClockQuotient.strip_membership ε h hε hh q hq
  have hs := KFCausalComplexClockInverse.complexInverse_analytic ε hε q hm.1
  have ht : AnalyticAt ℂ (fun z => complexInverse ε (shift h z)) q :=
    (KFCausalComplexClockInverse.complexInverse_analytic ε hε (shift h q) hm.2.1).comp
      (by unfold shift; fun_prop)
  have hy := analytic_flow (coupling α wR) _ (fun _ => normalize α wL wR c x) q hs
    (fun _ => analyticAt_const)
  refine ⟨hy,?_⟩
  exact analytic_rotate (-η) _ q (analytic_flow (coupling α wR) _ _ q (ht.sub hs)
    (analytic_rotate η _ q hy))

theorem multiplier_analytic (ε h a α W wL wR c η : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    AnalyticAt ℂ (fun z => multiplier ε h a α W wL wR c η z x) q := by
  obtain ⟨hy,ht⟩ := analytic_vectors ε h α wL wR c η hε hh q hq x
  have hqf := KFCausalTwoShearClockQuotient.quotient_analytic ε h hε hh a q hq
  have hty : AnalyticAt ℂ (fun z => quadratic (fun i => targetVector ε h α wL wR c η z x i)) q := by
    simp only [quadratic,Fin.sum_univ_succ,Fin.sum_univ_zero]
    exact ((ht 0).pow 2).add (((ht 1).pow 2).add (((ht 2).pow 2).add
      (((ht 3).pow 2).add (((ht 4).pow 2).add analyticAt_const))))
  have hby : AnalyticAt ℂ (fun z => weightedQuadratic (weights W wL wR)
      (fun i => baselineVector ε α wL wR c z x i)) q := by
    simp only [weightedQuadratic,Fin.sum_univ_succ,Fin.sum_univ_zero]
    exact (analyticAt_const.mul ((hy 0).pow 2)).add
      ((analyticAt_const.mul ((hy 1).pow 2)).add
      ((analyticAt_const.mul ((hy 2).pow 2)).add
      ((analyticAt_const.mul ((hy 3).pow 2)).add
      ((analyticAt_const.mul ((hy 4).pow 2)).add analyticAt_const))))
  exact (analyticAt_const.mul hqf).mul (hty.neg.add hby).cexp

theorem multiplier_gaussian_bound (ε h a α W wL wR c η : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (ha : 0 ≤ a) (hα : 0 < α) (hL : 1 ≤ wL) (hR : 1 ≤ wR) (hW : wL ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖multiplier ε h a α W wL wR c η q x‖ ≤
      (4*W)*(ε⁻¹*Real.exp (|h|/ε)*Real.exp (-(a/2)*q.re^2+4*a*h^2))*
        Real.exp (-(78/289:ℝ)*‖baselineVector ε α wL wR c (q.re:ℂ) x‖^2) := by
  have hWp : 0 < W := by linarith
  let σ := coupling α wR
  let ref := flow σ (complexInverse ε (q.re:ℂ)) (normalize α wL wR c x)
  let V : Space ≃ₗᵢ[ℂ] Space := LinearIsometryEquiv.refl ℂ Space
  have hr : ∀ i, (ref i).im=0 := by
    dsimp [ref]
    rw [KFCausalComplexClockInverse.complexInverse_real ε hε]
    exact KFCausalComplexShearGroup.flow_real σ _ _
      (KFCausalIndependentRadialNormalization.normalize_real α wL wR c x)
  have hb : rotatedFlow V σ (complexInverse ε q-complexInverse ε (q.re:ℂ)) ref =
      baselineVector ε α wL wR c q x := by
    change flow σ (complexInverse ε q-complexInverse ε (q.re:ℂ))
      (flow σ (complexInverse ε (q.re:ℂ)) (normalize α wL wR c x)) = _
    rw [KFCausalComplexShearGroup.flow_compose,sub_add_cancel]
    rfl
  have hσ := KFCausalPhysicalReciprocalNormalization.coupling_bound α wR hα hR
  have hweights := KFCausalIndependentRadialNormalization.weights_bound W wL wR hL hR hW
  have hm := KFCausalTwoShearTransverseQuotient.clock_times_transverse_bound ε h hε hh
    a ha (rotationIsometry η) V σ hσ (weights W wL wR) hweights q hq ref hr
  simp only [KFCausalTwoShearTransverseQuotient.clockTransverse,
    KFCausalTwoShearTransverseQuotient.transverse,hb] at hm
  change ‖quotient ε h a q*Complex.exp (-quadratic (fun i => targetVector ε h α wL wR c η q x i)+
    weightedQuadratic (weights W wL wR) (fun i => baselineVector ε α wL wR c q x i))‖ ≤ _ at hm
  calc
    ‖multiplier ε h a α W wL wR c η q x‖ = (4*W)*‖quotient ε h a q*
        Complex.exp (-quadratic (fun i => targetVector ε h α wL wR c η q x i)+
          weightedQuadratic (weights W wL wR) (fun i => baselineVector ε α wL wR c q x i))‖ := by
      rw [multiplier,mul_assoc,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ 4*W by positivity)]
    _ ≤ (4*W)*((ε⁻¹*Real.exp (|h|/ε)*Real.exp (-(a/2)*q.re^2+4*a*h^2))*
        Real.exp (-(78/289:ℝ)*‖ref‖^2)) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by dsimp only [ref,σ,baselineVector]; ring

theorem multiplier_bound (ε h a α W wL wR c η : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (ha : 0 ≤ a) (hα : 0 < α) (hL : 1 ≤ wL) (hR : 1 ≤ wR) (hW : wL ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖multiplier ε h a α W wL wR c η q x‖ ≤ 4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2) := by
  have hWp : 0 < W := by linarith
  have hm := multiplier_gaussian_bound ε h a α W wL wR c η hε hh ha hα hL hR hW q hq x
  have he : Real.exp (-(a/2)*q.re^2+4*a*h^2) ≤ Real.exp (4*a*h^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ha (sq_nonneg q.re)]
  have hrb : Real.exp (-(78/289:ℝ)*‖baselineVector ε α wL wR c (q.re:ℂ) x‖^2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)
  apply hm.trans
  calc
    _ ≤ (4*W)*(ε⁻¹*Real.exp (|h|/ε)*Real.exp (4*a*h^2))*1 := by
      apply mul_le_mul _ hrb (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

theorem bound_nonnegative (ε h a W : ℝ) (hε : 0 < ε) (hW : 0 ≤ W) :
    0 ≤ 4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2) := by positivity

#print axioms multiplier_mul_baseline
#print axioms multiplier_analytic
#print axioms multiplier_gaussian_bound
#print axioms multiplier_bound
#print axioms bound_nonnegative
end
end UnifiedTheory.Audit.KFCausalIndependentRadialHolomorphicQuotient
