/- A direct holomorphic multiplier for the width-one Gaussian and its
broader paired baseline. The real reference clock enters only the bound,
never the definition of the multiplier. -/
import UnifiedTheory.Audit.KFCausalNormalizedComplexRotation
import UnifiedTheory.Audit.KFCausalComplexShearGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 1024

namespace UnifiedTheory.Audit.KFCausalSingleGaussianHolomorphicQuotient
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalClockFloorComplexDefect (complexClock)
open KFCausalComplexShearPerturbation (Space flow rotatedFlow)
open KFCausalPhysicalReciprocalNormalization (normalize weights coupling)
open KFCausalNormalizedComplexRotation (rotate rotationIsometry)
open KFCausalComplexQuadraticPerturbation (quadratic weightedQuadratic)
open KFCausalTwoShearClockQuotient (shift quotient)

def baselineVector (ε α c : ℝ) (q : ℂ) (x : Joint 2 4) : Space :=
  flow (coupling α 1) (complexInverse ε q) (normalize α 1 c x)

def targetVector (ε h α c η : ℝ) (q : ℂ) (x : Joint 2 4) : Space :=
  rotatedFlow (rotationIsometry η) (coupling α 1)
    (complexInverse ε (shift h q)-complexInverse ε q) (baselineVector ε α c q x)

def baseline (ε a α c : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  ((Real.pi/(4*α):ℝ):ℂ)*Complex.exp (-complexInverse ε q)*
    Complex.exp (-((a/2:ℝ):ℂ)*q^2)*
    Complex.exp (-weightedQuadratic (weights 1 1) (fun i => baselineVector ε α c q x i))

def numerator (ε h a α c η : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  ((Real.pi/α:ℝ):ℂ)*(complexClock ε q)⁻¹*
    Complex.exp (-complexInverse ε (shift h q))*
    Complex.exp (-(a:ℂ)*(shift h q)^2)*
    Complex.exp (-quadratic (fun i => targetVector ε h α c η q x i))

def multiplier (ε h a α c η : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  (4:ℂ)*quotient ε h a q*
    Complex.exp (-quadratic (fun i => targetVector ε h α c η q x i)+
      weightedQuadratic (weights 1 1) (fun i => baselineVector ε α c q x i))

theorem multiplier_mul_baseline (ε h a α c η : ℝ) (q : ℂ) (x : Joint 2 4) :
    multiplier ε h a α c η q x * baseline ε a α c q x =
      numerator ε h a α c η q x := by
  have hp : (4:ℂ)*((Real.pi/(4*α):ℝ):ℂ)=((Real.pi/α:ℝ):ℂ) := by
    push_cast
    ring
  unfold multiplier baseline numerator quotient
  calc
    _ = ((4:ℂ)*((Real.pi/(4*α):ℝ):ℂ))*(complexClock ε q)⁻¹*
        Complex.exp ((complexInverse ε q-complexInverse ε (shift h q))+
          (-(a:ℂ)*(shift h q)^2+((a/2:ℝ):ℂ)*q^2)+
          (-quadratic (fun i => targetVector ε h α c η q x i)+
            weightedQuadratic (weights 1 1) (fun i => baselineVector ε α c q x i))+
          (-complexInverse ε q)+(-((a/2:ℝ):ℂ)*q^2)+
          (-weightedQuadratic (weights 1 1) (fun i => baselineVector ε α c q x i))) := by
      simp only [Complex.exp_add]
      ring
    _ = _ := by
      rw [hp,show (complexInverse ε q-complexInverse ε (shift h q))+
          (-(a:ℂ)*(shift h q)^2+((a/2:ℝ):ℂ)*q^2)+
          (-quadratic (fun i => targetVector ε h α c η q x i)+
            weightedQuadratic (weights 1 1) (fun i => baselineVector ε α c q x i))+
          (-complexInverse ε q)+(-((a/2:ℝ):ℂ)*q^2)+
          (-weightedQuadratic (weights 1 1) (fun i => baselineVector ε α c q x i)) =
          -complexInverse ε (shift h q)+(-(a:ℂ)*(shift h q)^2)+
            (-quadratic (fun i => targetVector ε h α c η q x i)) by ring]
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

private theorem analytic_vectors (ε h α c η : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    (∀ i, AnalyticAt ℂ (fun z => baselineVector ε α c z x i) q) ∧
    (∀ i, AnalyticAt ℂ (fun z => targetVector ε h α c η z x i) q) := by
  have hm := KFCausalTwoShearClockQuotient.strip_membership ε h hε hh q hq
  have hs := KFCausalComplexClockInverse.complexInverse_analytic ε hε q hm.1
  have ht : AnalyticAt ℂ (fun z => complexInverse ε (shift h z)) q :=
    (KFCausalComplexClockInverse.complexInverse_analytic ε hε (shift h q) hm.2.1).comp
      (by unfold shift; fun_prop)
  have hy := analytic_flow (coupling α 1) _ (fun _ => normalize α 1 c x) q hs
    (fun _ => analyticAt_const)
  refine ⟨hy,?_⟩
  exact analytic_rotate (-η) _ q (analytic_flow (coupling α 1) _ _ q (ht.sub hs)
    (analytic_rotate η _ q hy))

theorem multiplier_analytic (ε h a α c η : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    AnalyticAt ℂ (fun z => multiplier ε h a α c η z x) q := by
  obtain ⟨hy,ht⟩ := analytic_vectors ε h α c η hε hh q hq x
  have hqf := KFCausalTwoShearClockQuotient.quotient_analytic ε h hε hh a q hq
  have hty : AnalyticAt ℂ (fun z => quadratic (fun i => targetVector ε h α c η z x i)) q := by
    simp only [quadratic,Fin.sum_univ_succ,Fin.sum_univ_zero]
    exact ((ht 0).pow 2).add (((ht 1).pow 2).add (((ht 2).pow 2).add
      (((ht 3).pow 2).add (((ht 4).pow 2).add analyticAt_const))))
  have hby : AnalyticAt ℂ (fun z => weightedQuadratic (weights 1 1)
      (fun i => baselineVector ε α c z x i)) q := by
    simp only [weightedQuadratic,Fin.sum_univ_succ,Fin.sum_univ_zero]
    exact (analyticAt_const.mul ((hy 0).pow 2)).add
      ((analyticAt_const.mul ((hy 1).pow 2)).add
      ((analyticAt_const.mul ((hy 2).pow 2)).add
      ((analyticAt_const.mul ((hy 3).pow 2)).add
      ((analyticAt_const.mul ((hy 4).pow 2)).add analyticAt_const))))
  exact (analyticAt_const.mul hqf).mul (hty.neg.add hby).cexp

theorem multiplier_bound (ε h a α c η : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (ha : 0 ≤ a) (hα : 0 < α)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖multiplier ε h a α c η q x‖ ≤ 4*ε⁻¹*Real.exp (|h|/ε+4*a*h^2) := by
  let σ := coupling α 1
  let ref := flow σ (complexInverse ε (q.re:ℂ)) (normalize α 1 c x)
  let V : Space ≃ₗᵢ[ℂ] Space := LinearIsometryEquiv.refl ℂ Space
  have hr : ∀ i, (ref i).im=0 := by
    dsimp [ref]
    rw [KFCausalComplexClockInverse.complexInverse_real ε hε]
    exact KFCausalComplexShearGroup.flow_real σ _ _
      (KFCausalPhysicalReciprocalNormalization.normalize_real α 1 c x)
  have hb : rotatedFlow V σ (complexInverse ε q-complexInverse ε (q.re:ℂ)) ref =
      baselineVector ε α c q x := by
    change flow σ (complexInverse ε q-complexInverse ε (q.re:ℂ))
      (flow σ (complexInverse ε (q.re:ℂ)) (normalize α 1 c x)) = _
    rw [KFCausalComplexShearGroup.flow_compose,sub_add_cancel]
    rfl
  have hσ := KFCausalPhysicalReciprocalNormalization.coupling_bound α 1 hα (by norm_num)
  have hw := KFCausalPhysicalReciprocalNormalization.weights_bound 1 1 (by norm_num) (by norm_num)
  have hm := KFCausalTwoShearTransverseQuotient.clock_times_transverse_bound ε h hε hh
    a ha (rotationIsometry η) V σ hσ (weights 1 1) hw q hq ref hr
  simp only [KFCausalTwoShearTransverseQuotient.clockTransverse,
    KFCausalTwoShearTransverseQuotient.transverse,hb] at hm
  change ‖quotient ε h a q*Complex.exp (-quadratic (fun i => targetVector ε h α c η q x i)+
    weightedQuadratic (weights 1 1) (fun i => baselineVector ε α c q x i))‖ ≤ _ at hm
  have he : Real.exp (-(a/2)*q.re^2+4*a*h^2) ≤ Real.exp (4*a*h^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ha (sq_nonneg q.re)]
  have hrb : Real.exp (-(78/289:ℝ)*‖ref‖^2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)
  calc
    ‖multiplier ε h a α c η q x‖ = 4*‖quotient ε h a q*
        Complex.exp (-quadratic (fun i => targetVector ε h α c η q x i)+
          weightedQuadratic (weights 1 1) (fun i => baselineVector ε α c q x i))‖ := by
      simp [multiplier,mul_assoc]
    _ ≤ 4*((ε⁻¹*Real.exp (|h|/ε)*Real.exp (-(a/2)*q.re^2+4*a*h^2))*
        Real.exp (-(78/289:ℝ)*‖ref‖^2)) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ ≤ 4*((ε⁻¹*Real.exp (|h|/ε)*Real.exp (4*a*h^2))*1) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul _ hrb (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

theorem bound_nonnegative (ε h a : ℝ) (hε : 0 < ε) :
    0 ≤ 4*ε⁻¹*Real.exp (|h|/ε+4*a*h^2) := by positivity

#print axioms multiplier_mul_baseline
#print axioms multiplier_analytic
#print axioms multiplier_bound
#print axioms bound_nonnegative
end
end UnifiedTheory.Audit.KFCausalSingleGaussianHolomorphicQuotient
