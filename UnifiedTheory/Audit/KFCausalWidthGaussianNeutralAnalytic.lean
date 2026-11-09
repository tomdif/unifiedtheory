/- The neutral source-polynomial multiplier is genuinely holomorphic in
the clock coordinate and has the exact target/baseline factorization. -/
import UnifiedTheory.Audit.KFCausalWidthGaussianNeutralMultiplier
import Mathlib.Analysis.Analytic.Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 1024

namespace UnifiedTheory.Audit.KFCausalWidthGaussianNeutralMultiplier
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalComplexShearPerturbation (Space flow rotatedFlow)
open KFCausalPhysicalReciprocalNormalization (normalize coupling)
open KFCausalNormalizedComplexRotation (rotate rotationIsometry)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector targetVector)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalClockFloorCoherentStrip (clockPhase)

def numerator (ε h a α w c η : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (q : ℂ) (x : Joint 2 4) : ℂ :=
  (C*clockPhase p (complexInverse ε (shift h q)))*
    (P.eval (neutral ε h α w c η q x)*Complex.exp (b*neutral ε h α w c η q x))*
    KFCausalWidthGaussianHolomorphicQuotient.numerator ε h a α w c η q x

theorem multiplier_mul_baseline (ε h a α W w c η : ℝ) (hW : W ≠ 0)
    (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (q : ℂ) (x : Joint 2 4) :
    multiplier ε h a α W w c η C p b P q x*
      KFCausalWidthGaussianHolomorphicQuotient.baseline ε a α W w c q x=
      numerator ε h a α w c η C p b P q x := by
  unfold multiplier numerator
  rw [mul_assoc,KFCausalWidthGaussianHolomorphicQuotient.multiplier_mul_baseline
    ε h a α W w c η hW q x]

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

theorem neutral_analytic (ε h α w c η : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    AnalyticAt ℂ (fun z => neutral ε h α w c η z x) q := by
  have hm := KFCausalTwoShearClockQuotient.strip_membership ε h hε hh q hq
  have hs := KFCausalComplexClockInverse.complexInverse_analytic ε hε q hm.1
  have ht : AnalyticAt ℂ (fun z => complexInverse ε (shift h z)) q :=
    (KFCausalComplexClockInverse.complexInverse_analytic ε hε (shift h q) hm.2.1).comp
      (by unfold shift; fun_prop)
  have hy := analytic_flow (coupling α w) _ (fun _ => normalize α w c x) q hs
    (fun _ => analyticAt_const)
  have hz : ∀ i, AnalyticAt ℂ (fun z => targetVector ε h α w c η z x i) q :=
    analytic_rotate (-η) _ q (analytic_flow (coupling α w) _ _ q (ht.sub hs)
      (analytic_rotate η _ q hy))
  exact (hz 4).div_const

theorem multiplier_analytic (ε h a α W w c η : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hε : 0 < ε) (hh : |h| ≤ ε/10) (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    AnalyticAt ℂ (fun z => multiplier ε h a α W w c η C p b P z x) q := by
  have hn := neutral_analytic ε h α w c η hε hh q hq x
  have hp : AnalyticAt ℂ (fun z => P.eval (neutral ε h α w c η z x)) q :=
    (AnalyticOnNhd.eval_polynomial P _ (Set.mem_univ _)).comp hn
  have hm := KFCausalTwoShearClockQuotient.strip_membership ε h hε hh q hq
  have ht : AnalyticAt ℂ (fun z => complexInverse ε (shift h z)) q :=
    (KFCausalComplexClockInverse.complexInverse_analytic ε hε (shift h q) hm.2.1).comp
      (by unfold shift; fun_prop)
  have hphase : AnalyticAt ℂ (fun z => clockPhase p (complexInverse ε (shift h z))) q :=
    (analyticAt_const.mul ht).cexp
  exact ((analyticAt_const.mul hphase).mul (hp.mul (analyticAt_const.mul hn).cexp)).mul
    (KFCausalWidthGaussianHolomorphicQuotient.multiplier_analytic ε h a α W w c η hε hh q hq x)

#print axioms multiplier_mul_baseline
#print axioms neutral_analytic
#print axioms multiplier_analytic
end
end UnifiedTheory.Audit.KFCausalWidthGaussianNeutralMultiplier
