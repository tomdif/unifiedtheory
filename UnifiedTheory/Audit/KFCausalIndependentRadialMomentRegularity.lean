/- Strip analyticity and joint horizontal continuity of the actual bare
radial/source multiplier, including every shifted field power. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentMultiplier
import Mathlib.Analysis.Analytic.Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalIndependentRadialMomentMultiplier
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalIndependentRadialNormalization (normalize weights)
open KFCausalIndependentRadialHolomorphicQuotient (baselineVector)
open KFCausalIndependentRadialMomentInput (left right neutral)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalPhysicalReciprocalNormalization (coupling)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalComplexQuadraticPerturbation (quadratic weightedQuadratic)

theorem multiplier_analytic (ε h a α W wL wR c : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (m n k : ℕ) (hε : 0 < ε) (hb : |h| ≤ ε/10)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    AnalyticAt ℂ (fun z => multiplier ε h a α W wL wR c C p b P m n k z x) q := by
  have hy := KFCausalIndependentRadialBareMultiplier.vector_analytic ε h α wL wR c hε hb q hq x
  have hl : AnalyticAt ℂ (fun z => left α wL (baselineVector ε α wL wR c z x)) q :=
    (((hy 0).pow 2).add ((hy 2).pow 2)).div_const
  have hr : AnalyticAt ℂ (fun z => right α wR (baselineVector ε α wL wR c z x)) q :=
    (((hy 1).pow 2).add ((hy 3).pow 2)).div_const
  have hn : AnalyticAt ℂ (fun z => neutral α (baselineVector ε α wL wR c z x)) q :=
    (hy 4).div_const
  have hp : AnalyticAt ℂ (fun z => P.eval (neutral α (baselineVector ε α wL wR c z x))) q :=
    (AnalyticOnNhd.eval_polynomial P _ (Set.mem_univ _)).comp hn
  have hs := KFCausalComplexClockInverse.complexInverse_analytic ε hε q
    (KFCausalTwoShearClockQuotient.strip_membership ε h hε hb q hq).1
  have hphase : AnalyticAt ℂ (fun z => clockPhase p (complexInverse ε z)) q :=
    (analyticAt_const.mul hs).cexp
  have hf := KFCausalIndependentRadialShiftedField.coefficient_analytic ε h α wL wR c hε hb q hq x
  have hg := KFCausalIndependentRadialBareMultiplier.multiplier_analytic ε h a α W wL wR c hε hb q hq x
  unfold multiplier
  exact (((((hf.pow k).mul (hl.pow m)).mul (hr.pow n)).mul
    (analyticAt_const.mul hphase)).mul (hp.mul (analyticAt_const.mul hn).cexp)).mul hg

private theorem continuous_flow {T : Type*} [TopologicalSpace T] (σ : ℝ)
    (f : T → ℂ) (g : T → Space) (hf : Continuous f)
    (hg : ∀ i, Continuous (fun z => g z i)) :
    ∀ i, Continuous (fun z => flow σ (f z) (g z) i) := by
  intro i
  fin_cases i <;> dsimp [flow]
  · exact (hf.neg.div_const 2).cexp.mul (hg 0)
  · exact (hf.neg.div_const 2).cexp.mul (hg 1)
  · exact (hf.div_const 2).cexp.mul (hg 2)
  · exact (hf.div_const 2).cexp.mul (hg 3)
  · exact (hg 4).add ((continuous_const.mul ((hf.div_const 2).cexp.sub continuous_const)).mul (hg 3))

private theorem vector_continuous_of_inverse {T : Type*} [TopologicalSpace T]
    (ε α wL wR c : ℝ) (q : T → ℂ) (x : T → Joint 2 4) (hx : Continuous x)
    (hs : Continuous (fun t => complexInverse ε (q t))) :
    ∀ i, Continuous (fun t => baselineVector ε α wL wR c (q t) (x t) i) := by
  have hn : ∀ i, Continuous (fun t => normalize α wL wR c (x t) i) := by
    intro i
    have he (j : Fin 2 ⊕ Fin 4) : Continuous (fun t => x t j) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ⊕ Fin 4 => ℝ) j).comp hx
    fin_cases i <;> dsimp [KFCausalIndependentRadialNormalization.normalize]
    all_goals exact Complex.continuous_ofReal.comp (continuous_const.mul (he _))
  exact continuous_flow (coupling α wR) _ _ hs hn

theorem multiplier_horizontal_continuous (ε h a α W wL wR c : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (m n k : ℕ) (hε : 0 < ε) (hb : |h| ≤ ε/10)
    (y : ℝ) (hy : |y| ≤ |h|) :
    Continuous (fun v : ℝ × Joint 2 4 =>
      multiplier ε h a α W wL wR c C p b P m n k ((v.1:ℂ)+(y:ℂ)*Complex.I) v.2) := by
  have hs : Continuous (fun t : ℝ => complexInverse ε ((t:ℂ)+(y:ℂ)*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hm := KFCausalTwoShearClockQuotient.strip_membership ε h hε hb
      ((t:ℂ)+(y:ℂ)*Complex.I) (by simpa using hy)
    have hl : Continuous (fun t : ℝ => (t:ℂ)+(y:ℂ)*Complex.I) := by fun_prop
    exact (KFCausalComplexClockInverse.complexInverse_analytic ε hε _ hm.1).continuousAt.comp
      (f := fun t : ℝ => (t:ℂ)+(y:ℂ)*Complex.I) hl.continuousAt
  have hY := vector_continuous_of_inverse ε α wL wR c
    (fun v : ℝ × Joint 2 4 => (v.1:ℂ)+(y:ℂ)*Complex.I) (fun v => v.2)
    continuous_snd (hs.comp continuous_fst)
  have hl : Continuous (fun v : ℝ × Joint 2 4 =>
      left α wL (baselineVector ε α wL wR c ((v.1:ℂ)+(y:ℂ)*Complex.I) v.2)) :=
    (((hY 0).pow 2).add ((hY 2).pow 2)).div_const _
  have hr : Continuous (fun v : ℝ × Joint 2 4 =>
      right α wR (baselineVector ε α wL wR c ((v.1:ℂ)+(y:ℂ)*Complex.I) v.2)) :=
    (((hY 1).pow 2).add ((hY 3).pow 2)).div_const _
  have hn : Continuous (fun v : ℝ × Joint 2 4 =>
      neutral α (baselineVector ε α wL wR c ((v.1:ℂ)+(y:ℂ)*Complex.I) v.2)) :=
    (hY 4).div_const _
  have hp := P.continuous.comp hn
  have hphase : Continuous (fun v : ℝ × Joint 2 4 =>
      clockPhase p (complexInverse ε ((v.1:ℂ)+(y:ℂ)*Complex.I))) :=
    (continuous_const.mul (hs.comp continuous_fst)).cexp
  have hqf : Continuous (fun v : ℝ × Joint 2 4 =>
      quadratic (fun i => baselineVector ε α wL wR c ((v.1:ℂ)+(y:ℂ)*Complex.I) v.2 i)) := by
    simp only [quadratic,Fin.sum_univ_succ,Fin.sum_univ_zero]
    exact ((hY 0).pow 2).add (((hY 1).pow 2).add (((hY 2).pow 2).add
      (((hY 3).pow 2).add (((hY 4).pow 2).add continuous_const))))
  have hwf : Continuous (fun v : ℝ × Joint 2 4 =>
      weightedQuadratic (weights W wL wR)
        (fun i => baselineVector ε α wL wR c ((v.1:ℂ)+(y:ℂ)*Complex.I) v.2 i)) := by
    simp only [weightedQuadratic,Fin.sum_univ_succ,Fin.sum_univ_zero]
    exact (continuous_const.mul ((hY 0).pow 2)).add
      ((continuous_const.mul ((hY 1).pow 2)).add
      ((continuous_const.mul ((hY 2).pow 2)).add
      ((continuous_const.mul ((hY 3).pow 2)).add
      ((continuous_const.mul ((hY 4).pow 2)).add continuous_const))))
  have hg : Continuous (fun v : ℝ × Joint 2 4 =>
      KFCausalIndependentRadialBareMultiplier.multiplier ε a α W wL wR c
        ((v.1:ℂ)+(y:ℂ)*Complex.I) v.2) := by
    unfold KFCausalIndependentRadialBareMultiplier.multiplier
    fun_prop
  have hf := KFCausalIndependentRadialShiftedField.coefficient_horizontal_continuous
    ε h α wL wR c hε hb y hy
  unfold multiplier
  exact (((((hf.pow k).mul (hl.pow m)).mul (hr.pow n)).mul
    (continuous_const.mul hphase)).mul (hp.mul (continuous_const.mul hn).cexp)).mul hg

#print axioms multiplier_analytic
#print axioms multiplier_horizontal_continuous
end
end UnifiedTheory.Audit.KFCausalIndependentRadialMomentMultiplier
