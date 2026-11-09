/- Joint horizontal continuity of the actual holomorphic Gaussian multiplier. -/
import UnifiedTheory.Audit.KFCausalWidthGaussianHolomorphicQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 1024

namespace UnifiedTheory.Audit.KFCausalWidthGaussianHolomorphicQuotient
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalClockFloorComplexDefect (complexClock)
open KFCausalComplexShearPerturbation (Space flow rotatedFlow)
open KFCausalPhysicalReciprocalNormalization (normalize weights coupling)
open KFCausalNormalizedComplexRotation (rotate rotationIsometry)
open KFCausalComplexQuadraticPerturbation (quadratic weightedQuadratic)
open KFCausalTwoShearClockQuotient (shift quotient)

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

private theorem continuous_rotate {T : Type*} [TopologicalSpace T] (η : ℝ)
    (g : T → Space) (hg : ∀ i, Continuous (fun z => g z i)) :
    ∀ i, Continuous (fun z => rotate η (g z) i) := by
  intro i
  fin_cases i <;> dsimp [rotate]
  · exact (continuous_const.mul (hg 0)).sub (continuous_const.mul (hg 2))
  · exact (continuous_const.mul (hg 1)).sub (continuous_const.mul (hg 3))
  · exact (continuous_const.mul (hg 0)).add (continuous_const.mul (hg 2))
  · exact (continuous_const.mul (hg 1)).add (continuous_const.mul (hg 3))
  · exact hg 4

theorem multiplier_horizontal_continuous (ε h a α W w c η : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (y : ℝ) (hy : |y| ≤ |h|) :
    Continuous (fun v : ℝ × Joint 2 4 =>
      multiplier ε h a α W w c η ((v.1:ℂ)+(y:ℂ)*Complex.I) v.2) := by
  let line : ℝ → ℂ := fun t => (t:ℂ)+(y:ℂ)*Complex.I
  have hl : Continuous line := by dsimp [line]; fun_prop
  have hline (t : ℝ) : |(line t).im| ≤ |h| := by simpa [line] using hy
  have hs : Continuous (fun t => complexInverse ε (line t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (KFCausalComplexClockInverse.complexInverse_analytic ε hε (line t)
      (KFCausalTwoShearClockQuotient.strip_membership ε h hε hh (line t) (hline t)).1).continuousAt.comp hl.continuousAt
  have ht : Continuous (fun t => complexInverse ε (shift h (line t))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hz : Continuous (fun t => shift h (line t)) := hl.sub continuous_const
    exact (KFCausalComplexClockInverse.complexInverse_analytic ε hε (shift h (line t))
      (KFCausalTwoShearClockQuotient.strip_membership ε h hε hh (line t) (hline t)).2.1).continuousAt.comp (f := fun t : ℝ => shift h (line t)) hz.continuousAt
  have hq : Continuous (fun t => quotient ε h a (line t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (KFCausalTwoShearClockQuotient.quotient_analytic ε h hε hh a
      (line t) (hline t)).continuousAt.comp hl.continuousAt
  have hn : ∀ i, Continuous (fun v : ℝ × Joint 2 4 => normalize α w c v.2 i) := by
    intro i
    have he (j : Fin 2 ⊕ Fin 4) : Continuous (fun v : ℝ × Joint 2 4 => v.2 j) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ⊕ Fin 4 => ℝ) j).comp continuous_snd
    fin_cases i <;> dsimp [KFCausalPhysicalReciprocalNormalization.normalize]
    all_goals exact Complex.continuous_ofReal.comp (continuous_const.mul (he _))
  let Y : ℝ × Joint 2 4 → Space := fun v => baselineVector ε α w c (line v.1) v.2
  have hyb' : ∀ i, Continuous (fun v => Y v i) := by
    exact continuous_flow (coupling α w)
      (fun v : ℝ × Joint 2 4 => complexInverse ε (line v.1))
      (fun v : ℝ × Joint 2 4 => normalize α w c v.2) (hs.comp continuous_fst) hn
  let Z : ℝ × Joint 2 4 → Space := fun v => rotate η (Y v)
  have hz : ∀ i, Continuous (fun v => Z v i) := continuous_rotate η Y hyb'
  let T : ℝ × Joint 2 4 → Space := fun v => flow (coupling α w)
    (complexInverse ε (shift h (line v.1))-complexInverse ε (line v.1)) (Z v)
  have ht' : ∀ i, Continuous (fun v => T v i) := continuous_flow (coupling α w)
    (fun v : ℝ × Joint 2 4 => complexInverse ε (shift h (line v.1))-complexInverse ε (line v.1))
    Z ((ht.comp continuous_fst).sub (hs.comp continuous_fst)) hz
  have hyt' : ∀ i, Continuous (fun v : ℝ × Joint 2 4 => targetVector ε h α w c η (line v.1) v.2 i) :=
    continuous_rotate (-η) T ht'
  change Continuous (fun v : ℝ × Joint 2 4 => multiplier ε h a α W w c η (line v.1) v.2)
  have hq' := hq.comp (continuous_fst : Continuous (Prod.fst : ℝ × Joint 2 4 → ℝ))
  have hty : Continuous (fun v : ℝ × Joint 2 4 => quadratic
      (fun i => targetVector ε h α w c η (line v.1) v.2 i)) := by
    unfold quadratic
    exact continuous_finset_sum _ (fun i _ => (hyt' i).pow 2)
  have hby : Continuous (fun v : ℝ × Joint 2 4 => weightedQuadratic (weights W w)
      (fun i => baselineVector ε α w c (line v.1) v.2 i)) := by
    unfold weightedQuadratic
    exact continuous_finset_sum _ (fun i _ => continuous_const.mul ((hyb' i).pow 2))
  exact (continuous_const.mul hq').mul (hty.neg.add hby).cexp

#print axioms multiplier_horizontal_continuous
end
end UnifiedTheory.Audit.KFCausalWidthGaussianHolomorphicQuotient
