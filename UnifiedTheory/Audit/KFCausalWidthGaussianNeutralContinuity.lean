/- Horizontal and charge-angle continuity of the full sourced neutral
polynomial multiplier, with every inverse-clock premise discharged. -/
import UnifiedTheory.Audit.KFCausalWidthGaussianNeutralAnalytic
import UnifiedTheory.Audit.KFCausalWidthGaussianMixedSquareContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
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

private theorem continuous_rotation {T : Type*} [TopologicalSpace T] (η : T → ℝ) (g : T → Space)
    (hη : Continuous η) (hg : ∀ i, Continuous (fun θ => g θ i)) :
    ∀ i, Continuous (fun θ => rotate (η θ) (g θ) i) := by
  have hc := Complex.continuous_ofReal.comp (Real.continuous_cos.comp hη)
  have hs := Complex.continuous_ofReal.comp (Real.continuous_sin.comp hη)
  intro i
  fin_cases i <;> dsimp [rotate]
  · exact (hc.mul (hg 0)).sub (hs.mul (hg 2))
  · exact (hc.mul (hg 1)).sub (hs.mul (hg 3))
  · exact (hs.mul (hg 0)).add (hc.mul (hg 2))
  · exact (hs.mul (hg 1)).add (hc.mul (hg 3))
  · exact hg 4

theorem neutral_continuous_of_inverse {T : Type*} [TopologicalSpace T]
    (ε h α w c : ℝ) (η : T → ℝ) (q : T → ℂ) (x : T → Joint 2 4)
    (hη : Continuous η) (hx : Continuous x)
    (hs : Continuous (fun t => complexInverse ε (q t)))
    (ht : Continuous (fun t => complexInverse ε (shift h (q t)))) :
    Continuous (fun t => neutral ε h α w c (η t) (q t) (x t)) := by
  have hn : ∀ i, Continuous (fun t => normalize α w c (x t) i) := by
    intro i
    have he (j : Fin 2 ⊕ Fin 4) : Continuous (fun t => x t j) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ⊕ Fin 4 => ℝ) j).comp hx
    fin_cases i <;> dsimp [KFCausalPhysicalReciprocalNormalization.normalize]
    all_goals exact Complex.continuous_ofReal.comp (continuous_const.mul (he _))
  let Y : T → Space := fun t => baselineVector ε α w c (q t) (x t)
  have hy : ∀ i, Continuous (fun t => Y t i) :=
    continuous_flow (coupling α w) _ _ hs hn
  let Z : T → Space := fun t => rotate (η t) (Y t)
  have hz : ∀ i, Continuous (fun t => Z t i) := continuous_rotation η Y hη hy
  let U : T → Space := fun t => flow (coupling α w)
    (complexInverse ε (shift h (q t))-complexInverse ε (q t)) (Z t)
  have hu : ∀ i, Continuous (fun t => U t i) := continuous_flow (coupling α w) _ Z (ht.sub hs) hz
  have hv : ∀ i, Continuous (fun t => targetVector ε h α w c (η t) (q t) (x t) i) :=
    continuous_rotation (fun t => -η t) U hη.neg hu
  exact (hv 4).div_const _

private theorem shifted_inverse_line (ε h : ℝ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (y : ℝ) (hy : |y| ≤ |h|) :
    Continuous (fun t : ℝ => complexInverse ε (shift h ((t:ℂ)+(y:ℂ)*Complex.I))) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hm := KFCausalTwoShearClockQuotient.strip_membership ε h hε hh
    ((t:ℂ)+(y:ℂ)*Complex.I) (by simpa using hy)
  have hz : Continuous (fun t : ℝ => shift h ((t:ℂ)+(y:ℂ)*Complex.I)) := by unfold shift; fun_prop
  exact (KFCausalComplexClockInverse.complexInverse_analytic ε hε _ hm.2.1).continuousAt.comp
    (f := fun t : ℝ => shift h ((t:ℂ)+(y:ℂ)*Complex.I)) hz.continuousAt

theorem neutral_horizontal_continuous (ε h α w c η : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (y : ℝ) (hy : |y| ≤ |h|) :
    Continuous (fun v : ℝ × Joint 2 4 =>
      neutral ε h α w c η ((v.1:ℂ)+(y:ℂ)*Complex.I) v.2) := by
  have hs : Continuous (fun t : ℝ => complexInverse ε ((t:ℂ)+(y:ℂ)*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hm := KFCausalTwoShearClockQuotient.strip_membership ε h hε hh
      ((t:ℂ)+(y:ℂ)*Complex.I) (by simpa using hy)
    have hl : Continuous (fun t : ℝ => (t:ℂ)+(y:ℂ)*Complex.I) := by fun_prop
    exact (KFCausalComplexClockInverse.complexInverse_analytic ε hε _ hm.1).continuousAt.comp
      (f := fun t : ℝ => (t:ℂ)+(y:ℂ)*Complex.I) hl.continuousAt
  exact neutral_continuous_of_inverse ε h α w c (fun _ => η) _ _
    continuous_const continuous_snd (hs.comp continuous_fst)
    ((shifted_inverse_line ε h hε hh y hy).comp continuous_fst)

theorem multiplier_horizontal_continuous (ε h a α W w c η : ℝ)
    (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (y : ℝ) (hy : |y| ≤ |h|) :
    Continuous (fun v : ℝ × Joint 2 4 =>
      multiplier ε h a α W w c η C p b P ((v.1:ℂ)+(y:ℂ)*Complex.I) v.2) := by
  have hn := neutral_horizontal_continuous ε h α w c η hε hh y hy
  have hp := P.continuous.comp hn
  have ht := (shifted_inverse_line ε h hε hh y hy).comp
    (continuous_fst : Continuous (Prod.fst : ℝ × Joint 2 4 → ℝ))
  have hphase : Continuous (fun v : ℝ × Joint 2 4 =>
      clockPhase p (complexInverse ε (shift h ((v.1:ℂ)+(y:ℂ)*Complex.I)))) :=
    (continuous_const.mul ht).cexp
  exact ((continuous_const.mul hphase).mul (hp.mul (continuous_const.mul hn).cexp)).mul
    (KFCausalWidthGaussianHolomorphicQuotient.multiplier_horizontal_continuous ε h a α W w c η hε hh y hy)

theorem neutral_angle_continuous (ε h α w c : ℝ) (q : ℂ) (x : Joint 2 4) :
    Continuous (fun η => neutral ε h α w c η q x) :=
  neutral_continuous_of_inverse ε h α w c id (fun _ => q) (fun _ => x)
    continuous_id continuous_const continuous_const continuous_const

theorem multiplier_angle_continuous (ε h a α W w c : ℝ)
    (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (q : ℂ) (x : Joint 2 4) :
    Continuous (fun η => multiplier ε h a α W w c η C p b P q x) := by
  have hn := neutral_angle_continuous ε h α w c q x
  exact (continuous_const.mul ((P.continuous.comp hn).mul (continuous_const.mul hn).cexp)).mul
    (KFCausalWidthGaussianMixedSquareContinuity.holomorphic_multiplier_angle_continuous ε h a α W w c q x)

#print axioms neutral_continuous_of_inverse
#print axioms neutral_horizontal_continuous
#print axioms multiplier_horizontal_continuous
#print axioms neutral_angle_continuous
#print axioms multiplier_angle_continuous
end
end UnifiedTheory.Audit.KFCausalWidthGaussianNeutralMultiplier
