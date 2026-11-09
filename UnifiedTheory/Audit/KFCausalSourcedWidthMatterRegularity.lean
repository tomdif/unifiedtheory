/- Holomorphy and continuity of powers of the actual half-shifted matter
coordinate, retaining every neutral source and polynomial. -/
import UnifiedTheory.Audit.KFCausalSourcedWidthMatterMultiplier
import UnifiedTheory.Audit.KFCausalWidthGaussianNeutralContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalSourcedWidthMatterMultiplier
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalMatterInsertionCoordinate (coefficient halfScale)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector)
open KFCausalNormalizedComplexRotation (rotate rotationIsometry)
open KFCausalPhysicalReciprocalNormalization (normalize coupling)
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalTwoShearClockQuotient (shift)

theorem halfScale_analytic (ε h : ℝ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (q : ℂ) (hq : |q.im| ≤ |h|) : AnalyticAt ℂ (halfScale ε h) q := by
  have hs := KFCausalComplexClockInverse.complexInverse_analytic ε hε q
    (KFCausalTwoShearClockQuotient.strip_membership ε h hε hh q hq).1
  have ht : AnalyticAt ℂ (fun z => complexInverse ε (shift (h/2) z)) q :=
    (KFCausalComplexClockInverse.complexInverse_analytic ε hε _
      (half_shift_membership ε h hε hh q hq)).comp (by unfold shift; fun_prop)
  exact ((ht.sub hs).div_const).cexp

theorem coefficient_analytic (ε h α w c θ : ℝ)
    (hε : 0 < ε) (hh : |h| ≤ ε/10) (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    AnalyticAt ℂ (fun z => coefficient ε h α w c θ z x) q := by
  have hs := KFCausalComplexClockInverse.complexInverse_analytic ε hε q
    (KFCausalTwoShearClockQuotient.strip_membership ε h hε hh q hq).1
  have ht := halfScale_analytic ε h hε hh q hq
  simp_rw [coefficient,KFCausalPointFieldInsertionCoordinate.neutralCoefficient_eq_baseline,
    KFCausalSymmetricInsertionCoordinate.coefficient_eq_baseline,
    KFCausalNormalizedComplexRotation.rotationIsometry_apply]
  dsimp [KFCausalSymmetricInsertionCoordinate.coordinateIndex,rotate,baselineVector,flow]
  fun_prop

theorem multiplier_analytic (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k : ℕ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    AnalyticAt ℂ (fun z => multiplier ε h a α W w c θ C p b P k z x) q :=
  ((coefficient_analytic ε h α w c θ hε hh q hq x).pow k).mul
    (KFCausalWidthGaussianNeutralMultiplier.multiplier_analytic
      ε h a α W w c θ C p b P hε hh q hq x)

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

private theorem continuous_rotation {T : Type*} [TopologicalSpace T] (θ : T → ℝ) (g : T → Space)
    (hθ : Continuous θ) (hg : ∀ i, Continuous (fun t => g t i)) :
    ∀ i, Continuous (fun t => rotate (θ t) (g t) i) := by
  have hc := Complex.continuous_ofReal.comp (Real.continuous_cos.comp hθ)
  have hs := Complex.continuous_ofReal.comp (Real.continuous_sin.comp hθ)
  intro i
  fin_cases i <;> dsimp [rotate]
  · exact (hc.mul (hg 0)).sub (hs.mul (hg 2))
  · exact (hc.mul (hg 1)).sub (hs.mul (hg 3))
  · exact (hs.mul (hg 0)).add (hc.mul (hg 2))
  · exact (hs.mul (hg 1)).add (hc.mul (hg 3))
  · exact hg 4

private theorem coefficient_continuous_of_inverse {T : Type*} [TopologicalSpace T]
    (ε h α w c : ℝ) (θ : T → ℝ) (q : T → ℂ) (x : T → Joint 2 4)
    (hθ : Continuous θ) (hx : Continuous x)
    (hs : Continuous (fun t => complexInverse ε (q t)))
    (ht : Continuous (fun t => halfScale ε h (q t))) :
    Continuous (fun t => coefficient ε h α w c (θ t) (q t) (x t)) := by
  have hn : ∀ i, Continuous (fun t => normalize α w c (x t) i) := by
    intro i
    have he (j : Fin 2 ⊕ Fin 4) : Continuous (fun t => x t j) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ⊕ Fin 4 => ℝ) j).comp hx
    fin_cases i <;> dsimp [KFCausalPhysicalReciprocalNormalization.normalize]
    all_goals exact Complex.continuous_ofReal.comp (continuous_const.mul (he _))
  have hy : ∀ i, Continuous (fun t => baselineVector ε α w c (q t) (x t) i) :=
    continuous_flow (coupling α w) _ _ hs hn
  simp_rw [coefficient,KFCausalPointFieldInsertionCoordinate.neutralCoefficient_eq_baseline,
    KFCausalSymmetricInsertionCoordinate.coefficient_eq_baseline,
    KFCausalNormalizedComplexRotation.rotationIsometry_apply]
  exact ((hy 4).div_const _).add
    ((continuous_const.mul ((continuous_const.mul ht).sub continuous_const)).mul
      ((continuous_rotation θ _ hθ hy 3).div_const _))

theorem multiplier_horizontal_continuous (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k : ℕ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (y : ℝ) (hy : |y| ≤ |h|) :
    Continuous (fun v : ℝ × Joint 2 4 =>
      multiplier ε h a α W w c θ C p b P k ((v.1:ℂ)+(y:ℂ)*Complex.I) v.2) := by
  have hl : Continuous (fun t : ℝ => (t:ℂ)+(y:ℂ)*Complex.I) := by fun_prop
  have hs : Continuous (fun t : ℝ => complexInverse ε ((t:ℂ)+(y:ℂ)*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hm := KFCausalTwoShearClockQuotient.strip_membership ε h hε hh
      ((t:ℂ)+(y:ℂ)*Complex.I) (by simpa using hy)
    exact (KFCausalComplexClockInverse.complexInverse_analytic ε hε _ hm.1).continuousAt.comp
      (f := fun t : ℝ => (t:ℂ)+(y:ℂ)*Complex.I) hl.continuousAt
  have ht : Continuous (fun t : ℝ => halfScale ε h ((t:ℂ)+(y:ℂ)*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (halfScale_analytic ε h hε hh _ (by simpa using hy)).continuousAt.comp
      (f := fun t : ℝ => (t:ℂ)+(y:ℂ)*Complex.I) hl.continuousAt
  exact ((coefficient_continuous_of_inverse ε h α w c (fun _ => θ) _ _
    continuous_const continuous_snd (hs.comp continuous_fst) (ht.comp continuous_fst)).pow k).mul
    (KFCausalWidthGaussianNeutralMultiplier.multiplier_horizontal_continuous
      ε h a α W w c θ C p b P hε hh y hy)

theorem multiplier_angle_continuous (ε h a α W w c : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (k : ℕ) (q : ℂ) (x : Joint 2 4) :
    Continuous (fun θ => multiplier ε h a α W w c θ C p b P k q x) :=
  ((coefficient_continuous_of_inverse ε h α w c id (fun _ => q) (fun _ => x)
    continuous_id continuous_const continuous_const continuous_const).pow k).mul
    (KFCausalWidthGaussianNeutralMultiplier.multiplier_angle_continuous ε h a α W w c C p b P q x)

#print axioms halfScale_analytic
#print axioms coefficient_analytic
#print axioms multiplier_analytic
#print axioms multiplier_horizontal_continuous
#print axioms multiplier_angle_continuous
end
end UnifiedTheory.Audit.KFCausalSourcedWidthMatterMultiplier
