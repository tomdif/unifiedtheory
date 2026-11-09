/- Continuity of the actual symmetric derivative data, both along clock
lines with transverse variables and in the physical charge angle. -/
import UnifiedTheory.Audit.KFCausalSymmetricDirectionBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalSymmetricDirectionRegularity
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalComplexShearPerturbation (Space flow rotatedFlow)
open KFCausalPhysicalReciprocalNormalization (coupling)
open KFCausalNormalizedComplexRotation (rotate rotationIsometry)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector targetVector)
open KFCausalSymmetricNormalizedDirection (direction targetDirection)
open KFCausalSymmetricInsertionAffine (neutralSlope matterSlope matter_eq_baseline)
open KFCausalMatterInsertionCoordinate (coefficient halfScale)
open KFCausalTwoShearClockQuotient (shift)

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

private theorem baseline_continuous {T : Type*} [TopologicalSpace T]
    (ε α w c : ℝ) (q : T → ℂ) (x : T → Joint 2 4) (hx : Continuous x)
    (hs : Continuous (fun t => complexInverse ε (q t))) :
    ∀ i, Continuous (fun t => baselineVector ε α w c (q t) (x t) i) := by
  have hn : ∀ i, Continuous (fun t => KFCausalPhysicalReciprocalNormalization.normalize α w c (x t) i) := by
    intro i
    have he (j : Fin 2 ⊕ Fin 4) : Continuous (fun t => x t j) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ⊕ Fin 4 => ℝ) j).comp hx
    fin_cases i <;> dsimp [KFCausalPhysicalReciprocalNormalization.normalize]
    all_goals exact Complex.continuous_ofReal.comp (continuous_const.mul (he _))
  exact continuous_flow (coupling α w) _ _ hs hn

private theorem target_continuous {T : Type*} [TopologicalSpace T]
    (ε h α w c : ℝ) (θ : T → ℝ) (q : T → ℂ) (x : T → Joint 2 4)
    (hθ : Continuous θ) (hx : Continuous x)
    (hs : Continuous (fun t => complexInverse ε (q t)))
    (ht : Continuous (fun t => complexInverse ε (shift h (q t)))) :
    ∀ i, Continuous (fun t => targetVector ε h α w c (θ t) (q t) (x t) i) := by
  have hy := baseline_continuous ε α w c q x hx hs
  have hr := continuous_rotation θ _ hθ hy
  have hf := continuous_flow (coupling α w) _ _ (ht.sub hs) hr
  exact continuous_rotation (fun t => -θ t) _ hθ.neg hf

private theorem targetDirection_continuous {T : Type*} [TopologicalSpace T]
    (ε h α w : ℝ) (i : Fin 2) (θ : T → ℝ) (q : T → ℂ)
    (hθ : Continuous θ) (hs : Continuous (fun t => complexInverse ε (q t)))
    (ht : Continuous (fun t => complexInverse ε (shift h (q t)))) :
    ∀ j, Continuous (fun t => targetDirection ε h α w (θ t) i (q t) j) := by
  have hr := continuous_rotation θ (fun _ => direction α w i) hθ (fun _ => continuous_const)
  have hf := continuous_flow (coupling α w) _ _ (ht.sub hs) hr
  exact continuous_rotation (fun t => -θ t) _ hθ.neg hf

private theorem matter_continuous {T : Type*} [TopologicalSpace T]
    (ε h α w c : ℝ) (θ : T → ℝ) (q : T → ℂ) (x : T → Joint 2 4)
    (hθ : Continuous θ) (hx : Continuous x)
    (hs : Continuous (fun t => complexInverse ε (q t)))
    (ht : Continuous (fun t => halfScale ε h (q t))) :
    Continuous (fun t => coefficient ε h α w c (θ t) (q t) (x t)) := by
  have hy := baseline_continuous ε α w c q x hx hs
  simp_rw [matter_eq_baseline,KFCausalNormalizedComplexRotation.rotationIsometry_apply]
  exact ((hy 4).div_const _).add
    ((continuous_const.mul ((continuous_const.mul ht).sub continuous_const)).mul
      ((continuous_rotation θ _ hθ hy 3).div_const _))

private theorem matterSlope_continuous {T : Type*} [TopologicalSpace T]
    (ε h α w : ℝ) (i : Fin 2) (θ : T → ℝ) (q : T → ℂ)
    (hθ : Continuous θ) (ht : Continuous (fun t => halfScale ε h (q t))) :
    Continuous (fun t => matterSlope ε h α w (θ t) i (q t)) := by
  have hr := continuous_rotation θ (fun _ => direction α w i) hθ (fun _ => continuous_const)
  exact continuous_const.add
    ((continuous_const.mul ((continuous_const.mul ht).sub continuous_const)).mul ((hr 3).div_const _))

private theorem inverse_lines (ε h : ℝ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (y : ℝ) (hy : |y| ≤ |h|) :
    Continuous (fun t : ℝ => complexInverse ε ((t:ℂ)+(y:ℂ)*Complex.I)) ∧
    Continuous (fun t : ℝ => complexInverse ε (shift h ((t:ℂ)+(y:ℂ)*Complex.I))) ∧
    Continuous (fun t : ℝ => halfScale ε h ((t:ℂ)+(y:ℂ)*Complex.I)) := by
  have hl : Continuous (fun t : ℝ => (t:ℂ)+(y:ℂ)*Complex.I) := by fun_prop
  have hs : Continuous (fun t : ℝ => shift h ((t:ℂ)+(y:ℂ)*Complex.I)) := by unfold shift; fun_prop
  refine ⟨?_,?_,?_⟩
  · apply continuous_iff_continuousAt.mpr
    intro t
    exact (KFCausalComplexClockInverse.complexInverse_analytic ε hε _
      (KFCausalTwoShearClockQuotient.strip_membership ε h hε hh _ (by simpa using hy)).1).continuousAt.comp
        (f := fun t : ℝ => (t:ℂ)+(y:ℂ)*Complex.I) hl.continuousAt
  · apply continuous_iff_continuousAt.mpr
    intro t
    exact (KFCausalComplexClockInverse.complexInverse_analytic ε hε _
      (KFCausalTwoShearClockQuotient.strip_membership ε h hε hh _ (by simpa using hy)).2.1).continuousAt.comp
        (f := fun t : ℝ => shift h ((t:ℂ)+(y:ℂ)*Complex.I)) hs.continuousAt
  · apply continuous_iff_continuousAt.mpr
    intro t
    exact (KFCausalSourcedWidthMatterMultiplier.halfScale_analytic ε h hε hh _ (by simpa using hy)).continuousAt.comp
      (f := fun t : ℝ => (t:ℂ)+(y:ℂ)*Complex.I) hl.continuousAt

theorem targetVector_horizontal_continuous (ε h α w c θ : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (y : ℝ) (hy : |y| ≤ |h|) :
    ∀ j, Continuous (fun z : ℝ × Joint 2 4 =>
      targetVector ε h α w c θ ((z.1:ℂ)+(y:ℂ)*Complex.I) z.2 j) := by
  have hl := inverse_lines ε h hε hh y hy
  exact target_continuous ε h α w c (fun _ => θ) _ _ continuous_const continuous_snd
    (hl.1.comp continuous_fst) (hl.2.1.comp continuous_fst)

theorem targetVector_angle_continuous (ε h α w c : ℝ) (q : ℂ) (x : Joint 2 4) :
    ∀ j, Continuous (fun θ : ℝ => targetVector ε h α w c θ q x j) := by
  intro j
  exact target_continuous ε h α w c (fun θ : ℝ => θ)
    (fun _ : ℝ => q) (fun _ : ℝ => x)
    continuous_id continuous_const continuous_const continuous_const j

theorem matter_horizontal_continuous (ε h α w c θ : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (y : ℝ) (hy : |y| ≤ |h|) :
    Continuous (fun z : ℝ × Joint 2 4 => coefficient ε h α w c θ ((z.1:ℂ)+(y:ℂ)*Complex.I) z.2) := by
  have hl := inverse_lines ε h hε hh y hy
  exact matter_continuous ε h α w c (fun _ => θ) _ _ continuous_const continuous_snd
    (hl.1.comp continuous_fst) (hl.2.2.comp continuous_fst)

theorem matter_angle_continuous (ε h α w c : ℝ) (q : ℂ) (x : Joint 2 4) :
    Continuous (fun θ => coefficient ε h α w c θ q x) :=
  matter_continuous ε h α w c id (fun _ => q) (fun _ => x)
    continuous_id continuous_const continuous_const continuous_const

theorem targetDirection_horizontal_continuous (ε h α w θ : ℝ) (i : Fin 2) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (y : ℝ) (hy : |y| ≤ |h|) :
    ∀ j, Continuous (fun t : ℝ => targetDirection ε h α w θ i ((t:ℂ)+(y:ℂ)*Complex.I) j) := by
  have hl := inverse_lines ε h hε hh y hy
  exact targetDirection_continuous ε h α w i (fun _ => θ) _ continuous_const hl.1 hl.2.1

theorem targetDirection_angle_continuous (ε h α w : ℝ) (i : Fin 2) (q : ℂ) :
    ∀ j, Continuous (fun θ => targetDirection ε h α w θ i q j) :=
  targetDirection_continuous ε h α w i id (fun _ => q) continuous_id continuous_const continuous_const

theorem neutralSlope_horizontal_continuous (ε h α w θ : ℝ) (i : Fin 2) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (y : ℝ) (hy : |y| ≤ |h|) :
    Continuous (fun t : ℝ => neutralSlope ε h α w θ i ((t:ℂ)+(y:ℂ)*Complex.I)) :=
  (targetDirection_horizontal_continuous ε h α w θ i hε hh y hy 4).div_const _

theorem neutralSlope_angle_continuous (ε h α w : ℝ) (i : Fin 2) (q : ℂ) :
    Continuous (fun θ => neutralSlope ε h α w θ i q) :=
  (targetDirection_angle_continuous ε h α w i q 4).div_const _

theorem matterSlope_horizontal_continuous (ε h α w θ : ℝ) (i : Fin 2) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (y : ℝ) (hy : |y| ≤ |h|) :
    Continuous (fun t : ℝ => matterSlope ε h α w θ i ((t:ℂ)+(y:ℂ)*Complex.I)) :=
  matterSlope_continuous ε h α w i (fun _ => θ) _ continuous_const (inverse_lines ε h hε hh y hy).2.2

theorem matterSlope_angle_continuous (ε h α w : ℝ) (i : Fin 2) (q : ℂ) :
    Continuous (fun θ => matterSlope ε h α w θ i q) :=
  matterSlope_continuous ε h α w i id (fun _ => q) continuous_id continuous_const

#print axioms targetVector_horizontal_continuous
#print axioms targetVector_angle_continuous
#print axioms matter_horizontal_continuous
#print axioms matter_angle_continuous
#print axioms targetDirection_horizontal_continuous
#print axioms targetDirection_angle_continuous
#print axioms neutralSlope_horizontal_continuous
#print axioms neutralSlope_angle_continuous
#print axioms matterSlope_horizontal_continuous
#print axioms matterSlope_angle_continuous
end
end UnifiedTheory.Audit.KFCausalSymmetricDirectionRegularity
