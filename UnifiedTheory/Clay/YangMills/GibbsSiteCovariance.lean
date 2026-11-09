/- Actual singleton conditional covariance and its random-site average.
The sharp factor 1/4 comes from the proved bounded-test covariance theorem. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.GibbsSiteCovariance
noncomputable section
open MeasureTheory CompactGibbsBlockUpdate CompactGibbsBlockFiber
open FiniteProductInfluence

variable {I X : Type*} [Fintype I] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- The probability law of the specified continuous action. -/
def law (A : C(I → X, ℝ)) : Measure (I → X) :=
  CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) A

instance law_probability (A : C(I → X, ℝ)) : IsProbabilityMeasure (law μ A) :=
  CompactGibbsContinuity.law_probability _ _ A.continuous

/-- Literal random singleton conditional expectation. -/
def update (A F : C(I → X, ℝ)) : C(I → X, ℝ) :=
  (Fintype.card I : ℝ)⁻¹ • ∑ i, blockAverage μ A {i} F

theorem update_apply (A F : C(I → X, ℝ)) (U : I → X) :
    update μ A F U = (Fintype.card I : ℝ)⁻¹ * ∑ i, blockAverage μ A {i} F U := by
  simp only [update, ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul]

theorem update_stationary [Nonempty I] (A F : C(I → X, ℝ)) :
    (∫ U, update μ A F U ∂law μ A) = ∫ U, F U ∂law μ A := by
  simp only [update_apply, integral_const_mul]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    (blockAverage μ A {i} F).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp_rw [law, blockAverage_stationary]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

/-- Dictionary with the proved product-update oscillation machinery, without a coloring premise. -/
theorem update_eq_colorAverage (A F : C(I → X, ℝ)) (U : I → X) :
    update μ A F U = ParallelOscillation.colorAverage
      (fun i V => CompactGibbsContinuity.law μ (fun q => A (Function.update V i q)))
      (id : I → I) F U := by
  let Φ : Unit → (I → X) → ℝ := fun _ => A
  have hA : FiniteFactorParallelKernel.actionMap Φ (fun _ => A.continuous) = A := by
    ext V
    simp [FiniteFactorParallelKernel.actionMap, FiniteFactorConditional.action, Φ]
  have hK : FiniteFactorInfluence.coordinateLaw μ Φ =
      (fun i V => CompactGibbsContinuity.law μ (fun q => A (Function.update V i q))) := by
    funext i V
    simp [FiniteFactorInfluence.coordinateLaw, FiniteFactorConditional.action, Φ]
  rw [update_apply]
  unfold ParallelOscillation.colorAverage
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hf : Finset.univ.filter (fun j : I => id j = i) = {i} := by ext j; simp
  rw [hf, ← hK, ← hA]
  apply FiniteFactorParallelKernel.blockAverage_eq_parallelAverage μ
    (fun _ : Unit => Finset.univ) Φ (fun _ => A.continuous)
  · intro p V W h
    exact congrArg A (funext (fun j => h j (Finset.mem_univ j)))
  · intro p j hj k hk _ _
    exact (Finset.mem_singleton.mp hj).trans (Finset.mem_singleton.mp hk).symm

/-- The integrated cross defect is exactly the averaged conditional covariance. -/
theorem cross_defect (A F G : C(I → X, ℝ)) (S : Finset I) :
    (∫ U, (F U - blockAverage μ A S F U) * G U ∂law μ A) =
      ∫ U, blockAverage μ A S (F * G) U -
        blockAverage μ A S F U * blockAverage μ A S G U ∂law μ A := by
  have hi (H : C(I → X, ℝ)) : Integrable H (law μ A) :=
    H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr := blockAverage_reversible μ A S (blockAverage μ A S F) G
  rw [blockAverage_idempotent] at hr
  simp_rw [sub_mul]
  have h₁ := integral_sub (hi (F * G)) (hi (blockAverage μ A S F * G))
  have h₂ := integral_sub (hi (blockAverage μ A S (F * G)))
    (hi (blockAverage μ A S F * blockAverage μ A S G))
  simp only [ContinuousMap.mul_apply] at h₁ h₂
  rw [h₁, h₂, law, blockAverage_stationary, hr]
  rfl

/-- A singleton fiber has exactly the two supplied coordinate oscillations. -/
theorem singleton_covariance_bound [Nonempty X] (A F G : C(I → X, ℝ))
    (d e : I → ℝ) (hF : OscBound F d) (hG : OscBound G e) (i : I) (U : I → X) :
    |blockAverage μ A {i} (F * G) U -
      blockAverage μ A {i} F U * blockAverage μ A {i} G U| ≤ d i * e i / 4 := by
  let O := overwrite ({i} : Finset I) U
  have hosc (H : C(I → X, ℝ)) (b : I → ℝ) (hH : OscBound H b) (V W : I → X) :
      |(H.comp O) V - (H.comp O) W| ≤ b i := by
    apply hH i
    intro j hj
    simp [O, overwrite, hj]
  obtain ⟨f, hf, hfb⟩ := ParallelOscillation.interval_of_oscillation (F.comp O) (d i)
    (hosc F d hF)
  obtain ⟨g, hg, hgb⟩ := ParallelOscillation.interval_of_oscillation (G.comp O) (e i)
    (hosc G e hG)
  let ν := CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) (A.comp O)
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability _ _ (A.comp O).continuous
  have h := CompactGibbsOscillation.covariance_bound ν (F.comp O) (G.comp O)
    (F.comp O).continuous (G.comp O).continuous f (f + d i) g (g + e i) hf hg hfb hgb
  simp only [add_sub_cancel_left] at h
  simpa only [blockAverage_full_fiber, ContinuousMap.mul_apply, ContinuousMap.comp_apply]
    using h

theorem singleton_defect_bound [Nonempty X] (A F G : C(I → X, ℝ))
    (d e : I → ℝ) (hF : OscBound F d) (hG : OscBound G e) (i : I) :
    |∫ U, (F U - blockAverage μ A {i} F U) * G U ∂law μ A| ≤ d i * e i / 4 := by
  rw [cross_defect]
  calc
    _ ≤ ∫ U, |blockAverage μ A {i} (F * G) U -
        blockAverage μ A {i} F U * blockAverage μ A {i} G U| ∂law μ A :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _U : I → X, d i * e i / 4 ∂law μ A := by
      apply integral_mono _ (integrable_const _) (singleton_covariance_bound μ A F G d e hF hG i)
      exact ((blockAverage μ A {i} (F * G) -
        blockAverage μ A {i} F * blockAverage μ A {i} G).continuous.abs
        ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    _ = _ := by simp

theorem update_defect_bound [Nonempty I] [Nonempty X] (A F G : C(I → X, ℝ))
    (d e : I → ℝ) (hF : OscBound F d) (hG : OscBound G e) :
    |∫ U, (F U - update μ A F U) * G U ∂law μ A| ≤
      (Fintype.card I : ℝ)⁻¹ * (∑ i, d i * e i) / 4 := by
  have he (U : I → X) : (F U - update μ A F U) * G U =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, (F U - blockAverage μ A {i} F U) * G U := by
    rw [update_apply, ← Finset.sum_mul, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp
  simp_rw [he]
  have hsum := integral_finset_sum Finset.univ (fun i _ =>
    ((F - blockAverage μ A {i} F) * G).continuous.integrable_of_hasCompactSupport
      (μ := law μ A) (HasCompactSupport.of_compactSpace _))
  simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply] at hsum
  rw [integral_const_mul, hsum, abs_mul, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ i,
        |∫ U, (F U - blockAverage μ A {i} F U) * G U ∂law μ A| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ i, d i * e i / 4 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum
        (fun i _ => singleton_defect_bound μ A F G d e hF hG i)) (by positivity)
    _ = _ := by rw [← Finset.sum_div]; ring

end
end UnifiedTheory.Clay.YangMills.GibbsSiteCovariance
