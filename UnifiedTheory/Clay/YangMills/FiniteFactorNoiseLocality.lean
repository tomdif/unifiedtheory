/- Exact removed covariance locality for an arbitrary current finite-factor law.
The product conditional law is derived from independence in the current support
family. It therefore applies to computed induced factors at every finite depth. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorElimination
import UnifiedTheory.Clay.YangMills.GibbsCoordinateElimination
import UnifiedTheory.Clay.YangMills.CoordinateSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FiniteFactorNoiseLocality
noncomputable section
open MeasureTheory WilsonBlockMarginal CompactGibbsBlockUpdate
open FiniteFactorConditional GibbsCoordinateElimination

variable {I P X : Type*} [Fintype I] [Fintype P] [DecidableEq I]

/-- Only selected coordinates can vary within the conditional fiber. -/
def fiberSupport (T Q : Finset I) : Finset T := Finset.univ.filter (fun i => i.val ∈ Q)

omit [Fintype I] [Fintype P] in
theorem fiberSupport_disjoint (T Q R : Finset I) (h : Disjoint Q R) :
    Disjoint (fiberSupport T Q) (fiberSupport T R) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact Finset.disjoint_left.mp h (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

variable [MeasurableSpace X]

omit [Fintype I] [Fintype P] in
theorem fiber_dependsOn (T Q : Finset I) (F : (I → X) → ℝ)
    (hF : DependsOn F (Q : Set I)) (r : Outside (G := X) T) :
    DependsOn (fun V : Inside (G := X) T => F (assemble T (r, V)))
      (fiberSupport T Q : Set T) := by
  intro V W hVW
  apply hF
  intro i hiQ
  by_cases hiT : i ∈ T
  · rw [assemble_inside T _ i hiT, assemble_inside T _ i hiT]
    exact hVW ⟨i, hiT⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiQ⟩)
  · rw [assemble_outside T _ i hiT, assemble_outside T _ i hiT]

variable [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [Fintype I] in
/-- Actual conditional covariance cancellation for separated supported sources. -/
theorem conditional_zero (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : Finset I) (hT : Independent D T) (x₀ : X) (F G : C(I → X, ℝ))
    (Q R : Finset I) (hF : DependsOn F (Q : Set I)) (hG : DependsOn G (R : Set I))
    (hQR : Disjoint Q R) (r : Outside (G := X) T) :
    GibbsCrossCovariance.conditionalCovariance (insideMeasure T μ)
      (fun z : Outside (G := X) T × Inside (G := X) T => action Φ (assemble T z))
      (F.comp (join T)) (G.comp (join T)) r = 0 := by
  letI : Nonempty X := ⟨x₀⟩
  let U := assemble T (r, fun _ => x₀)
  let ν : T → Measure X := fun i => CompactGibbsContinuity.law μ
    (fun q => action Φ (Function.update U i.val q) - action Φ U)
  have hc : Continuous (action Φ) := action_continuous Φ hΦc
  have hν (i : T) : IsProbabilityMeasure (ν i) := by
    apply CompactGibbsContinuity.law_probability
    exact (hc.comp (update_continuous U i.val)).sub continuous_const
  letI : ∀ i, IsProbabilityMeasure (ν i) := hν
  have he (V : Inside (G := X) T) : replace T U V = assemble T (r, V) := by
    rw [FiniteFactorElimination.replace_eq_assemble]
    simp only [U, MeasurableEquiv.symm_apply_apply]
  have hprod : CompactGibbsContinuity.law (insideMeasure T μ)
      (fun V => action Φ (assemble T (r, V))) = Measure.pi ν := by
    calc
      _ = CompactGibbsContinuity.law (insideMeasure T μ)
          (fun V => action Φ (replace T U V)) := by
        congr 1
        funext V
        exact congrArg (action Φ) (he V).symm
      _ = _ := conditional_product_law μ D Φ hΦc hΦ T hT U
  unfold GibbsCrossCovariance.conditionalCovariance
  simp only [GibbsMarginalTower.response_eq_expectation (insideMeasure T μ)
    (fun z : Outside (G := X) T × Inside (G := X) T => action Φ (assemble T z)) _
    (hc.comp (assemble_continuous T)) r]
  rw [hprod]
  exact sub_eq_zero.mpr (CoordinateSupport.integral_mul_of_disjoint ν
    (fiberSupport T Q) (fiberSupport T R) (fiberSupport_disjoint T Q R hQR)
    (fun V => F (assemble T (r, V))) (fun V => G (assemble T (r, V)))
    (F.continuous.comp ((assemble_continuous T).comp
      (continuous_const.prodMk continuous_id)))
    (G.continuous.comp ((assemble_continuous T).comp
      (continuous_const.prodMk continuous_id)))
    (fiber_dependsOn T Q F hF r) (fiber_dependsOn T R G hG r))

/-- Locality of the literal pre-stage removed Gram under the actual current law. -/
theorem removedGram_zero (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : Finset I) (hT : Independent D T) (x₀ : X) (F G : C(I → X, ℝ))
    (Q R : Finset I) (hF : DependsOn F (Q : Set I)) (hG : DependsOn G (R : Set I))
    (hQR : Disjoint Q R) :
    removedGram μ T ⟨action Φ, action_continuous Φ hΦc⟩ F G = 0 := by
  rw [removedGram_eq, GibbsSuccessiveCovariance.gram_eq_conditional _ _ _ _ _
    ((⟨action Φ, action_continuous Φ hΦc⟩ : C(I → X, ℝ)).comp (join T)).continuous
    (F.comp (join T)).continuous (G.comp (join T)).continuous]
  apply integral_eq_zero_of_ae
  filter_upwards with r
  exact conditional_zero μ D Φ hΦc hΦ T hT x₀ F G Q R hF hG hQR r

end
end UnifiedTheory.Clay.YangMills.FiniteFactorNoiseLocality
