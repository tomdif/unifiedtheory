/- A proved covariance bound for the actual sourced Wilson law restricted
to a fixed Haar chord patch. It scales with patch cardinality, not separation;
the full unconditioned boundary covariance is a separate obligation. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchFluctuation
import UnifiedTheory.Clay.YangMills.WilsonIndependentVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchCovariance
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonBoundaryConnected
open WilsonSpatialCutEnergy WilsonPatchNeighborhood WilsonChordPatchLaw GibbsCrossCovariance
open scoped Quaternion

section Moment
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem covariance_moment_bound (F G : X → ℝ) (hF : Continuous F) (hG : Continuous G)
    (c d B : ℝ) (hF2 : (∫ x, (F x - c) ^ 2 ∂μ) ≤ B)
    (hG2 : (∫ x, (G x - d) ^ 2 ∂μ) ≤ B) : |covariance μ F G| ≤ B := by
  have hFF := WilsonIndependentVariance.covariance_le_square_shift μ F hF c |>.trans hF2
  have hGG := WilsonIndependentVariance.covariance_le_square_shift μ G hG d |>.trans hG2
  have heF : (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) = covariance μ F F := by
    rw [covariance_eq_centered μ F F hF hF]
    simp only [pow_two]
  have heG : (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) = covariance μ G G := by
    rw [covariance_eq_centered μ G G hG hG]
    simp only [pow_two]
  have h0F : 0 ≤ covariance μ F F := by
    rw [← heF]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have h0G : 0 ≤ covariance μ G G := by
    rw [← heG]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hcs := CompactDensityEntropy.integral_product_sq μ
    (fun x => F x - ∫ y, F y ∂μ) (fun x => G x - ∫ y, G y ∂μ)
    (hF.sub continuous_const) (hG.sub continuous_const)
  rw [← covariance_eq_centered μ F G hF hG, heF, heG] at hcs
  have hb := mul_le_mul hFF hGG h0G (h0F.trans hFF)
  apply (sq_le_sq₀ (abs_nonneg _) (h0F.trans hFF)).mp
  rw [sq_abs]
  nlinarith only [hcs, hb]
end Moment

variable (n : ℕ) [NeZero n]

theorem source_second_moment (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : 0 < ε) (A : Slice n → ℝ) (hA : Continuous A)
    (β : ℝ) (hβ : 0 ≤ β) (b : SpatialVertex n × Fin 3) (p : Q)
    (hp : β * ‖(p : ℍ) - 1‖ ≤ 1) (u v : Slice n) :
    (∫ x, (source n β b p u (assemble n S v₀ ε x) - source n β b p u v) ^ 2
      ∂law n S v₀ ε A) ≤
      4 * ∫ x, distanceSq n v (assemble n S v₀ ε x) ∂law n S v₀ ε A := by
  letI := law_probability n S v₀ ε hε A hA
  have hc := (source_continuous n β b p u).comp (assemble_continuous n S v₀ ε)
  have hd := (WilsonPatchFluctuation.distance_continuous n v).comp
    (assemble_continuous n S v₀ ε)
  rw [← integral_const_mul]
  apply integral_mono
    (((hc.sub continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((continuous_const.mul hd).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  intro x
  have hh := WilsonPatchMinimumResponse.source_difference_bound
    n β hβ b p hp u v (assemble n S v₀ ε x)
  dsimp only [Function.comp_apply, Pi.mul_apply]
  nlinarith only [hh]

/-- The actual two original insertions have a quantitative connected
covariance bound under the normalized patch law, throughout their rectangle. -/
theorem connected_bound (β : ℝ) (hβ : 1 < β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (hflat : ∀ p b, b ∈ S → b ∈ support n p →
      ‖((spatialHolonomy v₀ p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 64)
    (hu : ∀ b ∈ S, ‖(v₀ b : ℍ) - (u b : ℍ)‖ ≤ 1 / 2)
    (hw : ∀ b ∈ S, ‖(v₀ b : ℍ) - (w b : ℍ)‖ ≤ 1 / 2) :
    |covariance (law n S v₀ (1 / 256) (WilsonTiltedMiddleAction.action n β u w e d q r s t))
      (fun x => source n β e q u (assemble n S v₀ (1 / 256) x))
      (fun x => source n β d r u (assemble n S v₀ (1 / 256) x))| ≤
      8 * (S.card : ℝ) * Real.log 81 / (β - 1) := by
  obtain ⟨v, _, _, hmean⟩ := WilsonPatchFluctuation.action_fluctuation n β hβ u w e d hed
    q r hq hr s t hs ht S v₀ hflat hu hw
  let A := WilsonTiltedMiddleAction.action n β u w e d q r s t
  have hA : Continuous A := WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t
  letI := law_probability n S v₀ (1 / 256) (by norm_num) A hA
  apply covariance_moment_bound _ _ _
    ((source_continuous n β e q u).comp (assemble_continuous n S v₀ (1 / 256)))
    ((source_continuous n β d r u).comp (assemble_continuous n S v₀ (1 / 256)))
    (source n β e q u v) (source n β d r u v)
  · have hh := (source_second_moment n S v₀ (1 / 256) (by norm_num) A hA
      β (by linarith) e q hq u v).trans
      (mul_le_mul_of_nonneg_left hmean (by norm_num : (0 : ℝ) ≤ 4))
    convert hh using 1
    ring
  · have hh := (source_second_moment n S v₀ (1 / 256) (by norm_num) A hA
      β (by linarith) d r hr u v).trans
      (mul_le_mul_of_nonneg_left hmean (by norm_num : (0 : ℝ) ≤ 4))
    convert hh using 1
    ring

/-- The covariance appearing in retained-response transport is bounded
under the corresponding three-source patch law, including overlapping links. -/
theorem transport_connected_bound (β : ℝ) (hβ : 2 < β) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r p : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (hp : β * ‖(p : ℍ) - 1‖ ≤ 1)
    (s t h : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hh : h ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (hflat : ∀ z c, c ∈ S → c ∈ support n z →
      ‖((spatialHolonomy v₀ z.1 z.2.1.1 z.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 64)
    (hu : ∀ c ∈ S, ‖(v₀ c : ℍ) - (u c : ℍ)‖ ≤ 1 / 2)
    (hw : ∀ c ∈ S, ‖(v₀ c : ℍ) - (w c : ℍ)‖ ≤ 1 / 2) :
    |covariance (law n S v₀ (1 / 256) (CompactGibbsSource.action
        (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w) h))
      (fun x => source n β e q u (assemble n S v₀ (1 / 256) x))
      (fun x => source n β b p w (assemble n S v₀ (1 / 256) x))| ≤
      8 * (S.card : ℝ) * Real.log 81 / (β - 2) := by
  obtain ⟨v, _, _, hmean⟩ := WilsonPatchFluctuation.transport_fluctuation n β hβ u w
    e d b hed q r p hq hr hp s t h hs ht hh S v₀ hflat hu hw
  let A := CompactGibbsSource.action
    (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w) h
  have hA : Continuous A := CompactGibbsSource.action_continuous _ _
    (WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t)
    (source_continuous n β b p w) h
  letI := law_probability n S v₀ (1 / 256) (by norm_num) A hA
  apply covariance_moment_bound _ _ _
    ((source_continuous n β e q u).comp (assemble_continuous n S v₀ (1 / 256)))
    ((source_continuous n β b p w).comp (assemble_continuous n S v₀ (1 / 256)))
    (source n β e q u v) (source n β b p w v)
  · have hg := (source_second_moment n S v₀ (1 / 256) (by norm_num) A hA
      β (by linarith) e q hq u v).trans
      (mul_le_mul_of_nonneg_left hmean (by norm_num : (0 : ℝ) ≤ 4))
    convert hg using 1
    ring
  · have hg := (source_second_moment n S v₀ (1 / 256) (by norm_num) A hA
      β (by linarith) b p hp w v).trans
      (mul_le_mul_of_nonneg_left hmean (by norm_num : (0 : ℝ) ≤ 4))
    convert hg using 1
    ring

end
end UnifiedTheory.Clay.YangMills.WilsonPatchCovariance
