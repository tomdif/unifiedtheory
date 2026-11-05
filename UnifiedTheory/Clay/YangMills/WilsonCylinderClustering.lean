/- Uniform original open-cylinder correlation decay from its proved actual
conditional influences, product updates, reversibility and spatial locality. -/
import UnifiedTheory.Clay.YangMills.WilsonCylinderUpdateLocality
import UnifiedTheory.Clay.YangMills.ReversibleLocalClustering
import UnifiedTheory.Clay.YangMills.WilsonInteriorVacuum
import UnifiedTheory.Clay.YangMills.GibbsCrossCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCylinderClustering
noncomputable section
open MeasureTheory WilsonCylinderGeometry WilsonCylinderConditionalInfluence
open WilsonCylinderContraction WilsonCylinderUpdateLocality WilsonSingleLinkStaples
open ReversibleLocalClustering

variable (n L : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (Link n L) := Classical.decEq _

/-- Every input to the locality-to-clustering theorem is proved for this actual law. -/
theorem covariance_norm_bound (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F G : C(State n L, ℝ)) (A B : Finset (Link n L))
    (hF : DependsOn (F : State n L → ℝ) (A : Set (Link n L)))
    (hG : DependsOn (G : State n L → ℝ) (B : Set (Link n L)))
    (d : ℕ) (hsep : ∀ j, j < d → Disjoint (neighborhood n L A j) B) :
    |GibbsCrossCovariance.covariance (law n L β) F G| ≤
      rate β^d * ‖ContinuousMap.toLp 2 (law n L β) ℝ (centered (law n L β) F)‖ *
        ‖ContinuousMap.toLp 2 (law n L β) ℝ (centered (law n L β) G)‖ := by
  rw [GibbsCrossCovariance.covariance_eq_centered _ F G F.continuous G.continuous]
  exact ReversibleLocalClustering.covariance_norm_bound (law n L β) (update n L β heven)
    (update_stationary n L β heven) (rate β) (rate_nonneg β hβ)
    (centered_norm_contraction n L β hβ heven) (neighborhood n L)
    (fun F A hF k => iterate_dependsOn n L β hβ heven F A hF k)
    (fun F G A B hAB hF hG => disjoint_pairing_eq_update n L β heven A B hAB F G hF hG)
    F G A B hF hG d hsep

/-- The actual variances give the sharp standard-deviation prefactor. -/
theorem covariance_variance_bound (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F G : C(State n L, ℝ)) (A B : Finset (Link n L))
    (hF : DependsOn (F : State n L → ℝ) (A : Set (Link n L)))
    (hG : DependsOn (G : State n L → ℝ) (B : Set (Link n L)))
    (d : ℕ) (hsep : ∀ j, j < d → Disjoint (neighborhood n L A j) B) :
    |GibbsCrossCovariance.covariance (law n L β) F G| ≤
      rate β^d * Real.sqrt (∫ U, (F U - ∫ V, F V ∂law n L β)^2 ∂law n L β) *
        Real.sqrt (∫ U, (G U - ∫ V, G V ∂law n L β)^2 ∂law n L β) := by
  simpa only [centered_norm_eq_sqrt_variance] using
    covariance_norm_bound n L β hβ heven F G A B hF hG d hsep

/-- A finite prefactor uniform in both cylinder length and spatial volume. -/
theorem covariance_supnorm_bound (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F G : C(State n L, ℝ)) (A B : Finset (Link n L))
    (hF : DependsOn (F : State n L → ℝ) (A : Set (Link n L)))
    (hG : DependsOn (G : State n L → ℝ) (B : Set (Link n L)))
    (d : ℕ) (hsep : ∀ j, j < d → Disjoint (neighborhood n L A j) B) :
    |GibbsCrossCovariance.covariance (law n L β) F G| ≤
      (4 * ‖F‖ * ‖G‖) * rate β^d := by
  calc
    _ ≤ rate β^d * ‖ContinuousMap.toLp 2 (law n L β) ℝ (centered (law n L β) F)‖ *
        ‖ContinuousMap.toLp 2 (law n L β) ℝ (centered (law n L β) G)‖ :=
      covariance_norm_bound n L β hβ heven F G A B hF hG d hsep
    _ ≤ rate β^d * (2 * ‖F‖) * (2 * ‖G‖) := by
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left (centered_norm_le (law n L β) F)
          (pow_nonneg (rate_nonneg β hβ) d))
        (centered_norm_le (law n L β) G) (norm_nonneg _)
      exact mul_nonneg (pow_nonneg (rate_nonneg β hβ) d)
        (mul_nonneg (by norm_num) (norm_nonneg F))
    _ = _ := by ring

/-- A continuous spatial observable placed at one actual cylinder slice. -/
def sliceObservable (t : Fin (L + 1)) (F : C(WilsonSlabOperator.Slice n, ℝ)) :
    C(State n L, ℝ) :=
  ⟨fun U => F (spatialSlice n L U t), F.continuous.comp
    (continuous_pi (fun e => continuous_apply (Sum.inl (t, e))))⟩

omit [NeZero n] in
theorem sliceObservable_norm_le (t : Fin (L + 1)) (F : C(WilsonSlabOperator.Slice n, ℝ)) :
    ‖sliceObservable n L t F‖ ≤ ‖F‖ :=
  (ContinuousMap.norm_le (sliceObservable n L t F) (norm_nonneg F)).mpr
    (fun U => ContinuousMap.norm_coe_le_norm F (spatialSlice n L U t))

theorem slice_integral (β : ℝ) (t : Fin (L + 1)) (F : C(WilsonSlabOperator.Slice n, ℝ)) :
    (∫ U, sliceObservable n L t F U ∂law n L β) =
      ∫ z, F (z.1 t) ∂WilsonFiniteCylinder.law (n := n) character β 2 L :=
  WilsonCylinderCoordinates.integral_coordinates n L Q character character_continuous β 2
    (fun z => F (z.1 t))

theorem slice_product_integral (β : ℝ) (s t : Fin (L + 1))
    (F G : C(WilsonSlabOperator.Slice n, ℝ)) :
    (∫ U, sliceObservable n L s F U * sliceObservable n L t G U ∂law n L β) =
      ∫ z, F (z.1 s) * G (z.1 t) ∂WilsonFiniteCylinder.law (n := n) character β 2 L :=
  WilsonCylinderCoordinates.integral_coordinates n L Q character character_continuous β 2
    (fun z => F (z.1 s) * G (z.1 t))

/-- Ordinary time separation implies the proved graph-separation premise. -/
theorem slice_covariance_bound (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (s t : Fin (L + 1)) (F G : C(WilsonSlabOperator.Slice n, ℝ))
    (d : ℕ) (hgap : s.val + d ≤ t.val) :
    |GibbsCrossCovariance.covariance (law n L β)
      (sliceObservable n L s F) (sliceObservable n L t G)| ≤
        (4 * ‖F‖ * ‖G‖) * rate β^d := by
  have h := covariance_supnorm_bound n L β hβ heven
    (sliceObservable n L s F) (sliceObservable n L t G)
    (sliceSupport n L s) (sliceSupport n L t)
    (slice_observable_dependsOn n L s F) (slice_observable_dependsOn n L t G)
    d (fun j hj => sliceSupport_separation n L s t d j hgap hj)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg (rate_nonneg β hβ) d))
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (sliceObservable_norm_le n L s F) (by norm_num))
    (sliceObservable_norm_le n L t G) (norm_nonneg _) (by positivity)

omit L in
/-- The covariance in the already constructed raw-cylinder/vacuum dictionary
is exactly the covariance under its actual flattened Wilson law. -/
theorem interior_covariance_eq (β : ℝ) (j k : ℕ)
    (F G : C(WilsonSlabOperator.Slice n, ℝ)) :
    WilsonInteriorVacuum.covariance n β j k F G =
      GibbsCrossCovariance.covariance (law n (j + k + j) β)
        (sliceObservable n (j + k + j) (WilsonCylinderGluing.mark (j + k) j) F)
        (sliceObservable n (j + k + j) (WilsonCylinderGluing.secondMark j k j) G) := by
  unfold GibbsCrossCovariance.covariance
  rw [slice_product_integral, slice_integral, slice_integral]
  simp only [WilsonInteriorVacuum.covariance, WilsonInteriorVacuum.correlation,
    ContinuousMap.one_apply, mul_one, one_mul]

omit L in
/-- Uniform decay of actual interior connected correlations of the full Wilson cylinder. -/
theorem interior_covariance_bound (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F G : C(WilsonSlabOperator.Slice n, ℝ)) (j k : ℕ) :
    |WilsonInteriorVacuum.covariance n β j k F G| ≤ (4 * ‖F‖ * ‖G‖) * rate β^k := by
  rw [interior_covariance_eq]
  apply slice_covariance_bound n (j + k + j) β hβ heven _ _ F G k
  simp only [WilsonCylinderGluing.mark, WilsonCylinderGluing.secondMark]
  omega

end
end UnifiedTheory.Clay.YangMills.WilsonCylinderClustering
