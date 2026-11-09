/- Quantitative source stability of the actual constrained minimizer.
This concerns minimizing configurations, not Gibbs expectations. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchMinimum

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchMinimumResponse
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonJointRotation WilsonPatchNeighborhood
open WilsonPatchMinimum WilsonBoundaryConnected
open WilsonSpatialCutEnergy
open scoped Quaternion RealInnerProductSpace

variable (n : ℕ) [NeZero n]

theorem distanceSq_symm (v w : Slice n) : distanceSq n v w = distanceSq n w v := by
  unfold distanceSq
  simp only [norm_sub_rev (v _ : ℍ) (w _ : ℍ)]

/-- The actual beta-scaled local insertion is Lipschitz in the full
configuration chord distance, with a constant independent of volume. -/
theorem source_difference_bound (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (hq : β * ‖(q : ℍ) - 1‖ ≤ 1)
    (u v w : Slice n) :
    (source n β e q u v - source n β e q u w) ^ 2 ≤ 4 * distanceSq n v w := by
  have he : ‖(v e : ℍ) - (w e : ℍ)‖ ^ 2 ≤ distanceSq n v w := by
    unfold distanceSq
    exact Finset.single_le_sum (f := fun b => ‖(v b : ℍ) - (w b : ℍ)‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ e)
  have hd := (QuaternionSymmetricChange.rotation q (u e)).1
  simp only [one_mul] at hd
  have hb : |source n β e q u v - source n β e q u w| ≤
      2 * ‖(v e : ℍ) - (w e : ℍ)‖ := by
    rw [WilsonTiltedMiddleAction.source_linear, WilsonTiltedMiddleAction.source_linear,
      ← mul_sub, ← inner_sub_right, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * β)]
    have hi := abs_real_inner_le_norm (((q * u e : Q) : ℍ) - (u e : ℍ))
      ((v e : ℍ) - (w e : ℍ))
    have hi' := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * β)
    have hd' := mul_le_mul_of_nonneg_left hd hβ
    have hcoeff : 2 * β * ‖((q * u e : Q) : ℍ) - (u e : ℍ)‖ ≤ 2 := by linarith
    have hh := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg ((v e : ℍ) - (w e : ℍ)))
    nlinarith only [hi', hh]
  have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity :
    0 ≤ 2 * ‖(v e : ℍ) - (w e : ℍ)‖)).mpr hb
  rw [sq_abs] at hh
  nlinarith only [hh, he]

/-- Strong midpoint growth for both tilted actions controls the distance
between their minimizers. No probabilistic assertion enters this estimate. -/
theorem minimum_source_stability (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε κ L : ℝ) (hε : ε ^ 2 < 2) (hκ : 0 < κ) (A F : Slice n → ℝ)
    (s t : ℝ) (v w : Slice n)
    (hv : v ∈ region n S v₀ ε) (hw : w ∈ region n S v₀ ε)
    (hvs : IsMinOn (CompactGibbsSource.action A F s) (region n S v₀ ε) v)
    (hwt : IsMinOn (CompactGibbsSource.action A F t) (region n S v₀ ε) w)
    (hs : ∀ m ∈ region n S v₀ ε, ∀ a : Slice n, (∀ e, e ∉ S → a e = 1) →
      κ * cost n a ≤ CompactGibbsSource.action A F s (a * m) +
        CompactGibbsSource.action A F s (a⁻¹ * m) - 2 * CompactGibbsSource.action A F s m)
    (ht : ∀ m ∈ region n S v₀ ε, ∀ a : Slice n, (∀ e, e ∉ S → a e = 1) →
      κ * cost n a ≤ CompactGibbsSource.action A F t (a * m) +
        CompactGibbsSource.action A F t (a⁻¹ * m) - 2 * CompactGibbsSource.action A F t m)
    (hF : (F v - F w) ^ 2 ≤ L ^ 2 * distanceSq n v w) :
    κ ^ 2 * distanceSq n v w ≤ 4 * L ^ 2 * (s - t) ^ 2 := by
  have h1 := minimum_growth n S v₀ ε κ hε hκ.le _ hs v hv hvs w hw
  have h2 := minimum_growth n S v₀ ε κ hε hκ.le _ ht w hw hwt v hv
  rw [← distanceSq_symm n v w] at h2
  simp only [CompactGibbsSource.action] at h1 h2
  have hd := distanceSq_nonneg n v w
  have hsum : κ / 2 * distanceSq n v w ≤ (s - t) * (F v - F w) := by
    nlinarith only [h1, h2]
  have hsquare := (sq_le_sq₀ (by positivity : 0 ≤ κ / 2 * distanceSq n v w)
    ((by positivity : 0 ≤ κ / 2 * distanceSq n v w).trans hsum)).mpr hsum
  have hf := mul_le_mul_of_nonneg_left hF (sq_nonneg (s - t))
  have hmul : (κ ^ 2 * distanceSq n v w) * distanceSq n v w ≤
      (4 * L ^ 2 * (s - t) ^ 2) * distanceSq n v w := by
    nlinarith only [hsquare, hf]
  rcases eq_or_lt_of_le hd with hz | hp
  · rw [← hz, mul_zero]
    positivity
  · exact (mul_le_mul_iff_left₀ hp).mp hmul

/-- Changing the transported source strength from h to k moves its actual
patch minimizer by at most 4*abs(h-k)/(2*beta-4) in total chord distance. -/
theorem transport_minimum_stability (β : ℝ) (hβ : 2 < β) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r p : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (hp : β * ‖(p : ℍ) - 1‖ ≤ 1)
    (s t h k : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (hk : k ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ v z : Slice n)
    (hflat : ∀ a c, c ∈ S → c ∈ support n a →
      ‖((spatialHolonomy v₀ a.1 a.2.1.1 a.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 64)
    (hu : ∀ c ∈ S, ‖(v₀ c : ℍ) - (u c : ℍ)‖ ≤ 1 / 2)
    (hw : ∀ c ∈ S, ‖(v₀ c : ℍ) - (w c : ℍ)‖ ≤ 1 / 2)
    (hv : v ∈ region n S v₀ (1 / 256)) (hz : z ∈ region n S v₀ (1 / 256))
    (hminv : IsMinOn (CompactGibbsSource.action
      (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w) h)
      (region n S v₀ (1 / 256)) v)
    (hminz : IsMinOn (CompactGibbsSource.action
      (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w) k)
      (region n S v₀ (1 / 256)) z) :
    (2 * β - 4) ^ 2 * distanceSq n v z ≤ 16 * (h - k) ^ 2 := by
  have hg := minimum_source_stability n S v₀ (1 / 256) (2 * β - 4) 2
    (by norm_num) (by linarith) _ (source n β b p w) h k v z hv hz hminv hminz
    (fun m hm a ha => WilsonPatchSourceCurvature.transport_second_patch n β (by linarith)
      u w e d b hed q r p hq hr hp s t h hs ht hh S v₀ m a hm ha hflat hu hw)
    (fun m hm a ha => WilsonPatchSourceCurvature.transport_second_patch n β (by linarith)
      u w e d b hed q r p hq hr hp s t k hs ht hk S v₀ m a hm ha hflat hu hw)
    (by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
      source_difference_bound n β (by linarith) b p hp w v z)
  norm_num at hg ⊢
  exact hg

end
end UnifiedTheory.Clay.YangMills.WilsonPatchMinimumResponse
