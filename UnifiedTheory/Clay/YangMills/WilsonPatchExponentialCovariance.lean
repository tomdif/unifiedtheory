/- The actual unrestricted interior covariance now has an explicit
exponential cap-complement term. Retained exterior and endpoint
covariances, and spatial-separation decay, remain separate obligations. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchComplementTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchExponentialCovariance
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonBoundaryConnected WilsonSpatialCutEnergy
open WilsonPatchConditioning WilsonPatchComplementTail GibbsCrossCovariance
open scoped Quaternion

variable (n : ℕ) [NeZero n]

theorem connected_bound (β : ℝ) (hβ : 1 < β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (hflat : ∀ p b, b ∈ S → b ∈ support n p →
      ‖((spatialHolonomy v₀ p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 64)
    (hu : ∀ b ∈ S, ‖(v₀ b : ℍ) - (u b : ℍ)‖ ≤ 1 / 2)
    (hw : ∀ b ∈ S, ‖(v₀ b : ℍ) - (w b : ℍ)‖ ≤ 1 / 2) :
    |covariance (interiorLaw n S v₀ (WilsonTiltedMiddleAction.action n β u w e d q r s t))
      (source n β e q u ∘ insert n S v₀) (source n β d r u ∘ insert n S v₀)| ≤
      8 * (S.card : ℝ) * Real.log 81 / (β - 1) +
        20 * tailBound n β S v₀ u w (1 / 256) 4 := by
  have hc := WilsonPatchCovarianceTransfer.connected_bound n β hβ u w e d hed
    q r hq hr s t hs ht S v₀ hflat hu hw
  have hb := two_source_bound n β (by linarith) u w e d q r hq hr
    s t hs ht S v₀ (1 / 256) (by norm_num)
  linarith only [hc, hb]

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
    |covariance (interiorLaw n S v₀ (CompactGibbsSource.action
        (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w) h))
      (source n β e q u ∘ insert n S v₀) (source n β b p w ∘ insert n S v₀)| ≤
      8 * (S.card : ℝ) * Real.log 81 / (β - 2) +
        20 * tailBound n β S v₀ u w (1 / 256) 6 := by
  have hc := WilsonPatchCovarianceTransfer.transport_connected_bound n β hβ u w e d b hed
    q r p hq hr hp s t h hs ht hh S v₀ hflat hu hw
  have hb := transport_bound n β (by linarith) u w e d b q r p hq hr hp
    s t h hs ht hh S v₀ (1 / 256) (by norm_num)
  linarith only [hc, hb]

end
end UnifiedTheory.Clay.YangMills.WilsonPatchExponentialCovariance
