/- Source-stable curvature along a fixed active patch. Only incident
plaquettes and the active endpoint links need to be small-field. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchNeighborhood
import UnifiedTheory.Clay.YangMills.WilsonMiddleSourceTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchSourceCurvature
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonSpatialCutEnergy WilsonJointRotation
open WilsonPatchNeighborhood WilsonBoundaryConnected
open scoped Quaternion

variable (n : ℕ) [NeZero n]

theorem action_second_active (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v a : Slice n) (δ ηu ηw : ℝ)
    (ha : ∀ b, b ∉ S → a b = 1)
    (hflat : ∀ p b, b ∈ S → b ∈ support n p →
      ‖((spatialHolonomy v p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ≤ δ)
    (hu : ∀ b ∈ S, ‖(v b : ℍ) - (u b : ℍ)‖ ^ 2 ≤ ηu)
    (hw : ∀ b ∈ S, ‖(v b : ℍ) - (w b : ℍ)‖ ^ 2 ≤ ηw) :
    (β * (4 - ηu - ηw - 32 * δ) - 2) * cost n a ≤
      WilsonTiltedMiddleAction.action n β u w e d q r s t (a * v) +
      WilsonTiltedMiddleAction.action n β u w e d q r s t (a⁻¹ * v) -
      2 * WilsonTiltedMiddleAction.action n β u w e d q r s t v := by
  have h1 := WilsonMaskedCurvature.middle_second_active n β hβ S a u w v δ ηu ηw
    ha hflat hu hw
  have h2 := WilsonTiltedMiddleAction.action_second_lower n β hβ u w e d hed
    q r hq hr s t hs ht v a
  linarith

/-- The additional endpoint source may coincide with either earlier link. -/
theorem transport_second_active (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r p : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (hp : β * ‖(p : ℍ) - 1‖ ≤ 1)
    (s t h : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hh : h ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v a : Slice n) (δ ηu ηw : ℝ)
    (ha : ∀ c, c ∉ S → a c = 1)
    (hflat : ∀ z c, c ∈ S → c ∈ support n z →
      ‖((spatialHolonomy v z.1 z.2.1.1 z.2.1.2 : Q) : ℍ) - 1‖ ≤ δ)
    (hu : ∀ c ∈ S, ‖(v c : ℍ) - (u c : ℍ)‖ ^ 2 ≤ ηu)
    (hw : ∀ c ∈ S, ‖(v c : ℍ) - (w c : ℍ)‖ ^ 2 ≤ ηw) :
    (β * (4 - ηu - ηw - 32 * δ) - 4) * cost n a ≤
      CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h (a * v) +
      CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h (a⁻¹ * v) -
      2 * CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h v := by
  have hbase := action_second_active n β hβ u w e d hed q r hq hr s t hs ht
    S v a δ ηu ηw ha hflat hu hw
  have hb : -2 ≤ source n β b p w v := by
    have hbound := (abs_le.mp (source_bound n β hβ b p w v)).1
    linarith
  have hsour : -2 ≤ h * source n β b p w v := by nlinarith only [hb, hh.1, hh.2]
  have hm := mul_le_mul_of_nonneg_right hsour (sq_nonneg (displacement n a b))
  have hc : (displacement n a b) ^ 2 ≤ cost n a :=
    Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ b)
  rw [WilsonMiddleSourceTransport.transport_action_second]
  nlinarith only [hbase, hm, hc]

/-- One set of base hypotheses supplies the bound at every configuration in
the fixed patch neighborhood, with arbitrary far-away defects. -/
theorem action_second_patch (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ v a : Slice n)
    (hv : v ∈ region n S v₀ (1 / 256)) (ha : ∀ b, b ∉ S → a b = 1)
    (hflat : ∀ p b, b ∈ S → b ∈ support n p →
      ‖((spatialHolonomy v₀ p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 64)
    (hu : ∀ b ∈ S, ‖(v₀ b : ℍ) - (u b : ℍ)‖ ≤ 1 / 2)
    (hw : ∀ b ∈ S, ‖(v₀ b : ℍ) - (w b : ℍ)‖ ≤ 1 / 2) :
    (2 * β - 2) * cost n a ≤
      WilsonTiltedMiddleAction.action n β u w e d q r s t (a * v) +
      WilsonTiltedMiddleAction.action n β u w e d q r s t (a⁻¹ * v) -
      2 * WilsonTiltedMiddleAction.action n β u w e d q r s t v := by
  have h1 := action_second_active n β hβ u w e d hed q r hq hr s t hs ht
    S v a (1 / 32) (1 / 2) (1 / 2) ha (incident_small n S v₀ v hv hflat)
    (endpoint_small n S v₀ v u hv hu) (endpoint_small n S v₀ v w hv hw)
  convert h1 using 1
  ring

theorem transport_second_patch (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r p : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (hp : β * ‖(p : ℍ) - 1‖ ≤ 1)
    (s t h : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hh : h ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ v a : Slice n)
    (hv : v ∈ region n S v₀ (1 / 256)) (ha : ∀ c, c ∉ S → a c = 1)
    (hflat : ∀ z c, c ∈ S → c ∈ support n z →
      ‖((spatialHolonomy v₀ z.1 z.2.1.1 z.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 64)
    (hu : ∀ c ∈ S, ‖(v₀ c : ℍ) - (u c : ℍ)‖ ≤ 1 / 2)
    (hw : ∀ c ∈ S, ‖(v₀ c : ℍ) - (w c : ℍ)‖ ≤ 1 / 2) :
    (2 * β - 4) * cost n a ≤
      CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h (a * v) +
      CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h (a⁻¹ * v) -
      2 * CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h v := by
  have h1 := transport_second_active n β hβ u w e d b hed q r p hq hr hp s t h hs ht hh
    S v a (1 / 32) (1 / 2) (1 / 2) ha (incident_small n S v₀ v hv hflat)
    (endpoint_small n S v₀ v u hv hu) (endpoint_small n S v₀ v w hv hw)
  convert h1 using 1
  ring

end
end UnifiedTheory.Clay.YangMills.WilsonPatchSourceCurvature
