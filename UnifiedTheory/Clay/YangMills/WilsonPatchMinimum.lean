/- Actual compact-patch minimizers and quadratic growth for the sourced
middle Wilson action. This is deterministic constrained minimization;
it supplies no covariance or global coercivity estimate by itself. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchSourceCurvature

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchMinimum
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonSpatialCutEnergy WilsonJointRotation
open WilsonPatchNeighborhood WilsonPatchSourceCurvature WilsonBoundaryConnected
open scoped Quaternion

variable (n : ℕ) [NeZero n]

/-- A positive symmetric group-rotation bound becomes a strict midpoint
bound on this actual compact patch, measured in quaternion chord distance. -/
theorem midpoint_bound (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε κ : ℝ) (hε : ε ^ 2 < 2) (hκ : 0 ≤ κ) (A : Slice n → ℝ)
    (hsecond : ∀ m ∈ region n S v₀ ε, ∀ a : Slice n, (∀ e, e ∉ S → a e = 1) →
      κ * cost n a ≤ A (a * m) + A (a⁻¹ * m) - 2 * A m)
    (v w : Slice n) (hv : v ∈ region n S v₀ ε) (hw : w ∈ region n S v₀ ε) :
    ∃ m ∈ region n S v₀ ε,
      A m + (κ / 8) * distanceSq n v w ≤ (A v + A w) / 2 := by
  obtain ⟨m, hm, a, ha, hav, haw, hd⟩ := exists_midpoint n S v₀ ε hε v w hv hw
  have hs := hsecond m hm a ha
  rw [hav, haw] at hs
  have hmul := mul_le_mul_of_nonneg_left hd hκ
  exact ⟨m, hm, by nlinarith only [hs, hmul]⟩

theorem minimum_growth (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε κ : ℝ) (hε : ε ^ 2 < 2) (hκ : 0 ≤ κ) (A : Slice n → ℝ)
    (hsecond : ∀ m ∈ region n S v₀ ε, ∀ a : Slice n, (∀ e, e ∉ S → a e = 1) →
      κ * cost n a ≤ A (a * m) + A (a⁻¹ * m) - 2 * A m)
    (v : Slice n) (hv : v ∈ region n S v₀ ε) (hmin : IsMinOn A (region n S v₀ ε) v)
    (w : Slice n) (hw : w ∈ region n S v₀ ε) :
    (κ / 4) * distanceSq n v w ≤ A w - A v := by
  obtain ⟨m, hm, hb⟩ := midpoint_bound n S v₀ ε κ hε hκ A hsecond v w hv hw
  have hh : A v ≤ A m := hmin hm
  linarith

theorem exists_unique_minimum (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε κ : ℝ) (hε0 : 0 ≤ ε) (hε : ε ^ 2 < 2) (hκ : 0 < κ) (A : Slice n → ℝ)
    (hA : Continuous A)
    (hsecond : ∀ m ∈ region n S v₀ ε, ∀ a : Slice n, (∀ e, e ∉ S → a e = 1) →
      κ * cost n a ≤ A (a * m) + A (a⁻¹ * m) - 2 * A m) :
    ∃! v : Slice n, v ∈ region n S v₀ ε ∧ IsMinOn A (region n S v₀ ε) v := by
  obtain ⟨v, hv, hmin⟩ := (region_compact n S v₀ ε).exists_isMinOn
    ⟨v₀, center_mem n S v₀ ε hε0⟩ hA.continuousOn
  refine ⟨v, ⟨hv, hmin⟩, ?_⟩
  rintro w ⟨hw, hminw⟩
  have hg := minimum_growth n S v₀ ε κ hε hκ.le A hsecond v hv hmin w hw
  have hh : A w ≤ A v := hminw hv
  have hd := distanceSq_nonneg n v w
  have hz : distanceSq n v w = 0 := by nlinarith
  exact ((distanceSq_eq_zero n v w).mp hz).symm

/-- The exact two-source action has a unique constrained minimizer for
beta greater than one, uniformly throughout the source rectangle. -/
theorem action_unique_minimum (β : ℝ) (hβ : 1 < β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (hflat : ∀ p b, b ∈ S → b ∈ support n p →
      ‖((spatialHolonomy v₀ p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 64)
    (hu : ∀ b ∈ S, ‖(v₀ b : ℍ) - (u b : ℍ)‖ ≤ 1 / 2)
    (hw : ∀ b ∈ S, ‖(v₀ b : ℍ) - (w b : ℍ)‖ ≤ 1 / 2) :
    ∃! v : Slice n, v ∈ region n S v₀ (1 / 256) ∧
      IsMinOn (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (region n S v₀ (1 / 256)) v := by
  apply exists_unique_minimum n S v₀ (1 / 256) (2 * β - 2) (by norm_num) (by norm_num)
    (by linarith) _ (WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t)
  intro v hv a ha
  exact action_second_patch n β (by linarith) u w e d hed q r hq hr s t hs ht
    S v₀ v a hv ha hflat hu hw

theorem action_minimum_growth (β : ℝ) (hβ : 1 < β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ v z : Slice n)
    (hflat : ∀ p b, b ∈ S → b ∈ support n p →
      ‖((spatialHolonomy v₀ p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 64)
    (hu : ∀ b ∈ S, ‖(v₀ b : ℍ) - (u b : ℍ)‖ ≤ 1 / 2)
    (hw : ∀ b ∈ S, ‖(v₀ b : ℍ) - (w b : ℍ)‖ ≤ 1 / 2)
    (hv : v ∈ region n S v₀ (1 / 256))
    (hmin : IsMinOn (WilsonTiltedMiddleAction.action n β u w e d q r s t)
      (region n S v₀ (1 / 256)) v) (hz : z ∈ region n S v₀ (1 / 256)) :
    ((β - 1) / 2) * distanceSq n v z ≤
      WilsonTiltedMiddleAction.action n β u w e d q r s t z -
      WilsonTiltedMiddleAction.action n β u w e d q r s t v := by
  have hg := minimum_growth n S v₀ (1 / 256) (2 * β - 2) (by norm_num) (by linarith)
    _ (fun m hm a ha => action_second_patch n β (by linarith) u w e d hed q r hq hr
      s t hs ht S v₀ m a hm ha hflat hu hw) v hv hmin z hz
  convert hg using 1
  ring

/-- The transported third source also has a unique minimizer in the same
fixed patch. Its link need not be distinct from the first two links. -/
theorem transport_unique_minimum (β : ℝ) (hβ : 2 < β) (u w : Slice n)
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
    ∃! v : Slice n, v ∈ region n S v₀ (1 / 256) ∧
      IsMinOn (CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h) (region n S v₀ (1 / 256)) v := by
  apply exists_unique_minimum n S v₀ (1 / 256) (2 * β - 4) (by norm_num) (by norm_num)
    (by linarith) _
  · exact (WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t).sub
      (continuous_const.mul (source_continuous n β b p w))
  · intro v hv a ha
    exact transport_second_patch n β (by linarith) u w e d b hed q r p hq hr hp
      s t h hs ht hh S v₀ v a hv ha hflat hu hw

end
end UnifiedTheory.Clay.YangMills.WilsonPatchMinimum
