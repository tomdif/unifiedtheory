/- An actual cap-complement estimate for the unrestricted middle interior
law. Background plaquette and endpoint costs stay local and explicit;
they are not assumed small under the retained exterior distribution. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchGaussianPartition
import UnifiedTheory.Clay.YangMills.CompactGibbsGaussianTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchComplementTail
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonPatchConditioning
open WilsonPatchNeighborhood WilsonPatchLocalEnergy WilsonPatchGaussianPartition
open WilsonBoundaryConnected WilsonPatchCovarianceTransfer
open scoped Quaternion

variable (n : ℕ) [NeZero n]

def backgroundCost (S : Finset (SpatialVertex n × Fin 3)) (v₀ u w : Slice n) : ℝ :=
  2 * incidentEnergy n S v₀ + 3 * endpointEnergy n S v₀ u w

def tailBound (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) (v₀ u w : Slice n)
    (ε M : ℝ) : ℝ :=
  Real.exp ((S.card : ℝ) * Real.log (gaussianCap β) +
    β * (backgroundCost n S v₀ u w - ε ^ 2) + 2 * M)

/-- This is a probability bound for the actual unrestricted sourced law.
The exterior energy cancels exactly, not through a volume-dependent bound. -/
theorem perturbed_bound (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ u w : Slice n)
    (ε : ℝ) (hε : 0 ≤ ε) (R : Slice n → ℝ) (hR : Continuous R)
    (M : ℝ) (hRM : ∀ v, |R v| ≤ M) :
    badMass n S v₀ ε (fun v => WilsonMiddleBridge.action n β u w v - R v) ≤
      tailBound n β S v₀ u w ε M := by
  let A : Inside n S → ℝ := fun x =>
    WilsonMiddleBridge.action n β u w (insert n S v₀ x) - R (insert n S v₀ x)
  let D : Inside n S → ℝ := fun x => distanceSq n v₀ (insert n S v₀ x)
  have hA : Continuous A := ((WilsonMiddleBridge.action_continuous n β u w).sub hR).comp
    (insert_continuous n S v₀)
  have hD : Continuous D := (WilsonPatchFluctuation.distance_continuous n v₀).comp
    (insert_continuous n S v₀)
  have hu : ∀ x, A x ≤ β * exteriorEnergy n S v₀ u w +
      (2 * β * localEnergy n S v₀ u w + M) + (36 * β) * D x := by
    intro x
    have hv := insert_outside n S v₀ x
    have hb := mul_le_mul_of_nonneg_left (local_upper n S v₀ u w (insert n S v₀ x) hv) hβ
    have hs := (abs_le.mp (hRM (insert n S v₀ x))).1
    dsimp only [A, D]
    rw [action_split n S v₀ u w _ hv]
    nlinarith only [hb, hs]
  have hl : ∀ x ∈ (event n S v₀ ε)ᶜ,
      β * exteriorEnergy n S v₀ u w +
        (β * (ε ^ 2 - endpointEnergy n S v₀ u w) - M) ≤ A x := by
    intro x hx
    have hv := insert_outside n S v₀ x
    have hd := bad_distance n S v₀ ε hε x hx
    have hb := local_lower n S v₀ u w (insert n S v₀ x) hv
    have hm := mul_le_mul_of_nonneg_left
      (show ε ^ 2 - endpointEnergy n S v₀ u w ≤
        localEnergy n S (insert n S v₀ x) u w by linarith only [hd, hb]) hβ
    have hs := (abs_le.mp (hRM (insert n S v₀ x))).2
    dsimp only [A]
    rw [action_split n S v₀ u w _ hv]
    linarith only [hm, hs]
  have hh := CompactGibbsGaussianTail.event_bound (haar n S) A D hA hD
    (β * exteriorEnergy n S v₀ u w) (2 * β * localEnergy n S v₀ u w + M)
    (36 * β) ((S.card : ℝ) * Real.log (gaussianCap β))
    (β * (ε ^ 2 - endpointEnergy n S v₀ u w) - M) (event n S v₀ ε)ᶜ
    hu (gaussian_lower n S v₀ β hβ) hl
  change badMass n S v₀ ε (fun v => WilsonMiddleBridge.action n β u w v - R v) ≤ _ at hh
  apply hh.trans_eq
  unfold tailBound backgroundCost localEnergy
  congr 1
  ring

theorem scaled_source_bound (β : ℝ) (hβ : 0 ≤ β) (b : SpatialVertex n × Fin 3)
    (p : Q) (hp : β * ‖(p : ℍ) - 1‖ ≤ 1) (u v : Slice n) :
    |source n β b p u v| ≤ 2 := by
  have hh := source_bound n β hβ b p u v
  nlinarith only [hh, hp]

theorem source_strength_bound (β : ℝ) (hβ : 0 ≤ β) (b : SpatialVertex n × Fin 3)
    (p : Q) (hp : β * ‖(p : ℍ) - 1‖ ≤ 1) (u v : Slice n)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : |s * source n β b p u v| ≤ 2 := by
  rw [abs_mul, abs_of_nonneg hs.1]
  have hh := mul_le_mul hs.2 (scaled_source_bound n β hβ b p hp u v)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using hh

/-- Two-source error exp(8); the two links need not be distinct for this tail. -/
theorem two_source_bound (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ) (hε : 0 ≤ ε) :
    badMass n S v₀ ε (WilsonTiltedMiddleAction.action n β u w e d q r s t) ≤
      tailBound n β S v₀ u w ε 4 := by
  let R : Slice n → ℝ := fun v => s * source n β e q u v + t * source n β d r u v
  have hR : Continuous R :=
    (continuous_const.mul (source_continuous n β e q u)).add
      (continuous_const.mul (source_continuous n β d r u))
  have hRM (v : Slice n) : |R v| ≤ 4 := by
    have he := source_strength_bound n β hβ e q hq u v s hs
    have hd := source_strength_bound n β hβ d r hr u v t ht
    exact (abs_add_le _ _).trans (by linarith only [he, hd])
  have he : (fun v => WilsonMiddleBridge.action n β u w v - R v) =
      WilsonTiltedMiddleAction.action n β u w e d q r s t := by
    funext v
    unfold WilsonTiltedMiddleAction.action R
    ring
  have hh := perturbed_bound n β hβ S v₀ u w ε hε R hR 4 hRM
  rw [he] at hh
  exact hh

/-- The additional transported source costs exp(12), even with overlap. -/
theorem transport_bound (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (q r p : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (hp : β * ‖(p : ℍ) - 1‖ ≤ 1)
    (s t h : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hh : h ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ) (hε : 0 ≤ ε) :
    badMass n S v₀ ε (CompactGibbsSource.action
      (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w) h) ≤
      tailBound n β S v₀ u w ε 6 := by
  let R : Slice n → ℝ := fun v =>
    s * source n β e q u v + t * source n β d r u v + h * source n β b p w v
  have hR : Continuous R :=
    ((continuous_const.mul (source_continuous n β e q u)).add
      (continuous_const.mul (source_continuous n β d r u))).add
        (continuous_const.mul (source_continuous n β b p w))
  have hRM (v : Slice n) : |R v| ≤ 6 := by
    have he := source_strength_bound n β hβ e q hq u v s hs
    have hd := source_strength_bound n β hβ d r hr u v t ht
    have hb := source_strength_bound n β hβ b p hp w v h hh
    have ha := abs_add_le (s * source n β e q u v) (t * source n β d r u v)
    exact (abs_add_le _ _).trans (by linarith only [he, hd, hb, ha])
  have he : (fun v => WilsonMiddleBridge.action n β u w v - R v) =
      CompactGibbsSource.action (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (source n β b p w) h := by
    funext v
    unfold CompactGibbsSource.action WilsonTiltedMiddleAction.action R
    ring
  have hb := perturbed_bound n β hβ S v₀ u w ε hε R hR 6 hRM
  rw [he] at hb
  exact hb

/-- This explicit eligibility condition is stronger than positivity of
curvature on a cap. It is not asserted for arbitrary retained backgrounds. -/
theorem tailBound_suppressed (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ u w : Slice n) (ε M : ℝ)
    (hgood : backgroundCost n S v₀ u w ≤ ε ^ 2 / 2) :
    tailBound n β S v₀ u w ε M ≤
      Real.exp ((S.card : ℝ) * Real.log (gaussianCap β) + 2 * M - β * ε ^ 2 / 2) := by
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hgood hβ
  linarith only [hh]

end
end UnifiedTheory.Clay.YangMills.WilsonPatchComplementTail
