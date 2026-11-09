/- Explicit full-transfer versions of the arbitrary-pattern estimates.
The equality between the raw step and the full gauge-averaged transition is
used only with its gauge-invariance hypothesis. -/
import UnifiedTheory.Clay.YangMills.WilsonClusterCountTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonClusterPhysicalSource
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab WilsonTemporalGauge
open WilsonGroundLocalComparison WilsonGroundHeatBath WilsonPhysicalVariance WilsonHighFieldDecay
open SpatialPlaquetteCutGeometry SpatialWilsonPlaquetteKernels WilsonGroundSlabEnergy
open WilsonClusterSourceDecay

variable (n : ℕ) [NeZero n]

theorem full_mass (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice (2 * (2 * n)), ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) :
    (∫ u, (∫ v, transition (2 * (2 * n)) β hβ u v * f v
      ∂WilsonSlabOperator.measure (2 * (2 * n)))^2 ∂groundLaw (2 * (2 * n)) β hβ) =
      mass (2 * (2 * n)) β hβ (step (2 * (2 * n)) β hβ f) := by
  unfold mass
  apply integral_congr_ae
  filter_upwards with u
  rw [step_full _ β hβ f hinv u]

theorem intersection_decay (S : Finset (Plaquette (2 * n)))
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hR : 96 * envelope β ≤ R)
    (f : C(Slice (2 * (2 * n)), ℝ)) (hinv : ∀ h u, f (gaugeSlice h u) = f u)
    (hs : ∀ u, (∃ p ∈ S, defect (2 * n) p u < R) → f u = 0) :
    (∫ u, (∫ v, transition (2 * (2 * n)) β hβ.le u v * f v
      ∂WilsonSlabOperator.measure (2 * (2 * n)))^2 ∂groundLaw (2 * (2 * n)) β hβ.le) ≤
      (rate β R)^S.card * mass (2 * (2 * n)) β hβ.le f := by
  rw [full_mass n β hβ.le f hinv]
  exact WilsonClusterSourceDecay.intersection_decay n S β hβ R hR f hs

theorem source_tail (S : Finset (Plaquette (2 * n)))
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R)
    (f : C(Slice (2 * (2 * n)), ℝ)) (hinv : ∀ h u, f (gaugeSlice h u) = f u) :
    (∫ u, (WilsonPatchSourceTail.hard (2 * n) S R).indicator (fun v => (f v)^2) u
      ∂groundLaw (2 * (2 * n)) β hβ.le) ≤
      2 * (mass (2 * (2 * n)) β hβ.le f -
        ∫ u, (∫ v, transition (2 * (2 * n)) β hβ.le u v * f v
          ∂WilsonSlabOperator.measure (2 * (2 * n)))^2 ∂groundLaw (2 * (2 * n)) β hβ.le) +
        2 * (rate β R)^S.card * mass (2 * (2 * n)) β hβ.le f := by
  rw [full_mass n β hβ.le f hinv, ← loss_mass]
  exact WilsonClusterSourceTail.source_tail n S β hβ R hmargin hR f

theorem density_tail (A : Finset (Plaquette (2 * n)))
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R)
    (b k : ℕ) (hk : A.card ≤ b * k)
    (f : C(Slice (2 * (2 * n)), ℝ)) (hinv : ∀ h u, f (gaugeSlice h u) = f u) :
    (∫ u, (WilsonPatchCountTail.event (2 * n) A R k).indicator (fun v => (f v)^2) u
      ∂groundLaw (2 * (2 * n)) β hβ.le) ≤
      2 * (mass (2 * (2 * n)) β hβ.le f -
        ∫ u, (∫ v, transition (2 * (2 * n)) β hβ.le u v * f v
          ∂WilsonSlabOperator.measure (2 * (2 * n)))^2 ∂groundLaw (2 * (2 * n)) β hβ.le) +
        2 * ((2 : ℝ)^b * rate β R)^k * mass (2 * (2 * n)) β hβ.le f := by
  rw [full_mass n β hβ.le f hinv, ← loss_mass]
  exact WilsonClusterCountTail.density_tail n A β hβ R hmargin hR b k hk f

end
end UnifiedTheory.Clay.YangMills.WilsonClusterPhysicalSource
