/- Physical covariance transport through two actual Wilson eliminations.
Both removed forms admit full-Schwartz contact subtraction. The final retained
covariance is exact but still requires its own uniform bound and nonzero limit. -/
import UnifiedTheory.Clay.YangMills.WilsonTwoStepCovariance
import UnifiedTheory.Clay.YangMills.WilsonSecondNoiseContact
import UnifiedTheory.Clay.YangMills.WilsonSchwartzCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonTwoStepSchwartzCovariance
noncomputable section
open MeasureTheory Filter RegulatedGauge LocalFields PeriodicLattice4
open WilsonIndependentBlocks WilsonInducedProduct WilsonSchwartzContactPath
open scoped Topology

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

/-- The physical normalization of the true twice-retained response covariance. -/
def retainedCovariance (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (plane plane' : Plane)
    (f g : TestFunction) : ℝ :=
  (a ^ 8)⁻¹ * GibbsCrossCovariance.covariance
    (WilsonBlockMarginal.secondMarginal n WilsonSingleLinkStaples.Q
      WilsonSingleLinkStaples.character β 2 S T)
    (WilsonSuccessiveNoiseKernel.next n β S T (WilsonPhysicalCellWeights.weight n a plane f))
    (WilsonSuccessiveNoiseKernel.next n β S T (WilsonPhysicalCellWeights.weight n a plane' g))

/-- Exact two-kernel physical dictionary; no independence or limit premise is needed. -/
theorem pairing_sum_tensor_eq (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (plane plane' : Plane)
    (f g : TestFunction) (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    WilsonCompactContactSubtraction.pairing n β a S plane plane'
      (SchwartzProductTensor.tensor f g) +
    WilsonSecondNoiseContact.pairing n β a S T plane plane'
      (SchwartzProductTensor.tensor f g) =
      (WilsonSchwartzCovariance.fullCovariance n β a plane plane' f g : ℂ) -
        (retainedCovariance n β a S T plane plane' f g : ℂ) := by
  have h1 := WilsonNoiseCellPairing.tensor_pairing n β a S plane plane' f g hf hg
  have h2 := WilsonSecondNoiseCellPairing.tensor_pairing n β a S T plane plane' f g hf hg
  change WilsonCompactContactSubtraction.pairing n β a S plane plane'
    (SchwartzProductTensor.tensor f g) = _ at h1
  change WilsonSecondNoiseContact.pairing n β a S T plane plane'
    (SchwartzProductTensor.tensor f g) = _ at h2
  rw [h1, h2]
  have h := congrArg (fun x : ℝ => (((a ^ 8)⁻¹ * x : ℝ) : ℂ))
    (WilsonTwoStepCovariance.covariance_sub_two n β S T
      (WilsonPhysicalCellWeights.weight n a plane f)
      (WilsonPhysicalCellWeights.weight n a plane' g))
  unfold WilsonSchwartzCovariance.fullCovariance retainedCovariance
  push_cast at h ⊢
  linear_combination -h

omit [NeZero n] in
/-- Both actual removed distributions converge to their diagonal contacts on every Schwartz test. -/
theorem removed_subtraction_tendsto (β : ℕ → ℝ)
    (S : (k : ℕ) → Finset (Edge (Vertex (period k))))
    (hS : ∀ k, Independent (period k) ((S k).image (edgeCoord (period k))))
    (T : (k : ℕ) → Finset {e : Edge (Vertex (period k)) // e ∉ S k})
    (hT : ∀ k, NextSeparated (period k) (S k) (T k))
    (plane plane' : Plane) (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    Tendsto (fun k =>
      WilsonCompactContactSubtraction.pairing (period k) (β k) (spacing k)
        (S k) plane plane' F +
      WilsonSecondNoiseContact.pairing (period k) (β k) (spacing k)
        (S k) (T k) plane plane' F -
      WilsonCompactContactSubtraction.contact4 (period k) (β k) (spacing k) (radius k)
        (S k) plane plane' F -
      WilsonSecondNoiseContact.contact4 (period k) (β k) (spacing k) (radius k)
        (S k) (T k) plane plane' F) atTop (𝓝 0) := by
  have h := (WilsonSchwartzContactPath.subtraction_tendsto β S hS plane plane' F).add
    (WilsonSecondNoiseContact.subtraction_tendsto β S hS T hT plane plane' F)
  simp only [add_zero] at h
  convert h using 1
  funext k
  ring

omit [NeZero n] in
/-- The actual full covariance minus two derived contacts differs from the twice-retained
physical covariance by a vanishing error, with arbitrary coupling and full Schwartz smears. -/
theorem repaired_covariance_tendsto (β : ℕ → ℝ)
    (S : (k : ℕ) → Finset (Edge (Vertex (period k))))
    (hS : ∀ k, Independent (period k) ((S k).image (edgeCoord (period k))))
    (T : (k : ℕ) → Finset {e : Edge (Vertex (period k)) // e ∉ S k})
    (hT : ∀ k, NextSeparated (period k) (S k) (T k))
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    Tendsto (fun k =>
      (WilsonSchwartzCovariance.fullCovariance (period k) (β k) (spacing k)
        plane plane' f g : ℂ) -
      WilsonCompactContactSubtraction.contact4 (period k) (β k) (spacing k) (radius k)
        (S k) plane plane' (SchwartzProductTensor.tensor f g) -
      WilsonSecondNoiseContact.contact4 (period k) (β k) (spacing k) (radius k)
        (S k) (T k) plane plane' (SchwartzProductTensor.tensor f g) -
      (retainedCovariance (period k) (β k) (spacing k) (S k) (T k) plane plane' f g : ℂ))
      atTop (𝓝 0) := by
  have h := removed_subtraction_tendsto β S hS T hT plane plane'
    (SchwartzProductTensor.tensor f g)
  simp_rw [pairing_sum_tensor_eq _ _ _ _ _ plane plane' f g hf hg] at h
  convert h using 1
  funext k
  ring

omit [NeZero n] in
/-- Separated physical covariances agree asymptotically through the two genuine induced laws. -/
theorem separated_covariance_difference_tendsto (β : ℕ → ℝ)
    (S : (k : ℕ) → Finset (Edge (Vertex (period k))))
    (hS : ∀ k, Independent (period k) ((S k).image (edgeCoord (period k))))
    (T : (k : ℕ) → Finset {e : Edge (Vertex (period k)) // e ∉ S k})
    (hT : ∀ k, NextSeparated (period k) (S k) (T k))
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0)
    (hdiag : ∀ x : Spacetime, (x, x) ∉ tsupport (SchwartzProductTensor.tensor f g)) :
    Tendsto (fun k =>
      (WilsonSchwartzCovariance.fullCovariance (period k) (β k) (spacing k)
        plane plane' f g : ℂ) -
      (retainedCovariance (period k) (β k) (spacing k) (S k) (T k) plane plane' f g : ℂ))
      atTop (𝓝 0) := by
  have h := repaired_covariance_tendsto β S hS T hT plane plane' f g hf hg
  simpa only [WilsonCompactContactSubtraction.contact4_eq_zero_of_diagonal_disjoint
    _ _ _ _ _ plane plane' (SchwartzProductTensor.tensor f g) hdiag,
    WilsonSecondNoiseContact.contact_diagonal_support
    _ _ _ _ _ _ plane plane' (SchwartzProductTensor.tensor f g) hdiag, sub_zero] using h

end
end UnifiedTheory.Clay.YangMills.WilsonTwoStepSchwartzCovariance
