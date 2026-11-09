/- Arbitrary-pattern source tails under the original Wilson ground law.
The single variance-loss charge is retained; no independence is assumed. -/
import UnifiedTheory.Clay.YangMills.WilsonClusterSourceDecay
import UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonClusterSourceTail
noncomputable section
open WilsonSlabOperator
open MeasureTheory WilsonTimeSlab WilsonGroundHeatBath WilsonPhysicalVariance
open WilsonHighFieldDecay WilsonHighFieldReduction CompactDensityEntropy SpatialPlaquetteCutGeometry
open SpatialWilsonPlaquetteKernels (defect)
open WilsonGroundSlabEnergy WilsonClusterSourceDecay
open WilsonPatchSourceTail (cutoff cutoff_range cutoff_supported cutoff_one hard hard_measurable)

variable (n : ℕ) [NeZero n]

theorem cutoff_output (S : Finset (Plaquette (2 * n)))
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hR : 96 * envelope β ≤ R) (χ f : C(Slice (2 * (2 * n)), ℝ))
    (hχ : ∀ u, χ u ∈ Set.Icc 0 1)
    (hs : ∀ u, (∃ p ∈ S, defect (2 * n) p u < R) → χ u = 0) :
    mass (2 * (2 * n)) β hβ.le (χ * step (2 * (2 * n)) β hβ.le f) ≤
      (rate β R) ^ S.card * mass (2 * (2 * n)) β hβ.le f := by
  apply WilsonCutoffCover.cutoff_output (2 * (2 * n)) β hβ.le χ _
    (pow_nonneg (rate_pos β R).le _) hχ _ f
  intro g hg
  exact WilsonClusterSourceDecay.intersection_decay n S β hβ R hR g
    (fun u hu => hg u (hs u hu))

theorem source_cutoff (S : Finset (Plaquette (2 * n)))
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hR : 96 * envelope β ≤ R) (χ f : C(Slice (2 * (2 * n)), ℝ))
    (hχ : ∀ u, χ u ∈ Set.Icc 0 1)
    (hs : ∀ u, (∃ p ∈ S, defect (2 * n) p u < R) → χ u = 0) :
    mass (2 * (2 * n)) β hβ.le (χ * f) ≤ 2 * loss (2 * (2 * n)) β hβ.le f +
      2 * (rate β R) ^ S.card * mass (2 * (2 * n)) β hβ.le f := by
  let h0 : 0 ≤ β := by linarith
  let P2 := step (2 * (2 * n)) β h0 (step (2 * (2 * n)) β h0 f)
  have hi := WilsonCutoffCover.mass_split (2 * (2 * n)) β h0 χ f P2
  have ha := (cutoff_mass_le (2 * (2 * n)) β h0 χ (f-P2) hχ).trans
    (residual_le_loss (2 * (2 * n)) β h0 f)
  have hb := (cutoff_output n S β hβ R hR χ (step (2 * (2 * n)) β h0 f) hχ hs).trans
    (mul_le_mul_of_nonneg_left (mass_step_le (2 * (2 * n)) β h0 f) (pow_nonneg (rate_pos β R).le _))
  change mass (2 * (2 * n)) β h0 (χ*P2) ≤ _ at hb
  linarith

/-- A genuine joint pattern estimate. The source can concentrate on this
rare event; it is not replaced by an unweighted background probability. -/
theorem source_tail (S : Finset (Plaquette (2 * n)))
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R)
    (f : C(Slice (2 * (2 * n)), ℝ)) :
    (∫ u, (hard (2 * n) S R).indicator (fun v => (f v) ^ 2) u ∂groundLaw (2 * (2 * n)) β hβ.le) ≤
      2 * loss (2 * (2 * n)) β hβ.le f +
        2 * (rate β R) ^ S.card * mass (2 * (2 * n)) β hβ.le f := by
  let h0 : 0 ≤ β := by linarith
  letI := groundLaw_probability (2 * (2 * n)) β h0
  have hi : (∫ u, (hard (2 * n) S R).indicator (fun v => (f v) ^ 2) u
      ∂groundLaw (2 * (2 * n)) β h0) ≤
      mass (2 * (2 * n)) β h0 (cutoff (2 * n) S R * f) := by
    apply integral_mono
    · exact (continuous_integrable (groundLaw (2 * (2 * n)) β h0) _ (f.continuous.pow 2)).indicator
        (hard_measurable (2 * n) S R)
    · exact continuous_integrable (groundLaw (2 * (2 * n)) β h0) _ 
        ((cutoff (2 * n) S R * f).continuous.pow 2)
    · intro u
      by_cases hu : u ∈ hard (2 * n) S R
      · rw [Set.indicator_of_mem hu]
        simp only [ContinuousMap.mul_apply,
          cutoff_one (2 * n) S R hR u (fun p hp => hu ⟨p,hp⟩), one_mul, le_refl]
      · rw [Set.indicator_of_notMem hu]
        exact sq_nonneg _
  exact hi.trans (source_cutoff n S β hβ R hmargin (cutoff (2 * n) S R) f
    (cutoff_range (2 * n) S R) (cutoff_supported (2 * n) S R hR))


end
end UnifiedTheory.Clay.YangMills.WilsonClusterSourceTail
