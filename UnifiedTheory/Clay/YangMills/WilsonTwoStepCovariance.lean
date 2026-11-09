/- Exact two-stage covariance subtraction for the original Wilson law.
The first noise matrix is computed under the original law and the second under
its genuine induced law. Both match the actual successive response tower.
No block independence or continuum estimate is required for this identity. -/
import UnifiedTheory.Clay.YangMills.WilsonSuccessiveNoiseKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonTwoStepCovariance
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonBlockMarginal
open WilsonSingleLinkStaples

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

omit [NeZero n] in
/-- Forgetting the second coordinate split recovers the original first exterior. -/
theorem assemble_first_exterior (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (U : Configuration (Vertex n) Q) :
    assemble T ((assembleTwo S T).symm U).1 = ((assemble S).symm U).1 := by
  change assemble T ((assemble T).symm (((assemble S).symm U).1)) = _
  exact (assemble T).apply_symm_apply _

/-- The same first conditional expectation, expressed in the two coordinate charts. -/
theorem first_response_eq_retained (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f : PlaquetteIndex n → ℝ)
    (z : Outside (G := Q) T × Inside (G := Q) T) :
    firstResponse n Q character β 2 S T (WilsonBlockNoiseKernel.source n f) z =
      WilsonBlockNoiseKernel.retained n β S f (assemble T z) := rfl

/-- The first actual fluctuation is independent of how its exterior is split later. -/
theorem firstNoise_eq_noise (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f : PlaquetteIndex n → ℝ)
    (U : Configuration (Vertex n) Q) :
    WilsonSuccessiveCovariance.firstNoise n Q character β 2 S T
      (WilsonBlockNoiseKernel.source n f) U = WilsonBlockNoiseKernel.noise n β S f U := by
  unfold WilsonSuccessiveCovariance.firstNoise
  rw [first_response_eq_retained, assemble_first_exterior]
  rfl

/-- The first Gram in the genuine two-step tower is exactly the original-law matrix. -/
theorem firstGram_eq_bilinear (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f g : PlaquetteIndex n → ℝ) :
    WilsonSuccessiveCovariance.firstGram n Q character β 2 S T
      (WilsonBlockNoiseKernel.source n f) (WilsonBlockNoiseKernel.source n g) =
      WilsonBlockNoiseKernel.bilinear n β S f g := by
  rw [WilsonBlockNoiseKernel.bilinear_eq_noise]
  unfold WilsonSuccessiveCovariance.firstGram
  simp_rw [firstNoise_eq_noise]

/-- Exact physical-source-compatible subtraction: the second removed form is
computed under the first induced measure, not another copy of the original law. -/
theorem covariance_sub_two (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (f g : PlaquetteIndex n → ℝ) :
    GibbsCrossCovariance.covariance (PeriodicLattice4.wilsonLaw n Q character β 2)
      (WilsonBlockNoiseKernel.source n f) (WilsonBlockNoiseKernel.source n g) -
      WilsonBlockNoiseKernel.bilinear n β S f g -
      WilsonSuccessiveNoiseKernel.bilinear n β S T f g =
      GibbsCrossCovariance.covariance (secondMarginal n Q character β 2 S T)
        (WilsonSuccessiveNoiseKernel.next n β S T f)
        (WilsonSuccessiveNoiseKernel.next n β S T g) := by
  have h := WilsonSuccessiveCovariance.covariance_decomposition n Q character
    character_continuous β 2 S T (WilsonBlockNoiseKernel.source n f)
    (WilsonBlockNoiseKernel.source n g) (WilsonBlockNoiseKernel.source_continuous n f)
    (WilsonBlockNoiseKernel.source_continuous n g)
  rw [firstGram_eq_bilinear,
    ← WilsonSuccessiveNoiseKernel.bilinear_eq_secondGram] at h
  change _ = _ + _ + GibbsCrossCovariance.covariance
    (secondMarginal n Q character β 2 S T)
    (WilsonSuccessiveNoiseKernel.next n β S T f)
    (WilsonSuccessiveNoiseKernel.next n β S T g) at h
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonTwoStepCovariance
