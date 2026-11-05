/- A coherent mixed-source renormalization using the deterministic covariance
of the fluctuation removed by an actual Wilson block. The corrected second
moment is the retained covariance. Higher corrected moments are constructed,
but are not asserted to be moments of the retained law. -/
import UnifiedTheory.Clay.YangMills.FiniteSourceWickJets
import UnifiedTheory.Clay.YangMills.WilsonBlockNoiseKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonNoiseSourceJets
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples

variable (n : ℕ) [NeZero n]
local instance lawProbability (β : ℝ) : IsProbabilityMeasure (wilsonLaw n Q character β 2) :=
  wilsonLaw_probability n Q character character_continuous β 2

/-- Centering uses the original interacting Wilson measure. -/
def centered (β : ℝ) (f : PlaquetteIndex n → ℝ) (U : Configuration (Vertex n) Q) : ℝ :=
  WilsonBlockNoiseKernel.source n f U -
    ∫ V, WilsonBlockNoiseKernel.source n f V ∂wilsonLaw n Q character β 2

theorem centered_continuous (β : ℝ) (f : PlaquetteIndex n → ℝ) :
    Continuous (centered n β f) :=
  (WilsonBlockNoiseKernel.source_continuous n f).sub continuous_const

theorem centered_mean (β : ℝ) (f : PlaquetteIndex n → ℝ) :
    (∫ U, centered n β f U ∂wilsonLaw n Q character β 2) = 0 := by
  unfold centered
  have hi := (WilsonBlockNoiseKernel.source_continuous n f).integrable_of_hasCompactSupport
    (μ := wilsonLaw n Q character β 2) (HasCompactSupport.of_compactSpace _)
  rw [integral_sub hi (integrable_const _)]
  simp

variable {I : Type*}

/-- Every entry is a deterministic original-law expectation of removed noise. -/
def noiseMatrix (β : ℝ) (S : Finset (Edge (Vertex n)))
    (f : I → PlaquetteIndex n → ℝ) (i j : I) : ℝ :=
  WilsonBlockNoiseKernel.bilinear n β S (f i) (f j)

theorem noiseMatrix_symmetric (β : ℝ) (S : Finset (Edge (Vertex n)))
    (f : I → PlaquetteIndex n → ℝ) (i j : I) :
    noiseMatrix n β S f i j = noiseMatrix n β S f j i := by
  unfold noiseMatrix
  rw [WilsonBlockNoiseKernel.bilinear_eq_noise, WilsonBlockNoiseKernel.bilinear_eq_noise]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun U => mul_comm _ _)

variable [Fintype I] [DecidableEq I]

/-- A genuine finite-dimensional source generating function under the original law. -/
def generating (β : ℝ) (S : Finset (Edge (Vertex n)))
    (f : I → PlaquetteIndex n → ℝ) (t : I → ℝ) : ℝ :=
  FiniteSourceWickJets.generating (wilsonLaw n Q character β 2)
    (fun i => centered n β (f i)) (noiseMatrix n β S f) t

omit [DecidableEq I] in
theorem normalized (β : ℝ) (S : Finset (Edge (Vertex n)))
    (f : I → PlaquetteIndex n → ℝ) : generating n β S f 0 = 1 := by
  simp [generating, FiniteSourceWickJets.generating, FiniteSourceWickJets.quadratic]

/-- Actual arbitrary mixed derivatives, with no supplied differentiability hypothesis. -/
theorem all_order (β : ℝ) (S : Finset (Edge (Vertex n)))
    (f : I → PlaquetteIndex n → ℝ) (w : List I) :
    FiniteSourceWickJets.mixedDeriv w (generating n β S f) 0 =
      ∫ U, MvPolynomial.eval (fun i => centered n β (f i) U)
        (FiniteSourceWickJets.wickWord (noiseMatrix n β S f) w)
        ∂wilsonLaw n Q character β 2 :=
  FiniteSourceWickJets.mixedDeriv_zero (wilsonLaw n Q character β 2)
    (fun i => centered n β (f i)) (fun i => centered_continuous n β (f i))
    (noiseMatrix n β S f) (noiseMatrix_symmetric n β S f) w

theorem first_zero (β : ℝ) (S : Finset (Edge (Vertex n)))
    (f : I → PlaquetteIndex n → ℝ) (i : I) :
    FiniteSourceWickJets.mixedDeriv [i] (generating n β S f) 0 = 0 := by
  rw [all_order]
  simp only [FiniteSourceWickJets.wickWord_one, MvPolynomial.eval_X]
  exact centered_mean n β (f i)

/-- The corrected mixed second derivative is exactly the actual retained-law covariance.
This is a proved second-order identity, not an identification of higher retained moments. -/
theorem second_retained (β : ℝ) (S : Finset (Edge (Vertex n)))
    (f : I → PlaquetteIndex n → ℝ) (i j : I) :
    FiniteSourceWickJets.mixedDeriv [i,j] (generating n β S f) 0 =
      GibbsCrossCovariance.covariance (WilsonCrossCovariance.retainedLaw n Q character β 2 S)
        (WilsonBlockNoiseKernel.retained n β S (f i))
        (WilsonBlockNoiseKernel.retained n β S (f j)) := by
  have h := FiniteSourceWickJets.mixed_second (wilsonLaw n Q character β 2)
    (fun i => centered n β (f i)) (fun i => centered_continuous n β (f i))
    (noiseMatrix n β S f) (noiseMatrix_symmetric n β S f) i j
  change FiniteSourceWickJets.mixedDeriv [i,j] (generating n β S f) 0 =
    (∫ U, centered n β (f i) U * centered n β (f j) U ∂wilsonLaw n Q character β 2) -
      noiseMatrix n β S f i j at h
  rw [h]
  have hc := GibbsCrossCovariance.covariance_eq_centered (wilsonLaw n Q character β 2)
    (WilsonBlockNoiseKernel.source n (f i)) (WilsonBlockNoiseKernel.source n (f j))
    (WilsonBlockNoiseKernel.source_continuous n (f i))
    (WilsonBlockNoiseKernel.source_continuous n (f j))
  change GibbsCrossCovariance.covariance (wilsonLaw n Q character β 2)
    (WilsonBlockNoiseKernel.source n (f i)) (WilsonBlockNoiseKernel.source n (f j)) =
    (∫ U, centered n β (f i) U * centered n β (f j) U ∂wilsonLaw n Q character β 2) at hc
  rw [← hc]
  exact WilsonBlockNoiseKernel.covariance_sub_retained n β S (f i) (f j)

/-- Separation on the actual independent block preserves this mixed second form.
No reflection transformation law for the full corrected generating function is inferred. -/
theorem second_separated (β : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : WilsonIndependentBlocks.Independent n (S.image (WilsonIndependentBlocks.edgeCoord n)))
    (f : I → PlaquetteIndex n → ℝ) (i j : I)
    (hsep : WilsonSeparatedSources.SeparatedOnBlock n S (f i) (f j)) :
    FiniteSourceWickJets.mixedDeriv [i,j] (generating n β S f) 0 =
      GibbsCrossCovariance.covariance (wilsonLaw n Q character β 2)
        (WilsonBlockNoiseKernel.source n (f i)) (WilsonBlockNoiseKernel.source n (f j)) := by
  rw [second_retained]
  have h := WilsonBlockNoiseKernel.covariance_sub_retained n β S (f i) (f j)
  have hS' : WilsonIndependentBlocks.Independent n
      (@Finset.image _ _ (WilsonBlockNoiseKernel.linkDecidableEq n)
        (WilsonIndependentBlocks.edgeCoord n) S) := by
    convert hS using 1
    ext e
    simp
  rw [WilsonBlockNoiseKernel.bilinear_separated_zero n β S hS' (f i) (f j) hsep,
    sub_zero] at h
  exact h.symm

end
end UnifiedTheory.Clay.YangMills.WilsonNoiseSourceJets
