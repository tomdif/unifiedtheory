/- One actual pure-gauge score is projected out of the local response
family. Every physical response is unchanged, while the Gram quadratic
form decreases by a constructed positive semidefinite rank-one term. -/
import UnifiedTheory.Clay.YangMills.CompactScoreResidual
import UnifiedTheory.Clay.YangMills.WilsonCollectiveGram

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGaugeResidual
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalInfluence
open WilsonVarianceResponse WilsonPhysicalResponse WilsonPhysicalVariance WilsonRowGram
open WilsonSymmetricLinkChange CompactDensityEntropy CompactLikelihoodVariance

variable (n : ℕ) [NeZero n]

def nuisance (β : ℝ) (hβ : 0 ≤ β) (h : SliceGauge n Q) (u v : Slice n) : ℝ :=
  likelihood n β hβ u (gaugeSlice h u) v - 1

theorem nuisance_continuous (β : ℝ) (hβ : 0 ≤ β) (h : SliceGauge n Q) (u : Slice n) :
    Continuous (nuisance n β hβ h u) :=
  (likelihood_continuous n β hβ u _).sub continuous_const

theorem nuisance_mean_zero (β : ℝ) (hβ : 0 ≤ β) (h : SliceGauge n Q) (u : Slice n) :
    (∫ v, nuisance n β hβ h u v ∂rowLaw n β hβ u) = 0 := by
  letI := rowLaw_probability n β hβ u
  unfold nuisance
  rw [integral_sub (continuous_integrable _ _ (likelihood_continuous n β hβ u _))
    (integrable_const 1), likelihood_mean]
  simp

/-- Orthogonality to every continuous physical source is exact for the actual row law. -/
theorem nuisance_physical_response (β : ℝ) (hβ : 0 ≤ β)
    (h : SliceGauge n Q) (u : Slice n) (f : C(Slice n, ℝ))
    (hinv : ∀ k v, f (gaugeSlice k v) = f v) :
    (∫ v, nuisance n β hβ h u v*(f v-∫ w, f w ∂rowLaw n β hβ u)
      ∂rowLaw n β hβ u) = 0 := by
  letI := rowLaw_probability n β hβ u
  simp only [nuisance]
  rw [centered_likelihood _ _ f (likelihood_continuous n β hβ u _)
    f.continuous (likelihood_mean n β hβ u _), likelihood_reweight,
    rowMean_gauge n β hβ f hinv]
  exact sub_self _

variable {I : Type*}

def weightedScore (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (u : Slice n) (i : I) (v : Slice n) : ℝ :=
  amplitudes i * score n β hβ (edges i) (rotations i) u v

theorem weightedScore_continuous (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (u : Slice n) (i : I) :
    Continuous (weightedScore n β hβ edges rotations amplitudes u i) :=
  continuous_const.mul (score_continuous n β hβ (edges i) (rotations i) u)

def residualScore (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (h : SliceGauge n Q) (u : Slice n)
    (i : I) : Slice n → ℝ :=
  CompactScoreResidual.residual (rowLaw n β hβ u)
    (weightedScore n β hβ edges rotations amplitudes u i) (nuisance n β hβ h u)

theorem residualScore_continuous (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (h : SliceGauge n Q) (u : Slice n) (i : I) :
    Continuous (residualScore n β hβ edges rotations amplitudes h u i) :=
  CompactScoreResidual.residual_continuous _ _ _
    (weightedScore_continuous n β hβ edges rotations amplitudes u i)
    (nuisance_continuous n β hβ h u)

def nuisanceVariance (β : ℝ) (hβ : 0 ≤ β) (h : SliceGauge n Q) (u : Slice n) : ℝ :=
  CompactScoreResidual.pair (rowLaw n β hβ u) (nuisance n β hβ h u) (nuisance n β hβ h u)

theorem residualScore_mean_zero (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (h : SliceGauge n Q) (u : Slice n) (i : I) :
    (∫ v, residualScore n β hβ edges rotations amplitudes h u i v ∂rowLaw n β hβ u) = 0 := by
  letI := rowLaw_probability n β hβ u
  unfold residualScore CompactScoreResidual.residual
  have hi := integral_sub
    (continuous_integrable (rowLaw n β hβ u) _
      (weightedScore_continuous n β hβ edges rotations amplitudes u i))
    ((continuous_integrable (rowLaw n β hβ u) _ (nuisance_continuous n β hβ h u)).const_mul
      (CompactScoreResidual.coefficient (rowLaw n β hβ u)
        (weightedScore n β hβ edges rotations amplitudes u i) (nuisance n β hβ h u)))
  rw [hi, integral_const_mul, nuisance_mean_zero]
  simp only [weightedScore, integral_const_mul, score_mean_zero, mul_zero, sub_self]

def nuisanceCovariance (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (h : SliceGauge n Q) (u : Slice n) (i : I) : ℝ :=
  CompactScoreResidual.pair (rowLaw n β hβ u)
    (weightedScore n β hβ edges rotations amplitudes u i) (nuisance n β hβ h u)

def residualMatrix (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (h : SliceGauge n Q) (u : Slice n)
    (i j : I) : ℝ :=
  CompactGramResponse.gram (rowLaw n β hβ u)
    (residualScore n β hβ edges rotations amplitudes h u) i j

/-- The subtraction is an actual covariance regression, including the zero-variance case. -/
theorem residualMatrix_formula (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (h : SliceGauge n Q) (u : Slice n) (i j : I) :
    residualMatrix n β hβ edges rotations amplitudes h u i j =
      WilsonCollectiveGram.matrix n β hβ edges rotations amplitudes u i j -
        nuisanceCovariance n β hβ edges rotations amplitudes h u i *
          nuisanceCovariance n β hβ edges rotations amplitudes h u j /
            nuisanceVariance n β hβ h u := by
  letI := rowLaw_probability n β hβ u
  have hpair := CompactScoreResidual.residual_pair (rowLaw n β hβ u)
    (weightedScore n β hβ edges rotations amplitudes u i)
    (weightedScore n β hβ edges rotations amplitudes u j) (nuisance n β hβ h u)
    (weightedScore_continuous n β hβ edges rotations amplitudes u i)
    (weightedScore_continuous n β hβ edges rotations amplitudes u j)
    (nuisance_continuous n β hβ h u)
  change _ = CompactGramResponse.gram (rowLaw n β hβ u)
    (fun k v => amplitudes k*score n β hβ (edges k) (rotations k) u v) i j - _ at hpair
  rw [WilsonCollectiveGram.matrix_gram] at hpair
  exact hpair

theorem residualScore_orthogonal (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (h : SliceGauge n Q) (u : Slice n) (i : I) :
    CompactScoreResidual.pair (rowLaw n β hβ u)
      (residualScore n β hβ edges rotations amplitudes h u i) (nuisance n β hβ h u) = 0 := by
  letI := rowLaw_probability n β hβ u
  exact CompactScoreResidual.residual_orthogonal _ _ _
    (weightedScore_continuous n β hβ edges rotations amplitudes u i)
    (nuisance_continuous n β hβ h u)

/-- The original physical response survives the projection exactly. -/
theorem response_preserved (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (h : SliceGauge n Q) (u : Slice n) (i : I)
    (f : C(Slice n, ℝ)) (hinv : ∀ k v, f (gaugeSlice k v) = f v) :
    (∫ v, residualScore n β hβ edges rotations amplitudes h u i v *
      (f v-∫ w, f w ∂rowLaw n β hβ u) ∂rowLaw n β hβ u) =
        amplitudes i * (step n β hβ f (shift n (edges i) (rotations i) u)-step n β hβ f u) := by
  letI := rowLaw_probability n β hβ u
  rw [residualScore, CompactScoreResidual.residual_response _ _ _ f
    (weightedScore_continuous n β hβ edges rotations amplitudes u i)
    (nuisance_continuous n β hβ h u) f.continuous (nuisance_physical_response n β hβ h u f hinv)]
  simp only [weightedScore, mul_assoc, integral_const_mul, score_response]
  rfl

variable [Fintype I]

theorem residualMatrix_positive (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (h : SliceGauge n Q) (u : Slice n) (a : I → ℝ) :
    0 ≤ ∑ i, ∑ j, a i*a j*residualMatrix n β hβ edges rotations amplitudes h u i j := by
  letI := rowLaw_probability n β hβ u
  exact CompactGramResponse.gram_positive _ _
    (residualScore_continuous n β hβ edges rotations amplitudes h u) a

/-- The reduced quadratic form is always bounded above by the original actual one. -/
theorem residualMatrix_le (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (h : SliceGauge n Q) (u : Slice n) (a : I → ℝ) :
    (∑ i, ∑ j, a i*a j*residualMatrix n β hβ edges rotations amplitudes h u i j) ≤
      ∑ i, ∑ j, a i*a j*WilsonCollectiveGram.matrix n β hβ edges rotations amplitudes u i j := by
  letI := rowLaw_probability n β hβ u
  have hc := CompactScoreResidual.residual_gram_le (rowLaw n β hβ u)
    (weightedScore n β hβ edges rotations amplitudes u) (nuisance n β hβ h u)
    (weightedScore_continuous n β hβ edges rotations amplitudes u)
    (nuisance_continuous n β hβ h u) a
  have he (i j : I) : CompactGramResponse.gram (rowLaw n β hβ u)
      (weightedScore n β hβ edges rotations amplitudes u) i j =
        WilsonCollectiveGram.matrix n β hβ edges rotations amplitudes u i j :=
    WilsonCollectiveGram.matrix_gram n β hβ edges rotations amplitudes u i j
  simp_rw [he] at hc
  exact hc

end
end UnifiedTheory.Clay.YangMills.WilsonGaugeResidual
