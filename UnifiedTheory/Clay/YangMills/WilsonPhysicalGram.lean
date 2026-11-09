/- The canonical Gram form of physical likelihood scores. The raw form
splits exactly into this form plus the Gram form of removed components.
It is no larger than any previous one-gauge-score residual form. -/
import UnifiedTheory.Clay.YangMills.WilsonPhysicalScore
import UnifiedTheory.Clay.YangMills.CompactPhysicalProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPhysicalGram
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalInfluence
open WilsonPhysicalVariance WilsonSymmetricLinkChange CompactDensityEntropy

variable (n : ℕ) [NeZero n] {I : Type*}

def physicalScore (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (u : Slice n) (i : I) (v : Slice n) : ℝ :=
  amplitudes i * WilsonPhysicalScore.score n β hβ u (shift n (edges i) (rotations i) u) v

theorem physicalScore_continuous (β : ℝ) (hβ : 0 ≤ β)
    (edges : I → SpatialVertex n × Fin 3) (rotations : I → Q) (amplitudes : I → ℝ)
    (u : Slice n) (i : I) : Continuous (physicalScore n β hβ edges rotations amplitudes u i) :=
  continuous_const.mul (WilsonPhysicalScore.score_continuous n β hβ u _)

theorem physicalScore_gauge (β : ℝ) (hβ : 0 ≤ β)
    (edges : I → SpatialVertex n × Fin 3) (rotations : I → Q) (amplitudes : I → ℝ)
    (u : Slice n) (i : I) (h : SliceGauge n Q) (v : Slice n) :
    physicalScore n β hβ edges rotations amplitudes u i (gaugeSlice h v) =
      physicalScore n β hβ edges rotations amplitudes u i v := by
  simp only [physicalScore, WilsonPhysicalScore.score_gauge]

theorem removed_orthogonal (β : ℝ) (hβ : 0 ≤ β)
    (edges : I → SpatialVertex n × Fin 3) (rotations : I → Q) (amplitudes : I → ℝ)
    (u : Slice n) (i : I) (f : C(Slice n, ℝ))
    (hinv : ∀ h v, f (gaugeSlice h v) = f v) :
    (∫ v, (WilsonGaugeResidual.weightedScore n β hβ edges rotations amplitudes u i v-
      physicalScore n β hβ edges rotations amplitudes u i v)*f v ∂rowLaw n β hβ u) = 0 := by
  calc
    _ = amplitudes i * ∫ v, ((WilsonVarianceResponse.likelihood n β hβ u
        (shift n (edges i) (rotations i) u) v-1)-WilsonPhysicalScore.score n β hβ u
          (shift n (edges i) (rotations i) u) v)*f v ∂rowLaw n β hβ u := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      unfold WilsonGaugeResidual.weightedScore WilsonRowGram.score physicalScore
      ring
    _ = 0 := by rw [WilsonPhysicalScore.residual_orthogonal n β hβ u _ f hinv, mul_zero]

def matrix (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (u : Slice n) (i j : I) : ℝ :=
  CompactGramResponse.gram (rowLaw n β hβ u)
    (physicalScore n β hβ edges rotations amplitudes u) i j

/-- Its entries are computed with the full gauge-averaged transition, not a surrogate law. -/
theorem matrix_full_formula (β : ℝ) (hβ : 0 ≤ β)
    (edges : I → SpatialVertex n × Fin 3) (rotations : I → Q) (amplitudes : I → ℝ)
    (u : Slice n) (i j : I) :
    matrix n β hβ edges rotations amplitudes u i j =
      ∫ v, WilsonGroundLocalComparison.transition n β hβ u v *
        (physicalScore n β hβ edges rotations amplitudes u i v *
          physicalScore n β hβ edges rotations amplitudes u j v) ∂WilsonSlabOperator.measure n :=
  WilsonPhysicalScore.row_integral_physical n β hβ u _
    ((physicalScore_continuous n β hβ edges rotations amplitudes u i).mul
      (physicalScore_continuous n β hβ edges rotations amplitudes u j))
    (fun h v => by rw [physicalScore_gauge, physicalScore_gauge])

/-- The entire removed component is orthogonal to every retained physical score. -/
theorem matrix_decomposition (β : ℝ) (hβ : 0 ≤ β)
    (edges : I → SpatialVertex n × Fin 3) (rotations : I → Q) (amplitudes : I → ℝ)
    (u : Slice n) (i j : I) :
    WilsonCollectiveGram.matrix n β hβ edges rotations amplitudes u i j =
      matrix n β hβ edges rotations amplitudes u i j +
        CompactGramResponse.gram (rowLaw n β hβ u)
          (fun k v => WilsonGaugeResidual.weightedScore n β hβ edges rotations amplitudes u k v-
            physicalScore n β hβ edges rotations amplitudes u k v) i j := by
  letI := rowLaw_probability n β hβ u
  have h := CompactPhysicalProjection.gram_decomposition (rowLaw n β hβ u)
    (WilsonGaugeResidual.weightedScore n β hβ edges rotations amplitudes u)
    (physicalScore n β hβ edges rotations amplitudes u)
    (WilsonGaugeResidual.weightedScore_continuous n β hβ edges rotations amplitudes u)
    (physicalScore_continuous n β hβ edges rotations amplitudes u)
    (fun a b => removed_orthogonal n β hβ edges rotations amplitudes u a
      ⟨_, physicalScore_continuous n β hβ edges rotations amplitudes u b⟩
      (physicalScore_gauge n β hβ edges rotations amplitudes u b)) i j
  change CompactGramResponse.gram (rowLaw n β hβ u)
    (fun k v => amplitudes k*WilsonRowGram.score n β hβ (edges k) (rotations k) u v) i j = _ at h
  rw [WilsonCollectiveGram.matrix_gram] at h
  exact h

theorem response_preserved (β : ℝ) (hβ : 0 ≤ β)
    (edges : I → SpatialVertex n × Fin 3) (rotations : I → Q) (amplitudes : I → ℝ)
    (u : Slice n) (i : I) (f : C(Slice n, ℝ))
    (hinv : ∀ h v, f (gaugeSlice h v) = f v) :
    (∫ v, physicalScore n β hβ edges rotations amplitudes u i v *
      (f v-∫ w, f w ∂rowLaw n β hβ u) ∂rowLaw n β hβ u) =
        amplitudes i*(step n β hβ f (shift n (edges i) (rotations i) u)-step n β hβ f u) := by
  simp only [physicalScore, mul_assoc, integral_const_mul,
    WilsonPhysicalScore.score_response n β hβ u _ f hinv]

theorem physical_pairing (β : ℝ) (hβ : 0 ≤ β)
    (edges : I → SpatialVertex n × Fin 3) (rotations : I → Q) (amplitudes : I → ℝ)
    (u : Slice n) (i : I) (f : C(Slice n, ℝ))
    (hinv : ∀ h v, f (gaugeSlice h v) = f v) :
    (∫ v, physicalScore n β hβ edges rotations amplitudes u i v*f v ∂rowLaw n β hβ u) =
      amplitudes i*(step n β hβ f (shift n (edges i) (rotations i) u)-step n β hβ f u) := by
  simp only [physicalScore, mul_assoc, integral_const_mul,
    WilsonPhysicalScore.score_pairing n β hβ u _ f hinv]

variable [Fintype I]

theorem matrix_positive (β : ℝ) (hβ : 0 ≤ β)
    (edges : I → SpatialVertex n × Fin 3) (rotations : I → Q) (amplitudes : I → ℝ)
    (u : Slice n) (a : I → ℝ) :
    0 ≤ ∑ i, ∑ j, a i*a j*matrix n β hβ edges rotations amplitudes u i j := by
  letI := rowLaw_probability n β hβ u
  exact CompactGramResponse.gram_positive _ _
    (physicalScore_continuous n β hβ edges rotations amplitudes u) a

theorem matrix_le_raw (β : ℝ) (hβ : 0 ≤ β)
    (edges : I → SpatialVertex n × Fin 3) (rotations : I → Q) (amplitudes : I → ℝ)
    (u : Slice n) (a : I → ℝ) :
    (∑ i, ∑ j, a i*a j*matrix n β hβ edges rotations amplitudes u i j) ≤
      ∑ i, ∑ j, a i*a j*WilsonCollectiveGram.matrix n β hβ edges rotations amplitudes u i j := by
  letI := rowLaw_probability n β hβ u
  simp_rw [matrix_decomposition, mul_add, Finset.sum_add_distrib]
  apply le_add_of_nonneg_right
  exact CompactGramResponse.gram_positive _ _ (fun i =>
    (WilsonGaugeResidual.weightedScore_continuous n β hβ edges rotations amplitudes u i).sub
      (physicalScore_continuous n β hβ edges rotations amplitudes u i)) a

/-- Canonical projection improves every single pure-gauge subtraction, with no chosen gauge. -/
theorem matrix_le_residual (β : ℝ) (hβ : 0 ≤ β)
    (edges : I → SpatialVertex n × Fin 3) (rotations : I → Q) (amplitudes : I → ℝ)
    (h : SliceGauge n Q) (u : Slice n) (a : I → ℝ) :
    (∑ i, ∑ j, a i*a j*matrix n β hβ edges rotations amplitudes u i j) ≤
      ∑ i, ∑ j, a i*a j*WilsonGaugeResidual.residualMatrix n β hβ
        edges rotations amplitudes h u i j := by
  letI := rowLaw_probability n β hβ u
  apply CompactPhysicalProjection.gram_le_residual (rowLaw n β hβ u)
    (WilsonGaugeResidual.weightedScore n β hβ edges rotations amplitudes u)
    (physicalScore n β hβ edges rotations amplitudes u) (WilsonGaugeResidual.nuisance n β hβ h u)
    (WilsonGaugeResidual.weightedScore_continuous n β hβ edges rotations amplitudes u)
    (physicalScore_continuous n β hβ edges rotations amplitudes u)
    (WilsonGaugeResidual.nuisance_continuous n β hβ h u)
    (fun i j => removed_orthogonal n β hβ edges rotations amplitudes u i
      ⟨_, physicalScore_continuous n β hβ edges rotations amplitudes u j⟩
      (physicalScore_gauge n β hβ edges rotations amplitudes u j)) (fun j => ?_) a
  let F : C(Slice n, ℝ) :=
    ⟨_, physicalScore_continuous n β hβ edges rotations amplitudes u j⟩
  have hinv : ∀ k v, F (gaugeSlice k v) = F v :=
    physicalScore_gauge n β hβ edges rotations amplitudes u j
  have hp := WilsonPhysicalScore.raw_pairing n β hβ u (gaugeSlice h u) F
  rw [step_gauge n β hβ F hinv, sub_self] at hp
  exact hp

/-- No other continuous score family representing every physical pairing has a smaller form. -/
theorem matrix_minimal (β : ℝ) (hβ : 0 ≤ β)
    (edges : I → SpatialVertex n × Fin 3) (rotations : I → Q) (amplitudes : I → ℝ)
    (u : Slice n) (r : I → Slice n → ℝ) (hr : ∀ i, Continuous (r i))
    (hrep : ∀ i (f : C(Slice n, ℝ)), (∀ h v, f (gaugeSlice h v) = f v) →
      (∫ v, r i v * f v ∂rowLaw n β hβ u) =
        amplitudes i * (step n β hβ f (shift n (edges i) (rotations i) u) - step n β hβ f u))
    (a : I → ℝ) :
    (∑ i, ∑ j, a i*a j*matrix n β hβ edges rotations amplitudes u i j) ≤
      ∑ i, ∑ j, a i*a j*CompactGramResponse.gram (rowLaw n β hβ u) r i j := by
  letI := rowLaw_probability n β hβ u
  apply CompactPhysicalProjection.gram_le (rowLaw n β hβ u) r
    (physicalScore n β hβ edges rotations amplitudes u) hr
    (physicalScore_continuous n β hβ edges rotations amplitudes u) (fun i j => ?_) a
  let F : C(Slice n, ℝ) :=
    ⟨_, physicalScore_continuous n β hβ edges rotations amplitudes u j⟩
  have hF : ∀ h v, F (gaugeSlice h v) = F v :=
    physicalScore_gauge n β hβ edges rotations amplitudes u j
  change (∫ v, (r i v-physicalScore n β hβ edges rotations amplitudes u i v)*F v
    ∂rowLaw n β hβ u) = 0
  simp_rw [sub_mul]
  rw [integral_sub (continuous_integrable (rowLaw n β hβ u) (fun v => r i v*F v)
    ((hr i).mul F.continuous))
    (continuous_integrable (rowLaw n β hβ u)
      (fun v => physicalScore n β hβ edges rotations amplitudes u i v*F v)
      ((physicalScore_continuous n β hβ edges rotations amplitudes u i).mul F.continuous)),
    hrep i F hF, physical_pairing n β hβ edges rotations amplitudes u i F hF, sub_self]

end
end UnifiedTheory.Clay.YangMills.WilsonPhysicalGram
