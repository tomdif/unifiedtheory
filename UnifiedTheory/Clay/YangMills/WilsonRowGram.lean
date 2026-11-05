/- The actual local likelihood scores and their Gram matrix. Disjoint
input changes have an exact mixed partition-ratio formula; disjoint
support does not assert independence under the interacting row law. -/
import UnifiedTheory.Clay.YangMills.WilsonVarianceResponse
import UnifiedTheory.Clay.YangMills.CompactGramResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonRowGram
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalGauge
open WilsonTemporalInfluence WilsonPhysicalResponse WilsonVarianceResponse
open WilsonSymmetricLinkChange CompactDensityEntropy CompactLikelihoodVariance

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def score (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3) (q : Q)
    (u v : Slice n) : ℝ := likelihood n β hβ u (shift n e q u) v - 1

theorem score_continuous (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    Continuous (score n β hβ e q u) :=
  (likelihood_continuous n β hβ u _).sub continuous_const

theorem score_mean_zero (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    (∫ v, score n β hβ e q u v ∂rowLaw n β hβ u) = 0 := by
  letI := rowLaw_probability n β hβ u
  unfold score
  rw [integral_sub (continuous_integrable _ _ (likelihood_continuous n β hβ u _))
    (integrable_const 1), likelihood_mean]
  simp

/-- Each score is local in the output even though its normalization uses the full row law. -/
theorem score_local (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u v w : Slice n) (hvw : v e = w e) :
    score n β hβ e q u v = score n β hβ e q u w := by
  unfold score likelihood
  rw [WilsonTemporalInfluence.likelihood_local n β hβ {e} (shift n e q u) u v w
    (fun j hj => shift_away n e q u j (by simpa only [Finset.mem_singleton] using hj))
    (fun j hj => by simpa only [Finset.mem_singleton.mp hj] using hvw)]

theorem score_response (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) (f : C(Slice n, ℝ)) :
    (∫ v, score n β hβ e q u v*(f v-∫ w, f w ∂rowLaw n β hβ u)
      ∂rowLaw n β hβ u) = rowMean n β hβ f (shift n e q u)-rowMean n β hβ f u := by
  letI := rowLaw_probability n β hβ u
  simp only [score]
  rw [centered_likelihood _ _ f (likelihood_continuous n β hβ u _)
    f.continuous (likelihood_mean n β hβ u _), likelihood_reweight]
  rfl

def gram (β : ℝ) (hβ : 0 ≤ β) (e d : SpatialVertex n × Fin 3) (q r : Q)
    (u : Slice n) : ℝ :=
  ∫ v, score n β hβ e q u v*score n β hβ d r u v ∂rowLaw n β hβ u

theorem gram_symm (β : ℝ) (hβ : 0 ≤ β) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (u : Slice n) : gram n β hβ e d q r u = gram n β hβ d e r q u := by
  simp only [gram, mul_comm]

theorem gram_diagonal_nonneg (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    0 ≤ gram n β hβ e e q q u :=
  integral_nonneg (fun v => mul_self_nonneg (score n β hβ e q u v))

theorem gram_diagonal_bound (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    gram n β hβ e e q q u ≤ coefficient β q := by
  letI := rowLaw_probability n β hβ u
  have hb : 0 ≤ Real.exp (4*β*‖(q : Quaternion ℝ)-1‖)-1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))
  have hp (v : Slice n) : (score n β hβ e q u v)^2 ≤ coefficient β q := by
    simpa only [sq_abs, score, coefficient] using
      (sq_le_sq₀ (abs_nonneg (score n β hβ e q u v)) hb).mpr
        (likelihood_shift_bound n β hβ e q u v)
  have h := integral_mono
    (continuous_integrable (rowLaw n β hβ u) _ ((score_continuous n β hβ e q u).pow 2))
    (integrable_const (coefficient β q)) hp
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  simpa only [gram, score, pow_two, coefficient] using h

theorem gram_product (β : ℝ) (hβ : 0 ≤ β) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (u : Slice n) :
    gram n β hβ e d q r u + 1 = ∫ v,
      likelihood n β hβ u (shift n e q u) v * likelihood n β hβ u (shift n d r u) v
      ∂rowLaw n β hβ u := by
  letI := rowLaw_probability n β hβ u
  let a := likelihood n β hβ u (shift n e q u)
  let b := likelihood n β hβ u (shift n d r u)
  have ha := continuous_integrable (rowLaw n β hβ u) a (likelihood_continuous n β hβ u _)
  have hb := continuous_integrable (rowLaw n β hβ u) b (likelihood_continuous n β hβ u _)
  have hab := continuous_integrable (rowLaw n β hβ u) (fun v => a v*b v)
    ((likelihood_continuous n β hβ u _).mul (likelihood_continuous n β hβ u _))
  have he : gram n β hβ e d q r u = ∫ v, (a v*b v-a v)-b v+1 ∂rowLaw n β hβ u := by
    apply integral_congr_ae
    filter_upwards with v
    change (a v-1)*(b v-1) = _
    ring
  have h1 := integral_add ((hab.sub ha).sub hb) (integrable_const (1 : ℝ))
  have h2 := integral_sub (hab.sub ha) hb
  have h3 := integral_sub hab ha
  simp only [Pi.sub_apply] at h1 h2 h3
  rw [he, h1, h2, h3]
  dsimp only [a, b]
  rw [likelihood_mean, likelihood_mean]
  simp

/-- Distinct input links factor before output integration, including the actual output ground. -/
theorem rowWeight_cross (β : ℝ) (hβ : 0 ≤ β) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (hed : e ≠ d) (u v : Slice n) :
    rowWeight n β hβ (shift n e q (shift n d r u)) v * rowWeight n β hβ u v =
      rowWeight n β hβ (shift n e q u) v * rowWeight n β hβ (shift n d r u) v := by
  have hu (z : Slice n) (j) (hj : j ∉ ({e} : Finset _)) : shift n e q z j = z j :=
    shift_away n e q z j (by simpa only [Finset.mem_singleton] using hj)
  rw [rowWeight_tilt n β hβ {e} _ _ v (hu (shift n d r u)),
    rowWeight_tilt n β hβ {e} (shift n e q u) u v (hu u)]
  have ht : tilt n β {e} (shift n e q (shift n d r u)) (shift n d r u) v =
      tilt n β {e} (shift n e q u) u v := by
    simp only [tilt, Finset.sum_singleton, shift_at, shift_away n d r u e hed]
  rw [ht]
  ring

/-- The off-diagonal Gram entry is a genuine mixed partition response, not zero by locality. -/
theorem gram_mixed_partition (β : ℝ) (hβ : 0 ≤ β) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (hed : e ≠ d) (u : Slice n) :
    gram n β hβ e d q r u + 1 =
      (rowPartition n β hβ u * rowPartition n β hβ (shift n e q (shift n d r u))) /
        (rowPartition n β hβ (shift n e q u) * rowPartition n β hβ (shift n d r u)) := by
  rw [gram_product, rowLaw_integral]
  have he (v : Slice n) : rawTransition n β hβ u v *
      (likelihood n β hβ u (shift n e q u) v * likelihood n β hβ u (shift n d r u) v) =
      (rowPartition n β hβ u /
        (rowPartition n β hβ (shift n e q u) * rowPartition n β hβ (shift n d r u))) *
          rowWeight n β hβ (shift n e q (shift n d r u)) v := by
    unfold likelihood
    simp only [rawTransition_quotient]
    have hc := rowWeight_cross n β hβ e d q r hed u v
    field_simp [(rowWeight_pos n β hβ u v).ne', (rowPartition_pos n β hβ u).ne',
      (rowPartition_pos n β hβ (shift n e q u)).ne',
      (rowPartition_pos n β hβ (shift n d r u)).ne']
    nlinarith
  simp_rw [he]
  rw [integral_const_mul]
  change _ * rowPartition n β hβ (shift n e q (shift n d r u)) = _
  ring

end
end UnifiedTheory.Clay.YangMills.WilsonRowGram
