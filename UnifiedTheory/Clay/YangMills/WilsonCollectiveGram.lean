/- Actual correlated likelihood responses obey a collective Schur bound.
The matrix condition and the separate lower coercivity condition remain
explicit. Their uniform weak-coupling estimates are not asserted. -/
import UnifiedTheory.Clay.YangMills.WilsonRowGram
import UnifiedTheory.Clay.YangMills.WilsonDissipationIteration

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCollectiveGram
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalInfluence
open WilsonPhysicalResponse WilsonPhysicalVariance WilsonSymmetricLinkChange
open WilsonDissipationIteration CompactDensityEntropy WilsonRowGram

variable (n : ℕ) [NeZero n] {I : Type*} [Fintype I]

def matrix (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (u : Slice n) (i j : I) : ℝ :=
  amplitudes i*amplitudes j*gram n β hβ (edges i) (edges j) (rotations i) (rotations j) u

omit [Fintype I] in
theorem matrix_gram (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (u : Slice n) (i j : I) :
    CompactGramResponse.gram (rowLaw n β hβ u)
      (fun k v => amplitudes k*score n β hβ (edges k) (rotations k) u v) i j =
        matrix n β hβ edges rotations amplitudes u i j := by
  unfold CompactGramResponse.gram matrix gram
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  ring

omit [Fintype I] in
theorem matrix_symm (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (u : Slice n) (i j : I) :
    matrix n β hβ edges rotations amplitudes u i j =
      matrix n β hβ edges rotations amplitudes u j i := by
  unfold matrix
  rw [gram_symm n β hβ (edges i) (edges j)]
  ring

theorem matrix_positive (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (u : Slice n) (a : I → ℝ) :
    0 ≤ ∑ i, ∑ j, a i*a j*matrix n β hβ edges rotations amplitudes u i j := by
  letI := rowLaw_probability n β hβ u
  simp_rw [← matrix_gram]
  exact CompactGramResponse.gram_positive _ _
    (fun i => continuous_const.mul (score_continuous n β hβ (edges i) (rotations i) u)) a

/-- A row bound on the actual Gram matrix replaces the sum of separate direction constants. -/
theorem conditional_collective (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (u : Slice n) (f : C(Slice n, ℝ))
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hrow : ∀ i, ∑ j, |matrix n β hβ edges rotations amplitudes u i j| ≤ κ) :
    (∑ i, (amplitudes i)^2 *
      (step n β hβ f (shift n (edges i) (rotations i) u)-step n β hβ f u)^2) ≤
        κ * rowVariance n β hβ f u := by
  letI := rowLaw_probability n β hβ u
  have h := CompactGramResponse.collective_response (rowLaw n β hβ u)
    (fun i v => amplitudes i*score n β hβ (edges i) (rotations i) u v)
    (fun i => continuous_const.mul (score_continuous n β hβ (edges i) (rotations i) u))
    f f.continuous κ hκ (by simpa only [matrix_gram] using hrow)
  simp_rw [mul_assoc, integral_const_mul, score_response, mul_pow] at h
  exact h

def energy (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (f : C(Slice n, ℝ)) : ℝ :=
  ∑ i, (amplitudes i)^2 * responseEnergy n β hβ (edges i) (rotations i) f

theorem energy_nonneg (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (f : C(Slice n, ℝ)) :
    0 ≤ energy n β hβ edges rotations amplitudes f :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _)
    (responseEnergy_nonneg n β hβ (edges i) (rotations i) f))

theorem energy_integral (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (f : C(Slice n, ℝ)) :
    energy n β hβ edges rotations amplitudes f =
      ∫ u, ∑ i, (amplitudes i)^2 *
        (f (shift n (edges i) (rotations i) u)-f u)^2 ∂WilsonGroundHeatBath.groundLaw n β hβ := by
  letI := WilsonGroundHeatBath.groundLaw_probability n β hβ
  have hi (i : I) : Integrable (fun u => (amplitudes i)^2 *
      (f (shift n (edges i) (rotations i) u)-f u)^2)
      (WilsonGroundHeatBath.groundLaw n β hβ) := continuous_integrable _ _
    (continuous_const.mul (((f.continuous.comp (shift_continuous n _ _)).sub f.continuous).pow 2))
  rw [integral_finset_sum _ (fun i _ => hi i)]
  simp only [energy, responseEnergy, integral_const_mul]

/-- This needs a uniform row bound at the actual baseline inputs, not just an averaged matrix. -/
theorem energy_le_loss (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hrow : ∀ u i, ∑ j, |matrix n β hβ edges rotations amplitudes u i j| ≤ κ)
    (f : C(Slice n, ℝ)) :
    energy n β hβ edges rotations amplitudes (step n β hβ f) ≤ κ * loss n β hβ f := by
  letI := WilsonGroundHeatBath.groundLaw_probability n β hβ
  rw [energy_integral]
  have hl : Continuous (fun u => ∑ i, (amplitudes i)^2 *
      (step n β hβ f (shift n (edges i) (rotations i) u)-step n β hβ f u)^2) :=
    continuous_finset_sum _ (fun i _ => continuous_const.mul
      ((((step n β hβ f).continuous.comp (shift_continuous n _ _)).sub
        (step n β hβ f).continuous).pow 2))
  have h := integral_mono (continuous_integrable (WilsonGroundHeatBath.groundLaw n β hβ) _ hl)
    ((continuous_integrable _ _ (rowVariance_continuous n β hβ f)).const_mul κ)
    (fun u => conditional_collective n β hβ edges rotations amplitudes u f κ hκ (hrow u))
  rw [integral_const_mul, mean_rowVariance_eq_loss] at h
  exact h

/-- The same collective coefficient pays for the whole time interval. -/
theorem sum_energy_le_loss (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hrow : ∀ u i, ∑ j, |matrix n β hβ edges rotations amplitudes u i j| ≤ κ)
    (f : C(Slice n, ℝ)) (k : ℕ) :
    (∑ j ∈ Finset.range k,
      energy n β hβ edges rotations amplitudes (flow n β hβ f (j+1))) ≤
        κ * (variance n β hβ f-variance n β hβ (flow n β hβ f k)) := by
  calc
    _ ≤ ∑ j ∈ Finset.range k, κ * loss n β hβ (flow n β hβ f j) :=
      Finset.sum_le_sum (fun j _ =>
        energy_le_loss n β hβ edges rotations amplitudes κ hκ hrow _)
    _ = _ := by rw [← Finset.mul_sum, loss_telescope]

theorem sum_energy_bound (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hrow : ∀ u i, ∑ j, |matrix n β hβ edges rotations amplitudes u i j| ≤ κ)
    (f : C(Slice n, ℝ)) (k : ℕ) :
    (∑ j ∈ Finset.range k,
      energy n β hβ edges rotations amplitudes (flow n β hβ f (j+1))) ≤
        κ * variance n β hβ f := by
  have h := sum_energy_le_loss n β hβ edges rotations amplitudes κ hκ hrow f k
  nlinarith [mul_nonneg hκ (variance_nonneg n β hβ (flow n β hβ f k))]

/-- Both analytic hypotheses remain explicit: an upper Gram bound and a lower response bound. -/
theorem slab_contraction (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hrow : ∀ u i, ∑ j, |matrix n β hβ edges rotations amplitudes u i j| ≤ κ)
    (f : C(Slice n, ℝ)) (k : ℕ)
    (hcoerce : variance n β hβ (flow n β hβ f k) ≤
      ∑ j ∈ Finset.range k, energy n β hβ edges rotations amplitudes (flow n β hβ f (j + 1))) :
    variance n β hβ (flow n β hβ f k) ≤ (κ/(1+κ))*variance n β hβ f := by
  have h := hcoerce.trans (sum_energy_le_loss n β hβ edges rotations amplitudes κ hκ hrow f k)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 1+κ)).mpr
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonCollectiveGram
