/- Physical transfer dissipation can use the signed Gram form after an
actual gauge-score projection. An absolute distant row sum is sufficient
but is not required by this criterion. Uniform coercivity remains open. -/
import UnifiedTheory.Clay.YangMills.WilsonGaugeResidual

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonResidualDissipation
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalInfluence
open WilsonPhysicalVariance WilsonDissipationIteration WilsonGaugeResidual
open WilsonSymmetricLinkChange CompactDensityEntropy

variable (n : ℕ) [NeZero n] {I : Type*} [Fintype I]

/-- Any old raw absolute-row bound also bounds the reduced signed form. -/
theorem reduced_bound_of_rows (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (h : SliceGauge n Q) (u : Slice n)
    (κ : ℝ) (hrow : ∀ i, ∑ j, |WilsonCollectiveGram.matrix n β hβ
      edges rotations amplitudes u i j| ≤ κ) (a : I → ℝ) :
    (∑ i, ∑ j, a i * a j *
        residualMatrix n β hβ edges rotations amplitudes h u i j) ≤
      κ * ∑ i, (a i) ^ 2 :=
  (residualMatrix_le n β hβ edges rotations amplitudes h u a).trans
    (CompactGramResponse.quadratic_le_rows _
      (WilsonCollectiveGram.matrix_symm n β hβ edges rotations amplitudes u) κ hrow a)

/-- Only the signed quadratic form of the physical residual scores is bounded here. -/
theorem conditional_collective (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (h : SliceGauge n Q) (u : Slice n)
    (f : C(Slice n, ℝ)) (hinv : ∀ k v, f (gaugeSlice k v) = f v) (κ : ℝ) (hκ : 0 ≤ κ)
    (hquad : ∀ a : I → ℝ,
      (∑ i, ∑ j, a i * a j *
        residualMatrix n β hβ edges rotations amplitudes h u i j) ≤
        κ * ∑ i, (a i) ^ 2) :
    (∑ i, (amplitudes i)^2 *
      (step n β hβ f (shift n (edges i) (rotations i) u)-step n β hβ f u)^2) ≤
        κ * rowVariance n β hβ f u := by
  letI := rowLaw_probability n β hβ u
  have hc := CompactScoreResidual.collective_of_quadratic (rowLaw n β hβ u)
    (residualScore n β hβ edges rotations amplitudes h u)
    (residualScore_continuous n β hβ edges rotations amplitudes h u)
    f f.continuous κ hκ hquad
  simp_rw [response_preserved n β hβ edges rotations amplitudes h u _ f hinv, mul_pow] at hc
  exact hc

/-- The gauge choice may depend on the input. No regular gauge fixing is used or asserted. -/
theorem energy_le_loss (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (gauge : Slice n → SliceGauge n Q)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hquad : ∀ u (a : I → ℝ),
      (∑ i, ∑ j, a i * a j *
        residualMatrix n β hβ edges rotations amplitudes (gauge u) u i j) ≤
        κ * ∑ i, (a i) ^ 2)
    (f : C(Slice n, ℝ)) (hinv : ∀ k v, f (gaugeSlice k v) = f v) :
    WilsonCollectiveGram.energy n β hβ edges rotations amplitudes (step n β hβ f) ≤
      κ*loss n β hβ f := by
  letI := WilsonGroundHeatBath.groundLaw_probability n β hβ
  rw [WilsonCollectiveGram.energy_integral]
  have hl : Continuous (fun u => ∑ i, (amplitudes i)^2 *
      (step n β hβ f (shift n (edges i) (rotations i) u)-step n β hβ f u)^2) :=
    continuous_finset_sum _ (fun i _ => continuous_const.mul
      ((((step n β hβ f).continuous.comp (shift_continuous n _ _)).sub
        (step n β hβ f).continuous).pow 2))
  have hc := integral_mono (continuous_integrable (WilsonGroundHeatBath.groundLaw n β hβ) _ hl)
    ((continuous_integrable _ _ (rowVariance_continuous n β hβ f)).const_mul κ)
    (fun u => conditional_collective n β hβ edges rotations amplitudes (gauge u) u f hinv
      κ hκ (hquad u))
  rw [integral_const_mul, mean_rowVariance_eq_loss] at hc
  exact hc

theorem time_sum_le_loss (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (gauge : Slice n → SliceGauge n Q)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hquad : ∀ u (a : I → ℝ),
      (∑ i, ∑ j, a i * a j *
        residualMatrix n β hβ edges rotations amplitudes (gauge u) u i j) ≤
        κ * ∑ i, (a i) ^ 2)
    (f : C(Slice n, ℝ)) (hinv : ∀ k v, f (gaugeSlice k v) = f v) (k : ℕ) :
    (∑ j ∈ Finset.range k,
      WilsonCollectiveGram.energy n β hβ edges rotations amplitudes (flow n β hβ f (j+1))) ≤
        κ*(variance n β hβ f-variance n β hβ (flow n β hβ f k)) := by
  calc
    _ ≤ ∑ j ∈ Finset.range k, κ*loss n β hβ (flow n β hβ f j) :=
      Finset.sum_le_sum (fun j _ => energy_le_loss n β hβ edges rotations amplitudes gauge
        κ hκ hquad _ (flow_gauge n β hβ f hinv j))
    _ = _ := by rw [← Finset.mul_sum, loss_telescope]

/-- The independent observability constant multiplies the reduced upper coefficient. -/
theorem slab_contraction (β : ℝ) (hβ : 0 ≤ β) (edges : I → SpatialVertex n × Fin 3)
    (rotations : I → Q) (amplitudes : I → ℝ) (gauge : Slice n → SliceGauge n Q)
    (κ C : ℝ) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hquad : ∀ u (a : I → ℝ),
      (∑ i, ∑ j, a i * a j *
        residualMatrix n β hβ edges rotations amplitudes (gauge u) u i j) ≤
        κ * ∑ i, (a i) ^ 2)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v) (k : ℕ)
    (hcoerce : variance n β hβ (flow n β hβ f k) ≤ C *
      ∑ j ∈ Finset.range k,
        WilsonCollectiveGram.energy n β hβ edges rotations amplitudes (flow n β hβ f (j + 1))) :
    variance n β hβ (flow n β hβ f k) ≤ (C*κ/(1+C*κ))*variance n β hβ f := by
  have h := hcoerce.trans (mul_le_mul_of_nonneg_left
    (time_sum_le_loss n β hβ edges rotations amplitudes gauge κ hκ hquad f hinv k) hC)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 1+C*κ)).mpr
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonResidualDissipation
