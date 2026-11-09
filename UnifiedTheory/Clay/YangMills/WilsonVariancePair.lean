/- Two outputs of the actual Wilson row represent its variance. Multiplying
by the stationary ground density cancels the middle ground amplitude exactly. -/
import UnifiedTheory.Clay.YangMills.CompactVariancePair
import UnifiedTheory.Clay.YangMills.WilsonVarianceProfileCost

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonVariancePair
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonTemporalInfluence WilsonPhysicalVariance WilsonVarianceProfile
open WilsonStationaryEntropy CompactDensityEntropy

variable (n : ℕ) [NeZero n]

/-- The middle variable has no unknown ground amplitude in this density. -/
def pairWeight (β : ℝ) (hβ : 0 ≤ β) (u v w : Slice n) : ℝ :=
  rawKernel WilsonSingleLinkStaples.character β 2 u v *
    rawKernel WilsonSingleLinkStaples.character β 2 u w *
      ground n β hβ v * ground n β hβ w / ‖transfer n β‖^2

theorem pairWeight_pos (β : ℝ) (hβ : 0 ≤ β) (u v w : Slice n) :
    0 < pairWeight n β hβ u v w := by
  unfold pairWeight
  exact div_pos (mul_pos (mul_pos (mul_pos (rawKernel_pos _ _ _ _ _)
    (rawKernel_pos _ _ _ _ _)) (ground_pos n β hβ v)) (ground_pos n β hβ w))
    (sq_pos_of_pos (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1)

theorem pairWeight_continuous (β : ℝ) (hβ : 0 ≤ β) :
    Continuous (fun z : Slice n × (Slice n × Slice n) => pairWeight n β hβ z.1 z.2.1 z.2.2) := by
  have hk := rawKernel_continuous WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_continuous β 2 (n := n)
  have hg := (ground n β hβ).continuous
  exact ((((hk.comp (f := fun z : Slice n × (Slice n × Slice n) => (z.1,z.2.1))
    (by fun_prop)).mul
    (hk.comp (f := fun z : Slice n × (Slice n × Slice n) => (z.1,z.2.2)) (by fun_prop))).mul
    (hg.comp (f := fun z : Slice n × (Slice n × Slice n) => z.2.1) (by fun_prop))).mul
    (hg.comp (f := fun z : Slice n × (Slice n × Slice n) => z.2.2) (by fun_prop))).div_const _

theorem ground_cancel (β : ℝ) (hβ : 0 ≤ β) (u v w : Slice n) :
    (ground n β hβ u)^2*rawTransition n β hβ u v*rawTransition n β hβ u w =
      pairWeight n β hβ u v w := by
  unfold rawTransition pairWeight
  field_simp [(ground_pos n β hβ u).ne']

theorem pairWeight_mass (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    (∫ v, ∫ w, pairWeight n β hβ u v w ∂WilsonSlabOperator.measure n
      ∂WilsonSlabOperator.measure n) = (ground n β hβ u)^2 := by
  simp_rw [← ground_cancel, integral_const_mul, rawTransition_mass, mul_one]
  rw [integral_const_mul, rawTransition_mass, mul_one]

/-- Two independent conditional outputs, not independent equilibrium slices. -/
theorem rowVariance_pair (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) (f : C(Slice n, ℝ)) :
    (∫ v, ∫ w, rawTransition n β hβ u v*rawTransition n β hβ u w*(f v-f w)^2
      ∂WilsonSlabOperator.measure n ∂WilsonSlabOperator.measure n)/2 =
      rowVariance n β hβ f u := by
  letI := rowLaw_probability n β hβ u
  let p : C(Slice n, ℝ) := ⟨rawTransition n β hβ u, row_continuous n β hβ u⟩
  have h := CompactVariancePair.normalized_pair (WilsonSlabOperator.measure n) p f
    (rawTransition_mass n β hβ u)
  have hv := CompactLikelihoodVariance.variance_formula (rowLaw n β hβ u) f f.continuous
  simp_rw [rowLaw_integral] at hv
  exact h.trans hv.symm

/-- Exact positive pair representation of the retained ground-weighted profile. -/
theorem amplitude_pair (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) (f : C(Slice n, ℝ)) :
    (ground n β hβ u*profile n β hβ f u)^2 =
      (∫ v, ∫ w, pairWeight n β hβ u v w*(f v-f w)^2
        ∂WilsonSlabOperator.measure n ∂WilsonSlabOperator.measure n)/2 := by
  have he : (∫ v, ∫ w, pairWeight n β hβ u v w*(f v-f w)^2
      ∂WilsonSlabOperator.measure n ∂WilsonSlabOperator.measure n) =
      (ground n β hβ u)^2*(∫ v, ∫ w,
        rawTransition n β hβ u v*rawTransition n β hβ u w*(f v-f w)^2
          ∂WilsonSlabOperator.measure n ∂WilsonSlabOperator.measure n) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with v
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with w
    rw [← ground_cancel]
    ring
  rw [he, mul_div_assoc, rowVariance_pair, mul_pow, profile_square]

end
end UnifiedTheory.Clay.YangMills.WilsonVariancePair
