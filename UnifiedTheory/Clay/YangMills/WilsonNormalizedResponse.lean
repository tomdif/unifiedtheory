/- Exact row normalization improves the local response coefficient. The
same Haar family and the actual ground-law variance loss are retained. -/
import UnifiedTheory.Clay.YangMills.CompactNormalizedLikelihood
import UnifiedTheory.Clay.YangMills.WilsonHaarLinkResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonNormalizedResponse
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalGauge
open WilsonTemporalInfluence WilsonPhysicalResponse WilsonRowGeometry
open WilsonSymmetricLinkChange WilsonVarianceResponse WilsonPhysicalVariance
open CompactDensityEntropy CompactNormalizedLikelihood
open scoped Quaternion

def rangeCoefficient (R : ℝ) : ℝ := (R-1)^2/(4*R)

theorem rangeCoefficient_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ rangeCoefficient R :=
  div_nonneg (sq_nonneg _) (by positivity)

theorem rangeCoefficient_mono (R S : ℝ) (hR : 1 ≤ R) (hRS : R ≤ S) :
    rangeCoefficient R ≤ rangeCoefficient S := by
  unfold rangeCoefficient
  apply (div_le_div_iff₀ (by positivity : 0 < 4*R) (by nlinarith : 0 < 4*S)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hRS) (show 0 ≤ R*S-1 by nlinarith)]

def coefficient (β : ℝ) (q : Q) : ℝ :=
  rangeCoefficient (Real.exp (4*β*‖(q : ℍ)-1‖))

theorem coefficient_nonneg (β : ℝ) (q : Q) : 0 ≤ coefficient β q :=
  rangeCoefficient_nonneg _ (Real.exp_pos _).le

def haarCap (β : ℝ) : ℝ := rangeCoefficient (Real.exp (8*β))

theorem haarCap_nonneg (β : ℝ) : 0 ≤ haarCap β :=
  rangeCoefficient_nonneg _ (Real.exp_pos _).le

theorem coefficient_cap (β : ℝ) (hβ : 0 ≤ β) (q : Q) : coefficient β q ≤ haarCap β := by
  have hq : ‖(q : ℍ)-1‖ ≤ 2 := by
    simpa only [QuaternionSymmetricChange.unit_norm, norm_one, one_add_one_eq_two] using
      norm_sub_le (q : ℍ) (1 : ℍ)
  exact rangeCoefficient_mono _ _ (Real.one_le_exp_iff.mpr (by positivity))
    (Real.exp_le_exp.mpr (by nlinarith))

variable (n : ℕ) [NeZero n]

/-- The common partition ratio is kept instead of bounding it independently.
Consequently the normalized likelihood has range ratio exp(4 beta d). -/
theorem likelihood_range (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n) :
    ∃ m : ℝ, 0 < m ∧ ∀ v, likelihood n β hβ u w v ∈
      Set.Icc m (Real.exp (4*β*inputCost n u w)*m) := by
  let E := Real.exp (2*β*inputCost n u w)
  let z := rowPartition n β hβ u / rowPartition n β hβ w
  have hE : 0 < E := Real.exp_pos _
  have hz : 0 < z := div_pos (rowPartition_pos n β hβ u) (rowPartition_pos n β hβ w)
  refine ⟨(1/E)*z, by positivity, ?_⟩
  intro v
  have hw : rowWeight n β hβ w v ≤ E * rowWeight n β hβ u v := by
    simpa only [E, inputCost_symm n w u] using rowWeight_geometric n β hβ w u v
  have hu := rowWeight_geometric n β hβ u w v
  have hl : 1/E ≤ rowWeight n β hβ w v / rowWeight n β hβ u v :=
    (div_le_div_iff₀ hE (rowWeight_pos n β hβ u v)).mpr (by simpa [E, mul_comm] using hu)
  have hh : rowWeight n β hβ w v / rowWeight n β hβ u v ≤ E :=
    (div_le_iff₀ (rowWeight_pos n β hβ u v)).mpr hw
  have he : likelihood n β hβ u w v =
      (rowWeight n β hβ w v / rowWeight n β hβ u v)*z := by
    unfold likelihood
    simp_rw [rawTransition_quotient]
    dsimp only [z]
    field_simp
  have hexp : Real.exp (4*β*inputCost n u w) = E^2 := by
    dsimp only [E]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have htop : Real.exp (4*β*inputCost n u w)*((1/E)*z) = E*z := by
    rw [hexp]
    field_simp
  rw [he, htop]
  exact ⟨mul_le_mul_of_nonneg_right hl hz.le, mul_le_mul_of_nonneg_right hh hz.le⟩

/-- A better coefficient for the actual conditional variance, at every input. -/
theorem response_sq_conditional_variance (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) (f : C(Slice n, ℝ)) :
    (rowMean n β hβ f (shift n e q u)-rowMean n β hβ f u)^2 ≤
      coefficient β q * ProbabilityTheory.variance f (rowLaw n β hβ u) := by
  letI := rowLaw_probability n β hβ u
  obtain ⟨m, _, hb⟩ := likelihood_range n β hβ u (shift n e q u)
  rw [inputCost_symm n u, shift_cost] at hb
  have h := response_sq_le_range_ratio (rowLaw n β hβ u)
    (likelihood n β hβ u (shift n e q u)) f
    (likelihood_continuous n β hβ u _) f.continuous (likelihood_mean n β hβ u _)
    (Real.exp (4*β*‖(q : ℍ)-1‖)) m (Real.exp_pos _) hb
  rw [likelihood_reweight] at h
  exact h

/-- The improved response is paid for by the same stationary variance loss. -/
theorem response_le_loss (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (f : C(Slice n, ℝ)) :
    responseEnergy n β hβ e q (step n β hβ f) ≤ coefficient β q * loss n β hβ f := by
  letI := WilsonGroundHeatBath.groundLaw_probability n β hβ
  have hf := (step n β hβ f).continuous
  have h := integral_mono
    (continuous_integrable (WilsonGroundHeatBath.groundLaw n β hβ) _
      (((hf.comp (shift_continuous n e q)).sub hf).pow 2))
    ((continuous_integrable (WilsonGroundHeatBath.groundLaw n β hβ) _
      (rowVariance_continuous n β hβ f)).const_mul (coefficient β q))
    (fun u => response_sq_conditional_variance n β hβ e q u f)
  rw [integral_const_mul, mean_rowVariance_eq_loss] at h
  exact h

theorem total_upper (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    WilsonHaarLinkResponse.totalEnergy n β hβ (step n β hβ f) ≤
      (Fintype.card (SpatialVertex n × Fin 3) : ℝ) * haarCap β * loss n β hβ f := by
  have he (e : SpatialVertex n × Fin 3) :
      (∫ q, responseEnergy n β hβ e q (step n β hβ f) ∂RegulatedGauge.compactHaar Q) ≤
        haarCap β * loss n β hβ f := by
    have h := integral_mono (continuous_integrable (RegulatedGauge.compactHaar Q) _
      (WilsonHaarLinkResponse.responseEnergy_continuous n β hβ e (step n β hβ f)))
      (integrable_const _) (fun q => (response_le_loss n β hβ e q f).trans
        (mul_le_mul_of_nonneg_right (coefficient_cap β hβ q) (loss_nonneg n β hβ f)))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h
  calc
    _ ≤ ∑ _e : SpatialVertex n × Fin 3, haarCap β * loss n β hβ f :=
      Finset.sum_le_sum (fun e _ => he e)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Same lower factorization and same Haar family; the upper coefficient is improved. -/
theorem slab_contraction (β : ℝ) (hβ : 0 ≤ β) (A : ℝ) (hA : 0 ≤ A)
    (hfactor : ∀ F : C(Slice n, ℝ), (∀ h U, F (gaugeSlice h U) = F U) →
      variance n β hβ F ≤ A * WilsonHaarLinkResponse.totalConditionalVariance n β hβ F)
    (f : C(Slice n, ℝ)) (hinv : ∀ h U, f (gaugeSlice h U) = f U)
    (k : ℕ) (hk : 0 < k) :
    variance n β hβ (WilsonDissipationIteration.flow n β hβ f k) ≤
      (A*((Fintype.card (SpatialVertex n × Fin 3) : ℝ)*haarCap β) /
        ((k : ℝ)+A*((Fintype.card (SpatialVertex n × Fin 3) : ℝ)*haarCap β))) *
          variance n β hβ f :=
  WilsonHaarLinkResponse.slab_contraction n β hβ A _ hA
    (mul_nonneg (Nat.cast_nonneg _) (haarCap_nonneg β)) hfactor
    (fun F _ => total_upper n β hβ F) f hinv k hk

end
end UnifiedTheory.Clay.YangMills.WilsonNormalizedResponse
