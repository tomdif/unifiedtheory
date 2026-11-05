/- Volume-uniform fractional integrability of the actual positive star
remainder. The spatial average is controlled even for extensive blocks.
This is an L^(1/2) bound, not uniform integrability of the full remainder
or exponential control needed to remove it from a Gibbs action. -/
import UnifiedTheory.Clay.YangMills.SU2StableStarRemainder
import UnifiedTheory.Clay.YangMills.WilsonBadStapleProbability

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonRemainderDensity
noncomputable section
open MeasureTheory Filter RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples
open WilsonIndependentBlocks SU2StarEnergy WilsonEnergyDensity WilsonBadStapleProbability
open SU2GeneralStarApproximation SU2StableStarRemainder
open scoped Quaternion Topology

def envelope (β : ℝ) : ℝ := 18 * Real.sqrt β * energyEnvelope β

theorem envelope_nonneg (β : ℝ) (hβ : 0 < β) : 0 ≤ envelope β :=
  mul_nonneg (by positivity) (energyEnvelope_nonneg β hβ)

theorem envelope_square_bound (t : ℝ) (ht : 1 ≤ t) :
    envelope (t ^ 2) ≤ 28224 / t ^ 3 + 96 * (Real.log 7 + 2 * Real.log t) / t := by
  have ht0 : 0 < t := by linarith
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
  have hl : Real.log (2 * t ^ 2 + 5) ≤ Real.log 7 + 2 * Real.log t := by
    have h := Real.log_le_log (by positivity : 0 < 2 * t ^ 2 + 5)
      (show 2 * t ^ 2 + 5 ≤ 7 * t ^ 2 by linarith)
    rw [Real.log_mul (by norm_num : (7 : ℝ) ≠ 0) (pow_ne_zero 2 ht0.ne'), Real.log_pow] at h
    exact h
  have he : envelope (t ^ 2) = 28224 / t ^ 3 + 96 * Real.log (2 * t ^ 2 + 5) / t := by
    unfold envelope energyEnvelope
    rw [Real.sqrt_sq ht0.le]
    field_simp
    ring
  rw [he]
  gcongr

theorem envelope_tendsto : Tendsto envelope atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => 28224 / t ^ 3) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by decide : 3 ≠ 0))).const_mul
        (28224 : ℝ)
  have hi : Tendsto (fun t : ℝ => Real.log 7 / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (Real.log 7)
  have hl : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hu : Tendsto (fun t : ℝ =>
      28224 / t ^ 3 + 96 * (Real.log 7 + 2 * Real.log t) / t) atTop (𝓝 0) := by
    convert hp.add ((hi.add (hl.const_mul 2)).const_mul 96) using 1
    · ext t; ring
    · norm_num
  have hs : Tendsto (fun t : ℝ => envelope (t ^ 2)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact envelope_nonneg _ (by positivity)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact envelope_square_bound t ht
  apply (hs.comp Real.tendsto_sqrt_atTop).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with β hβ
  simp only [Function.comp_apply, Real.sq_sqrt hβ]

theorem sqrt_positiveRemainder_bound (β : ℝ) (hβ : 0 < β) (A : ℍ) (hA : ‖A‖ ≤ 6) :
    Real.sqrt (positiveRemainder β A) ≤ Real.sqrt β * (6 - ‖A‖) := by
  have hr := positiveRemainder_bounds β hβ A hA
  apply (Real.sqrt_le_iff).mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hA), ?_⟩
  rw [mul_pow, Real.sq_sqrt hβ.le]
  nlinarith [mul_nonneg hβ.le (sq_nonneg (6 - ‖A‖))]

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

def fractionalRemainder (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (U : Configuration (Vertex n) Q) : ℝ :=
  Real.sqrt (positiveRemainder β (stapleField n x μ U))

omit [Fact (1 < n)] in
theorem fractionalRemainder_continuous (x : Vertex n) (μ : Fin 4) (β : ℝ) :
    Continuous (fractionalRemainder n x μ β) :=
  Real.continuous_sqrt.comp
    ((continuous_const.max (error_continuous β)).comp (stapleField_continuous n x μ))

theorem fractionalRemainder_energy_bound (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (hβ : 0 < β) (U : Configuration (Vertex n) Q) :
    fractionalRemainder n x μ β U ≤ Real.sqrt β / 2 * starEnergy n x μ U := by
  have h := sqrt_positiveRemainder_bound β hβ (stapleField n x μ U)
    (stapleField_norm_le_six n x μ U)
  have he := mul_le_mul_of_nonneg_left (starEnergy_lower n x μ U) (Real.sqrt_nonneg β)
  unfold fractionalRemainder
  nlinarith

theorem fractionalRemainder_mean_bound (x : Vertex n) (μ : Fin 4) (β : ℝ) (hβ : 0 < β) :
    (∫ U, fractionalRemainder n x μ β U ∂wilsonLaw n Q character β 2) ≤ envelope β := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  have hi := (fractionalRemainder_continuous n x μ β).integrable_of_hasCompactSupport
    (μ := wilsonLaw n Q character β 2) (HasCompactSupport.of_compactSpace _)
  have hj := (starEnergy_continuous n x μ).integrable_of_hasCompactSupport
    (μ := wilsonLaw n Q character β 2) (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ U, Real.sqrt β / 2 * starEnergy n x μ U ∂wilsonLaw n Q character β 2 :=
      integral_mono hi (hj.const_mul _) (fractionalRemainder_energy_bound n x μ β hβ)
    _ = Real.sqrt β / 2 * ∫ U, starEnergy n x μ U ∂wilsonLaw n Q character β 2 :=
      integral_const_mul _ _
    _ ≤ Real.sqrt β / 2 * (36 * energyEnvelope β) :=
      mul_le_mul_of_nonneg_left (starEnergy_mean_bound n β hβ x μ) (by positivity)
    _ = envelope β := by unfold envelope; ring

/-- Mean square-root remainder per selected link; defined as zero for an empty block. -/
def density (S : Finset (Link n)) (β : ℝ) (U : Configuration (Vertex n) Q) : ℝ :=
  (∑ e ∈ S, fractionalRemainder n e.1 e.2 β U) / S.card

omit [Fact (1 < n)] in
theorem density_continuous (S : Finset (Link n)) (β : ℝ) : Continuous (density n S β) :=
  (continuous_finset_sum S (fun e _ => fractionalRemainder_continuous n e.1 e.2 β)).div_const _

omit [NeZero n] [Fact (1 < n)] in
theorem density_nonneg (S : Finset (Link n)) (β : ℝ) (U : Configuration (Vertex n) Q) :
    0 ≤ density n S β U := by
  unfold density fractionalRemainder
  positivity

/-- No cardinality or volume factor: this applies to the entire lattice. -/
theorem density_mean_bound (S : Finset (Link n)) (β : ℝ) (hβ : 0 < β) :
    (∫ U, density n S β U ∂wilsonLaw n Q character β 2) ≤ envelope β := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  by_cases hS : S.Nonempty
  · have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    unfold density
    rw [integral_div, integral_finset_sum]
    · apply (div_le_iff₀ hc).mpr
      calc
        _ ≤ ∑ _e ∈ S, envelope β :=
          Finset.sum_le_sum (fun e _ => fractionalRemainder_mean_bound n e.1 e.2 β hβ)
        _ = envelope β * S.card := by simp [mul_comm]
    · intro e _
      exact (fractionalRemainder_continuous n e.1 e.2 β).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simpa [he, density] using envelope_nonneg β hβ

theorem density_mean_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (S : ∀ i, Finset (Link (N i))) (β : ι → ℝ) (hβ : Tendsto β l atTop) :
    Tendsto (fun i => ∫ U, density (N i) (S i) (β i) U
      ∂wilsonLaw (N i) Q character (β i) 2) l (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (envelope_tendsto.comp hβ)
  · exact Eventually.of_forall (fun i => integral_nonneg (density_nonneg (N i) (S i) (β i)))
  · filter_upwards [hβ.eventually (eventually_gt_atTop (0 : ℝ))] with i hi
    exact density_mean_bound (N i) (S i) (β i) hi

/-- A bounded truncation of the full remainder has a vanishing first moment. -/
theorem truncated_mean_bound (x : Vertex n) (μ : Fin 4) (β L : ℝ)
    (hβ : 0 < β) (hL : 0 ≤ L) :
    (∫ U, min L (positiveRemainder β (stapleField n x μ U))
      ∂wilsonLaw n Q character β 2) ≤ Real.sqrt L * envelope β := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  have hc : Continuous (fun U => min L (positiveRemainder β (stapleField n x μ U))) :=
    continuous_const.min
      ((continuous_const.max (error_continuous β)).comp (stapleField_continuous n x μ))
  calc
    _ ≤ ∫ U, Real.sqrt L * fractionalRemainder n x μ β U
        ∂wilsonLaw n Q character β 2 := by
      apply integral_mono
        (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (((fractionalRemainder_continuous n x μ β).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)).const_mul _)
      intro U
      let R := positiveRemainder β (stapleField n x μ U)
      have hR : 0 ≤ R := le_max_left _ _
      change min L R ≤ Real.sqrt L * Real.sqrt R
      by_cases h : L ≤ R
      · rw [min_eq_left h]
        calc
          L = Real.sqrt L * Real.sqrt L := (Real.mul_self_sqrt hL).symm
          _ ≤ Real.sqrt L * Real.sqrt R :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg _)
      · rw [min_eq_right (le_of_not_ge h)]
        calc
          R = Real.sqrt R * Real.sqrt R := (Real.mul_self_sqrt hR).symm
          _ ≤ Real.sqrt L * Real.sqrt R :=
            mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (le_of_not_ge h))
              (Real.sqrt_nonneg _)
    _ = Real.sqrt L * ∫ U, fractionalRemainder n x μ β U
        ∂wilsonLaw n Q character β 2 := integral_const_mul _ _
    _ ≤ Real.sqrt L * envelope β := mul_le_mul_of_nonneg_left
      (fractionalRemainder_mean_bound n x μ β hβ) (Real.sqrt_nonneg _)

/-- Empirical fraction of selected links whose positive remainder exceeds epsilon. -/
def badFraction (S : Finset (Link n)) (β ε : ℝ)
    (U : Configuration (Vertex n) Q) : ℝ :=
  ((S.filter (fun e => ε ≤ positiveRemainder β (stapleField n e.1 e.2 U))).card : ℝ) / S.card

omit [NeZero n] [Fact (1 < n)] in
theorem badFraction_le_density (S : Finset (Link n)) (β ε : ℝ)
    (U : Configuration (Vertex n) Q) :
    Real.sqrt ε * badFraction n S β ε U ≤ density n S β U := by
  classical
  let B := S.filter (fun e => ε ≤ positiveRemainder β (stapleField n e.1 e.2 U))
  have hsum : Real.sqrt ε * B.card ≤ ∑ e ∈ S, fractionalRemainder n e.1 e.2 β U := by
    calc
      _ = ∑ _e ∈ B, Real.sqrt ε := by simp [mul_comm]
      _ ≤ ∑ e ∈ B, fractionalRemainder n e.1 e.2 β U := by
        apply Finset.sum_le_sum
        intro e he
        exact Real.sqrt_le_sqrt (Finset.mem_filter.mp he).2
      _ ≤ ∑ e ∈ S, fractionalRemainder n e.1 e.2 β U :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun e _ _ => Real.sqrt_nonneg _)
  unfold density badFraction
  simpa only [B, mul_div_assoc] using div_le_div_of_nonneg_right hsum (Nat.cast_nonneg S.card)

/-- No independence assumption and no factor proportional to the number of links. -/
theorem badFraction_probability_bound (S : Finset (Link n)) (β ε η : ℝ)
    (hβ : 0 < β) (hε : 0 < ε) (hη : 0 < η) :
    (wilsonLaw n Q character β 2).real {U | η ≤ badFraction n S β ε U} ≤
      envelope β / (Real.sqrt ε * η) := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  have hs : {U | η ≤ badFraction n S β ε U} ⊆
      {U | Real.sqrt ε * η ≤ density n S β U} := by
    intro U hU
    exact (mul_le_mul_of_nonneg_left hU (Real.sqrt_nonneg _)).trans
      (badFraction_le_density n S β ε U)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (density_nonneg n S β))
    ((density_continuous n S β).integrable_of_hasCompactSupport
      (μ := wilsonLaw n Q character β 2) (HasCompactSupport.of_compactSpace _))
    (Real.sqrt ε * η)
  have hc : 0 < Real.sqrt ε * η := mul_pos (Real.sqrt_pos.mpr hε) hη
  apply (le_div_iff₀ hc).mpr
  calc
    _ ≤ Real.sqrt ε * η *
        (wilsonLaw n Q character β 2).real {U | Real.sqrt ε * η ≤ density n S β U} := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (measureReal_mono (μ := wilsonLaw n Q character β 2) hs) hc.le
    _ ≤ _ := hm.trans (density_mean_bound n S β hβ)

theorem badFraction_probability_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (S : ∀ i, Finset (Link (N i))) (β : ι → ℝ) (hβ : Tendsto β l atTop)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    Tendsto (fun i => (wilsonLaw (N i) Q character (β i) 2).real
      {U | η ≤ badFraction (N i) (S i) (β i) ε U}) l (𝓝 0) := by
  have hu := (envelope_tendsto.comp hβ).div_const (Real.sqrt ε * η)
  simp only [zero_div] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  · filter_upwards [hβ.eventually (eventually_gt_atTop (0 : ℝ))] with i hi
    exact badFraction_probability_bound (N i) (S i) (β i) ε η hi hε hη

end
end UnifiedTheory.Clay.YangMills.WilsonRemainderDensity
