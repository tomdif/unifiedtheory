/- An explicit two-atom probability family using the actual SU(2) Haar
remainder. Its staple deficit mean is 1/beta and its square-root remainder
mean vanishes, but its remainder mean tends to 1/6 and its exponential
moment diverges. This is not a Wilson law or a counterexample to Yang-Mills;
it disproves the inference from the current concentration input alone. -/
import UnifiedTheory.Clay.YangMills.SU2StableStarRemainder
import UnifiedTheory.Clay.YangMills.LocalGibbsComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.StarRemainderIntegrabilityObstruction
noncomputable section
open MeasureTheory Filter SU2GeneralStarApproximation SU2StableStarRemainder
open SU2AlignedGaussianApproximation
open scoped Quaternion Topology

def rareStaple : ℍ := (5 : ℝ) • (1 : ℍ)
def vacuumStaple : ℍ := (6 : ℝ) • (1 : ℍ)

theorem rareStaple_norm : ‖rareStaple‖ = 5 := by norm_num [rareStaple, norm_smul]
theorem vacuumStaple_norm : ‖vacuumStaple‖ = 6 := by norm_num [vacuumStaple, norm_smul]

theorem staples_ne : rareStaple ≠ vacuumStaple := by
  intro h
  have he := congrArg norm h
  rw [rareStaple_norm, vacuumStaple_norm] at he
  norm_num at he

/-- At beta >= 1 these two weights are nonnegative and sum to one. -/
def law (β : ℝ) : Measure ℍ :=
  ENNReal.ofReal (1 / β) • Measure.dirac rareStaple +
    ENNReal.ofReal (1 - 1 / β) • Measure.dirac vacuumStaple

theorem law_probability (β : ℝ) (hβ : 1 ≤ β) : IsProbabilityMeasure (law β) := by
  have hp : 0 ≤ 1 / β := by positivity
  have hq : 0 ≤ 1 - 1 / β := sub_nonneg.mpr ((div_le_one (by linarith)).mpr hβ)
  constructor
  simp only [law, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp hq]
  norm_num

theorem law_integrable (β : ℝ) (f : ℍ → ℝ) : Integrable f (law β) :=
  ((integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)

theorem expectation_eq (β : ℝ) (hβ : 1 ≤ β) (f : ℍ → ℝ) :
    (∫ A, f A ∂law β) = f rareStaple / β + (1 - 1 / β) * f vacuumStaple := by
  have hp : 0 ≤ 1 / β := by positivity
  have hq : 0 ≤ 1 - 1 / β := sub_nonneg.mpr ((div_le_one (by linarith)).mpr hβ)
  rw [law, integral_add_measure
    ((integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hp,
    ENNReal.toReal_ofReal hq, smul_eq_mul]
  ring

theorem deficit_mean (β : ℝ) (hβ : 1 ≤ β) :
    (∫ A, (6 - ‖A‖) ∂law β) = 1 / β := by
  rw [expectation_eq β hβ, rareStaple_norm, vacuumStaple_norm]
  ring

theorem vacuum_remainder (β : ℝ) : positiveRemainder β vacuumStaple = 0 := by
  unfold positiveRemainder error quadratic
  rw [vacuumStaple_norm]
  norm_num [vacuumStaple]

/-- The exact radial correction is bounded by 3/10 at norm five. -/
theorem rare_remainder_bounds (β : ℝ) (hβ : 0 < β) :
    β / 6 - 3 / 10 ≤ positiveRemainder β rareStaple ∧
      positiveRemainder β rareStaple ≤ β / 6 := by
  have hc := (abs_le.mp (radial_correction_bound β 5 hβ (by norm_num) (by norm_num))).1
  have he : β / 6 - 3 / 10 ≤ error β rareStaple := by
    rw [error_radial, quadratic, rareStaple_norm]
    norm_num at hc ⊢
    linarith
  refine ⟨he.trans (le_max_right _ _), ?_⟩
  have hu := (positiveRemainder_bounds β hβ rareStaple (by rw [rareStaple_norm]; norm_num)).2
  norm_num [rareStaple_norm] at hu
  exact hu

theorem remainder_mean_bounds (β : ℝ) (hβ : 1 ≤ β) :
    1 / 6 - 3 / (10 * β) ≤ (∫ A, positiveRemainder β A ∂law β) ∧
      (∫ A, positiveRemainder β A ∂law β) ≤ 1 / 6 := by
  have hb : 0 < β := by linarith
  have h := rare_remainder_bounds β hb
  rw [expectation_eq β hβ, vacuum_remainder, mul_zero, add_zero]
  constructor
  · apply (le_div_iff₀ hb).mpr
    calc
      _ = β / 6 - 3 / 10 := by field_simp
      _ ≤ _ := h.1
  · exact (div_le_iff₀ hb).mpr (by linarith [h.2])

/-- The positive remainder fails to tend to zero in L1. -/
theorem remainder_mean_tendsto :
    Tendsto (fun β => ∫ A, positiveRemainder β A ∂law β) atTop (𝓝 (1 / 6)) := by
  have hl : Tendsto (fun β : ℝ => 1 / 6 - 3 / (10 * β)) atTop (𝓝 (1 / 6)) := by
    convert (tendsto_const_nhds (x := (1 / 6 : ℝ))).sub
      (tendsto_inv_atTop_zero.const_mul (3 / 10 : ℝ)) using 1
    · ext β; ring
    · norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
    exact (remainder_mean_bounds β hβ).1
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
    exact (remainder_mean_bounds β hβ).2

/-- Every fixed tail threshold retains asymptotic first-moment mass 1/6. -/
theorem tail_mean_tendsto (L : ℝ) :
    Tendsto (fun β => ∫ A, ({A | L < positiveRemainder β A} : Set ℍ).indicator
      (positiveRemainder β) A ∂law β) atTop (𝓝 (1 / 6)) := by
  apply remainder_mean_tendsto.congr'
  filter_upwards [eventually_ge_atTop (max 1 (6 * (L + 1)))] with β hβ
  have hb : 1 ≤ β := (le_max_left _ _).trans hβ
  have hL : 6 * (L + 1) ≤ β := (le_max_right _ _).trans hβ
  have hr : L < positiveRemainder β rareStaple := by
    linarith [(rare_remainder_bounds β (by linarith)).1]
  rw [expectation_eq β hb, expectation_eq β hb]
  simp [Set.indicator_apply, vacuum_remainder, hr]

theorem sqrt_remainder_mean_bound (β : ℝ) (hβ : 1 ≤ β) :
    (∫ A, Real.sqrt (positiveRemainder β A) ∂law β) ≤ 1 / Real.sqrt β := by
  have hb : 0 < β := by linarith
  have hr := rare_remainder_bounds β hb
  rw [expectation_eq β hβ, vacuum_remainder, Real.sqrt_zero, mul_zero, add_zero]
  calc
    _ ≤ Real.sqrt β / β := div_le_div_of_nonneg_right
      (Real.sqrt_le_sqrt (hr.2.trans (by linarith))) hb.le
    _ = 1 / Real.sqrt β := by
      have hs := Real.sq_sqrt hb.le
      have hs0 : Real.sqrt β ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
      field_simp
      nlinarith

theorem sqrt_remainder_mean_tendsto :
    Tendsto (fun β => ∫ A, Real.sqrt (positiveRemainder β A) ∂law β) atTop (𝓝 0) := by
  have hu : Tendsto (fun β : ℝ => 1 / Real.sqrt β) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall (fun β => integral_nonneg (fun A => Real.sqrt_nonneg _))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
    exact sqrt_remainder_mean_bound β hβ

theorem exponential_mean_lower (β : ℝ) (hβ : 4 ≤ β) :
    Real.exp (β / 12) / β ≤ ∫ A, Real.exp (positiveRemainder β A) ∂law β := by
  have hb : 0 < β := by linarith
  have hr : β / 12 ≤ positiveRemainder β rareStaple := by
    linarith [(rare_remainder_bounds β hb).1]
  rw [expectation_eq β (by linarith), vacuum_remainder, Real.exp_zero, mul_one]
  have hq : 0 ≤ 1 - 1 / β := sub_nonneg.mpr ((div_le_one hb).mpr (by linarith))
  exact (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hr) hb.le).trans
    (le_add_of_nonneg_right hq)

theorem exponential_mean_tendsto :
    Tendsto (fun β => ∫ A, Real.exp (positiveRemainder β A) ∂law β) atTop atTop := by
  have hh : Tendsto (fun β : ℝ => Real.exp (β / 12) / β) atTop atTop := by
    have hscale : Tendsto (fun β : ℝ => β / 12) atTop atTop :=
      tendsto_id.atTop_div_const (by norm_num)
    convert ((Real.tendsto_exp_div_pow_atTop 1).comp hscale).atTop_div_const
      (by norm_num : (0 : ℝ) < 12) using 1
    ext β
    simp only [Function.comp_apply, pow_one]
    ring
  apply tendsto_atTop_mono' _ ?_ hh
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with β hβ
  exact exponential_mean_lower β hβ

theorem rare_probability (β : ℝ) (hβ : 1 ≤ β) :
    (law β).real {rareStaple} = 1 / β := by
  have h := expectation_eq β hβ (({rareStaple} : Set ℍ).indicator (fun _ => (1 : ℝ)))
  simpa [integral_indicator (measurableSet_singleton rareStaple), staples_ne.symm] using h

theorem rare_probability_tendsto :
    Tendsto (fun β => (law β).real {rareStaple}) atTop (𝓝 0) := by
  apply (show Tendsto (fun β : ℝ => 1 / β) atTop (𝓝 0) by
    simpa only [one_div] using tendsto_inv_atTop_zero).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
  exact (rare_probability β hβ).symm

/-- Removing a positive remainder from an action multiplies its weight by exp(R). -/
def tiltedLaw (β : ℝ) : Measure ℍ :=
  LocalGibbsComparison.weightedLaw (law β) (fun A => Real.exp (positiveRemainder β A))

theorem exponential_mean_pos (β : ℝ) (hβ : 1 ≤ β) :
    0 < ∫ A, Real.exp (positiveRemainder β A) ∂law β := by
  have hb : 0 < β := by linarith
  rw [expectation_eq β hβ, vacuum_remainder, Real.exp_zero, mul_one]
  exact add_pos_of_pos_of_nonneg (div_pos (Real.exp_pos _) hb)
    (sub_nonneg.mpr ((div_le_one hb).mpr hβ))

theorem tiltedLaw_probability (β : ℝ) (hβ : 1 ≤ β) : IsProbabilityMeasure (tiltedLaw β) :=
  LocalGibbsComparison.weightedLaw_probability (law β) _
    (Real.continuous_exp.comp (continuous_const.max (error_continuous β))).measurable
    (law_integrable β _) (fun _ => (Real.exp_pos _).le) (exponential_mean_pos β hβ)

theorem tilted_rare_probability (β : ℝ) (hβ : 1 ≤ β) :
    (tiltedLaw β).real {rareStaple} =
      (1 + (β - 1) / Real.exp (positiveRemainder β rareStaple))⁻¹ := by
  letI := tiltedLaw_probability β hβ
  have hb : 0 < β := by linarith
  let r := Real.exp (positiveRemainder β rareStaple)
  have hr : 0 < r := Real.exp_pos _
  have hz : r + β - 1 ≠ 0 := by linarith
  have h := LocalGibbsComparison.weighted_integral (law β)
    (fun A => Real.exp (positiveRemainder β A))
    (Real.continuous_exp.comp (continuous_const.max (error_continuous β))).measurable
    (fun _ => (Real.exp_pos _).le) (exponential_mean_pos β hβ)
    (({rareStaple} : Set ℍ).indicator (fun _ => (1 : ℝ)))
  rw [expectation_eq β hβ, expectation_eq β hβ] at h
  simp only [Set.indicator_of_mem (Set.mem_singleton _),
    Set.indicator_of_notMem (show vacuumStaple ∉ ({rareStaple} : Set ℍ) from staples_ne.symm),
    mul_one, mul_zero, add_zero, vacuum_remainder, Real.exp_zero] at h
  have hh : (tiltedLaw β).real {rareStaple} = r / β / (r / β + (1 - 1 / β)) := by
    simpa only [tiltedLaw, r, integral_indicator (measurableSet_singleton rareStaple),
      setIntegral_const, smul_eq_mul, mul_one] using h
  rw [hh]
  change r / β / (r / β + (1 - 1 / β)) = (1 + (β - 1) / r)⁻¹
  field_simp

theorem tilted_rare_probability_tendsto :
    Tendsto (fun β => (tiltedLaw β).real {rareStaple}) atTop (𝓝 1) := by
  have hdecay : Tendsto (fun β : ℝ => β / Real.exp (β / 12)) atTop (𝓝 0) := by
    have hscale : Tendsto (fun β : ℝ => β / 12) atTop atTop :=
      tendsto_id.atTop_div_const (by norm_num)
    convert ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale).const_mul 12 using 1
    · ext β
      simp only [Function.comp_apply, pow_one, Real.exp_neg]
      ring
    · norm_num
  have hratio : Tendsto (fun β : ℝ =>
      (β - 1) / Real.exp (positiveRemainder β rareStaple)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdecay
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
      exact div_nonneg (sub_nonneg.mpr hβ) (Real.exp_pos _).le
    · filter_upwards [eventually_ge_atTop (4 : ℝ)] with β hβ
      have hb : 0 < β := by linarith
      have hr : β / 12 ≤ positiveRemainder β rareStaple := by
        linarith [(rare_remainder_bounds β hb).1]
      exact (div_le_div_of_nonneg_right (by linarith : β - 1 ≤ β) (Real.exp_pos _).le).trans
        (div_le_div_of_nonneg_left hb.le (Real.exp_pos _) (Real.exp_le_exp.mpr hr))
  have hi := ((tendsto_const_nhds (x := (1 : ℝ))).add hratio).inv₀ (by norm_num)
  simp only [add_zero, inv_one] at hi
  apply hi.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
  exact (tilted_rare_probability β hβ).symm

theorem reweighting_probability_separation :
    Tendsto (fun β => (tiltedLaw β).real {rareStaple} - (law β).real {rareStaple})
      atTop (𝓝 1) := by
  simpa only [sub_zero] using tilted_rare_probability_tendsto.sub rare_probability_tendsto

end
end UnifiedTheory.Clay.YangMills.StarRemainderIntegrabilityObstruction
