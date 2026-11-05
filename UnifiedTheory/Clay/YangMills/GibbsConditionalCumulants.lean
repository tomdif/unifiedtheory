/- Exact higher cumulance under the actual compact Gibbs marginal.
The retained/noise cross terms are preserved explicitly; no uniform
continuum estimate or sign is supplied by these finite - cutoff identities. -/
import UnifiedTheory.Clay.YangMills.GibbsCrossCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.GibbsConditionalCumulants
noncomputable section
open MeasureTheory GibbsMarginalTower GibbsCrossCovariance

section OneMeasure
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]

def centeredMoment (F : Y → ℝ) (k : ℕ) : ℝ :=
  ∫ y, (F y - ∫ z, F z ∂ν) ^ k ∂ν

def cumulantThree (F : Y → ℝ) : ℝ := centeredMoment ν F 3

def cumulantFour (F : Y → ℝ) : ℝ :=
  centeredMoment ν F 4 - 3 * (centeredMoment ν F 2) ^ 2

/-- All powers of a shifted continuous compact observable, with explicit binomial factors. -/
theorem integral_shift_power (F : Y → ℝ) (hF : Continuous F) (c : ℝ) (k : ℕ) :
    (∫ y, (F y + c) ^ k ∂ν) =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * c ^ (k - j) * (∫ y, (F y) ^ j ∂ν) := by
  have he (y : Y) : (F y + c) ^ k =
      ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℝ) * c ^ (k - j)) * (F y) ^ j := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul]
  · intro j _
    exact ((hF.pow j).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _

theorem centeredMoment_two_eq_covariance (F : Y → ℝ) (hF : Continuous F) :
    centeredMoment ν F 2 = covariance ν F F := by
  rw [covariance_eq_centered ν F F hF hF]
  simp only [centeredMoment, pow_two]
theorem integral_centered_mul (F G : Y → ℝ) (hF : Continuous F) (hG : Continuous G) :
    (∫ y, (F y-∫ z, F z ∂ν) * G y ∂ν) = covariance ν F G := by
  have hiG := hG.integrable_of_hasCompactSupport (μ := ν)
    (HasCompactSupport.of_compactSpace _)
  have hiFG : Integrable (fun y => F y * G y) ν :=
    (hF.mul hG).integrable_of_hasCompactSupport (μ := ν)
    (HasCompactSupport.of_compactSpace _)
  simp_rw [sub_mul]
  rw [integral_sub hiFG (hiG.const_mul _), integral_const_mul]
  rfl
end OneMeasure

variable {B X : Type*}
  [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μB : Measure B) (μX : Measure X) [IsProbabilityMeasure μB] [IsProbabilityMeasure μX]

/-- The actual centered fiber moment of the eliminated variables. -/
def noiseMoment (A F : B × X → ℝ) (k : ℕ) (b : B) : ℝ :=
  response μX A (fun p => (removed μX A F p) ^ k) b

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem noiseMoment_continuous (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (k : ℕ) : Continuous (noiseMoment μX A F k) :=
  response_continuous μX A _ hA ((removed_continuous μX A F hA hF).pow k)

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B]
  [BorelSpace B] [SecondCountableTopology X] in
theorem noiseMoment_zero (A F : B × X → ℝ) (hA : Continuous A) (b : B) :
    noiseMoment μX A F 0 b = 1 := by
  simp only [noiseMoment, pow_zero]
  exact response_boundary μX A hA (fun _ => 1) b

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem noiseMoment_one (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (b : B) : noiseMoment μX A F 1 b = 0 := by
  simp only [noiseMoment, pow_one]
  exact removed_response μX A F hA hF b

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
/-- The all - order conditional expansion is derived from the normalized actual fiber law. -/
theorem conditional_shift_power (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (c : ℝ) (k : ℕ) (b : B) :
    response μX A (fun p => (F p - c) ^ k) b =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        (response μX A F b - c) ^ (k - j) * noiseMoment μX A F j b := by
  let ν := CompactGibbsContinuity.law μX (fun x => A (b, x))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability μX _
    (hA.comp (continuous_const.prodMk continuous_id))
  have hc : Continuous (fun x => removed μX A F (b, x)) :=
    (removed_continuous μX A F hA hF).comp (continuous_const.prodMk continuous_id)
  have h := integral_shift_power ν _ hc (response μX A F b - c) k
  have he (x : X) : removed μX A F (b, x) + (response μX A F b - c) = F (b, x) - c := by
    unfold removed
    ring
  simp_rw [he] at h
  simp only [response_eq_expectation μX _ _ hA b, noiseMoment]
  simpa only [response_eq_expectation μX _ _ hA b] using h

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem conditional_centered_cube (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (c : ℝ) (b : B) :
    response μX A (fun p => (F p - c) ^ 3) b =
      (response μX A F b - c) ^ 3 +
        3 * (response μX A F b - c) * noiseMoment μX A F 2 b + noiseMoment μX A F 3 b := by
  rw [conditional_shift_power μX A F hA hF c 3 b]
  norm_num [Finset.sum_range_succ, Nat.choose_succ_succ, noiseMoment_zero μX A F hA b,
    noiseMoment_one μX A F hA hF b]

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology X] in
theorem conditional_centered_fourth (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (c : ℝ) (b : B) :
    response μX A (fun p => (F p - c) ^ 4) b =
      (response μX A F b - c) ^ 4 +
        6 * (response μX A F b - c) ^ 2 * noiseMoment μX A F 2 b +
        4 * (response μX A F b - c) * noiseMoment μX A F 3 b + noiseMoment μX A F 4 b := by
  rw [conditional_shift_power μX A F hA hF c 4 b]
  norm_num [Finset.sum_range_succ, Nat.choose_succ_succ, noiseMoment_zero μX A F hA b,
    noiseMoment_one μX A F hA hF b]

/-- Exact global cubic expansion, with the retained/noise mixed term kept. -/
theorem total_centered_cube (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (c : ℝ) :
    (∫ p, (F p - c) ^ 3 ∂CompactGibbsContinuity.law (μB.prod μX) A) =
      (∫ b, (response μX A F b - c) ^ 3 ∂marginal μB μX A) +
      3 * (∫ b, (response μX A F b - c) * noiseMoment μX A F 2 b ∂marginal μB μX A) +
      ∫ b, noiseMoment μX A F 3 b ∂marginal μB μX A := by
  letI := marginal_probability μB μX A hA
  have hr : Continuous (fun b => response μX A F b - c) :=
    (response_continuous μX A F hA hF).sub continuous_const
  have hv := noiseMoment_continuous μX A F hA hF 2
  have ht := noiseMoment_continuous μX A F hA hF 3
  have hi (H : B → ℝ) (hH : Continuous H) : Integrable H (marginal μB μX A) :=
    hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← response_expectation μB μX A _ hA ((hF.sub continuous_const).pow 3)]
  simp_rw [conditional_centered_cube μX A F hA hF c]
  have hi3 : Integrable (fun b => (response μX A F b - c) ^ 3) (marginal μB μX A) :=
    hi _ (hr.pow 3)
  have hiV : Integrable (fun b => 3 * (response μX A F b - c) * noiseMoment μX A F 2 b)
      (marginal μB μX A) := hi _ ((continuous_const.mul hr).mul hv)
  have hi3V : Integrable (fun b => (response μX A F b - c) ^ 3 +
      3 * (response μX A F b - c) * noiseMoment μX A F 2 b) (marginal μB μX A) := hi3.add hiV
  rw [integral_add hi3V (hi _ ht), integral_add hi3 hiV]
  congr 1
  congr 1
  rw [show (fun b => 3 * (response μX A F b - c) * noiseMoment μX A F 2 b) =
    (fun b => 3 * ((response μX A F b - c) * noiseMoment μX A F 2 b)) by funext b; ring,
    integral_const_mul]

/-- The fourth expansion includes both retained - variance and retained - skewness mixing. -/
theorem total_centered_fourth (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (c : ℝ) :
    (∫ p, (F p - c) ^ 4 ∂CompactGibbsContinuity.law (μB.prod μX) A) =
      (∫ b, (response μX A F b - c) ^ 4 ∂marginal μB μX A) +
      6 * (∫ b, (response μX A F b - c) ^ 2 * noiseMoment μX A F 2 b ∂marginal μB μX A) +
      4 * (∫ b, (response μX A F b - c) * noiseMoment μX A F 3 b ∂marginal μB μX A) +
      ∫ b, noiseMoment μX A F 4 b ∂marginal μB μX A := by
  letI := marginal_probability μB μX A hA
  have hr : Continuous (fun b => response μX A F b - c) :=
    (response_continuous μX A F hA hF).sub continuous_const
  have hv := noiseMoment_continuous μX A F hA hF 2
  have ht := noiseMoment_continuous μX A F hA hF 3
  have hu := noiseMoment_continuous μX A F hA hF 4
  have hi (H : B → ℝ) (hH : Continuous H) : Integrable H (marginal μB μX A) :=
    hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← response_expectation μB μX A _ hA ((hF.sub continuous_const).pow 4)]
  simp_rw [conditional_centered_fourth μX A F hA hF c]
  have hi4 : Integrable (fun b => (response μX A F b - c) ^ 4) (marginal μB μX A) :=
    hi _ (hr.pow 4)
  have hiV : Integrable (fun b => 6 * (response μX A F b - c) ^ 2 * noiseMoment μX A F 2 b)
      (marginal μB μX A) := hi _ ((continuous_const.mul (hr.pow 2)).mul hv)
  have hiT : Integrable (fun b => 4 * (response μX A F b - c) * noiseMoment μX A F 3 b)
      (marginal μB μX A) := hi _ ((continuous_const.mul hr).mul ht)
  have hi4V : Integrable (fun b => (response μX A F b - c) ^ 4 +
      6 * (response μX A F b - c) ^ 2 * noiseMoment μX A F 2 b) (marginal μB μX A) := hi4.add hiV
  have hi4VT : Integrable (fun b => (response μX A F b - c) ^ 4 +
      6 * (response μX A F b - c) ^ 2 * noiseMoment μX A F 2 b +
      4 * (response μX A F b - c) * noiseMoment μX A F 3 b) (marginal μB μX A) := hi4V.add hiT
  rw [integral_add hi4VT (hi _ hu), integral_add hi4V hiT, integral_add hi4 hiV]
  simp_rw [mul_assoc, integral_const_mul]

/-- The conditional fourth cumulant, rather than the unconnected fourth moment. -/
def noiseCumulantFour (A F : B × X → ℝ) (b : B) : ℝ :=
  noiseMoment μX A F 4 b - 3 * (noiseMoment μX A F 2 b) ^ 2

/-- The retained and full first moments are literally equal under the true marginal. -/
theorem cumulant_three_decomposition (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) :
    cumulantThree (CompactGibbsContinuity.law (μB.prod μX) A) F =
      cumulantThree (marginal μB μX A) (response μX A F) +
      (∫ b, noiseMoment μX A F 3 b ∂marginal μB μX A) +
      3 * covariance (marginal μB μX A) (response μX A F) (noiseMoment μX A F 2) := by
  letI := marginal_probability μB μX A hA
  have hm := response_expectation μB μX A F hA hF
  unfold cumulantThree centeredMoment
  rw [← hm, total_centered_cube μB μX A F hA hF]
  rw [integral_centered_mul (marginal μB μX A) _ _
    (response_continuous μX A F hA hF) (noiseMoment_continuous μX A F hA hF 2)]
  ring

omit [CompactSpace B] [SecondCountableTopology B] [MeasurableSpace B]
  [BorelSpace B] [SecondCountableTopology X] in
theorem noiseMoment_two_eq_covariance (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) (b : B) :
    noiseMoment μX A F 2 b = conditionalCovariance μX A F F b := by
  simpa only [noiseMoment, pow_two] using
    conditional_removed_product μX A F F hA hF hF b

/-- The variance decomposition used in the fourth cumulance identity. -/
theorem centeredMoment_two_decomposition (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) :
    centeredMoment (CompactGibbsContinuity.law (μB.prod μX) A) F 2 =
      (∫ b, noiseMoment μX A F 2 b ∂marginal μB μX A) +
      centeredMoment (marginal μB μX A) (response μX A F) 2 := by
  letI := CompactGibbsContinuity.law_probability (μB.prod μX) A hA
  letI := marginal_probability μB μX A hA
  rw [centeredMoment_two_eq_covariance _ F hF,
    centeredMoment_two_eq_covariance _ _ (response_continuous μX A F hA hF),
    total_covariance μB μX A F F hA hF hF]
  simp_rw [noiseMoment_two_eq_covariance μX A F hA hF]

/-- Exact law of total fourth cumulance. The covariance terms are not sign definite. -/
theorem cumulant_four_decomposition (A F : B × X → ℝ) (hA : Continuous A)
    (hF : Continuous F) :
    cumulantFour (CompactGibbsContinuity.law (μB.prod μX) A) F =
      cumulantFour (marginal μB μX A) (response μX A F) +
      (∫ b, noiseCumulantFour μX A F b ∂marginal μB μX A) +
      4 * covariance (marginal μB μX A) (response μX A F) (noiseMoment μX A F 3) +
      3 * covariance (marginal μB μX A) (noiseMoment μX A F 2) (noiseMoment μX A F 2) +
      6 * covariance (marginal μB μX A)
        (fun b => (response μX A F b-∫ r, response μX A F r ∂marginal μB μX A) ^ 2)
        (noiseMoment μX A F 2) := by
  let ν := marginal μB μX A
  letI : IsProbabilityMeasure ν := marginal_probability μB μX A hA
  let m := response μX A F
  let v := noiseMoment μX A F 2
  let t := noiseMoment μX A F 3
  let u := noiseMoment μX A F 4
  have hm := response_expectation μB μX A F hA hF
  have hmc : Continuous m := response_continuous μX A F hA hF
  have hvc : Continuous v := noiseMoment_continuous μX A F hA hF 2
  have htc : Continuous t := noiseMoment_continuous μX A F hA hF 3
  have huc : Continuous u := noiseMoment_continuous μX A F hA hF 4
  have hi (H : B → ℝ) (hH : Continuous H) : Integrable H ν :=
    hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hk : (∫ b, noiseCumulantFour μX A F b ∂ν) =
      (∫ b, u b ∂ν) - 3 * (∫ b, (v b) ^ 2 ∂ν) := by
    unfold noiseCumulantFour
    rw [integral_sub (hi _ huc) ((hi _ (hvc.pow 2)).const_mul 3), integral_const_mul]
  have hmt := integral_centered_mul ν m t hmc htc
  unfold cumulantFour
  rw [centeredMoment_two_decomposition μB μX A F hA hF]
  unfold centeredMoment
  rw [← hm, total_centered_fourth μB μX A F hA hF]
  change (∫ b, (m b-∫ r, m r ∂ν) ^ 4 ∂ν) +
      6 * (∫ b, (m b-∫ r, m r ∂ν) ^ 2 * v b ∂ν) +
      4 * (∫ b, (m b-∫ r, m r ∂ν) * t b ∂ν) + (∫ b, u b ∂ν) -
      3 * ((∫ b, v b ∂ν) + ∫ b, (m b-∫ r, m r ∂ν) ^ 2 ∂ν) ^ 2 =
    (∫ b, (m b-∫ r, m r ∂ν) ^ 4 ∂ν) - 3 * (∫ b, (m b-∫ r, m r ∂ν) ^ 2 ∂ν) ^ 2 +
      (∫ b, noiseCumulantFour μX A F b ∂ν) + 4 * covariance ν m t +
      3 * covariance ν v v +
      6 * covariance ν (fun b => (m b-∫ r, m r ∂ν) ^ 2) v
  rw [hk, hmt]
  unfold covariance
  simp only [← pow_two]
  ring

end
end UnifiedTheory.Clay.YangMills.GibbsConditionalCumulants
