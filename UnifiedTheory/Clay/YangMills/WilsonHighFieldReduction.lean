/- Slow actual transfer modes have quantitatively small high-density mass.
Reversibility moves the proved high-field input estimate to the output;
the two-step residual is controlled by the actual variance loss. -/
import UnifiedTheory.Clay.YangMills.WilsonHighFieldSector

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonHighFieldReduction
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonTemporalInfluence WilsonPhysicalResponse WilsonAveragedResponse
open WilsonPhysicalVariance WilsonGroundHeatBath WilsonHighFieldNormalization
open WilsonHighFieldDecay CompactDensityEntropy
open WilsonSingleLinkStaples (character)

variable (n : ℕ) [NeZero n]

def pairing (β : ℝ) (hβ : 0 ≤ β) (f h : C(Slice n, ℝ)) : ℝ :=
  ∫ u, f u*h u ∂groundLaw n β hβ

theorem pairing_symm (β : ℝ) (hβ : 0 ≤ β) (f h : C(Slice n, ℝ)) :
    pairing n β hβ f h = pairing n β hβ h f := by simp only [pairing, mul_comm]

theorem pairing_self (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    pairing n β hβ f f = mass n β hβ f := by simp only [pairing, mass, pow_two]

theorem pairing_raw (β : ℝ) (hβ : 0 ≤ β) (f h : C(Slice n, ℝ)) :
    pairing n β hβ f (step n β hβ h) =
      ∫ u, ∫ v, (ground n β hβ u)^2 * rawTransition n β hβ u v*f u*h v
        ∂WilsonSlabOperator.measure n ∂WilsonSlabOperator.measure n := by
  rw [pairing, groundLaw, GroundStateDirichlet.stationary_integral _ _ (ground n β hβ).continuous]
  change (∫ u, (ground n β hβ u)^2*(f u*rowMean n β hβ h u)
    ∂WilsonSlabOperator.measure n) = _
  simp_rw [rowMean_eq_raw, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  apply integral_congr_ae
  filter_upwards with v
  ring

/-- Actual detailed balance, without a spectral or mixing hypothesis. -/
theorem pairing_step (β : ℝ) (hβ : 0 ≤ β) (f h : C(Slice n, ℝ)) :
    pairing n β hβ f (step n β hβ h) = pairing n β hβ (step n β hβ f) h := by
  rw [pairing_symm n β hβ (step n β hβ f) h, pairing_raw, pairing_raw]
  have hc : Continuous (fun z : Slice n × Slice n =>
      (ground n β hβ z.1)^2 * rawTransition n β hβ z.1 z.2*f z.1*h z.2) :=
    (((((ground n β hβ).continuous.comp continuous_fst).pow 2).mul
      (rawTransition_continuous n β hβ)).mul (f.continuous.comp continuous_fst)).mul
      (h.continuous.comp continuous_snd)
  rw [integral_integral_swap (f := fun u v =>
    (ground n β hβ u)^2 * rawTransition n β hβ u v*f u*h v)
    (continuous_integrable ((WilsonSlabOperator.measure n).prod
      (WilsonSlabOperator.measure n)) _ hc)]
  apply integral_congr_ae
  filter_upwards with v
  apply integral_congr_ae
  filter_upwards with u
  rw [raw_detailed_balance]
  ring

theorem pairing_sq (β : ℝ) (hβ : 0 ≤ β) (f h : C(Slice n, ℝ)) :
    (pairing n β hβ f h)^2 ≤ mass n β hβ f*mass n β hβ h := by
  letI := groundLaw_probability n β hβ
  exact integral_product_sq (groundLaw n β hβ) f h f.continuous h.continuous

theorem mass_step_le (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    mass n β hβ (step n β hβ f) ≤ mass n β hβ f := by
  have h := loss_nonneg n β hβ f
  rwa [loss_mass, sub_nonneg] at h

theorem mass_sub (β : ℝ) (hβ : 0 ≤ β) (f h : C(Slice n, ℝ)) :
    mass n β hβ (f-h) = mass n β hβ f-2*pairing n β hβ f h+mass n β hβ h := by
  letI := groundLaw_probability n β hβ
  have hf := continuous_integrable (groundLaw n β hβ) _ (f.continuous.pow 2)
  have hh := continuous_integrable (groundLaw n β hβ) _ (h.continuous.pow 2)
  have hfh : Integrable (fun u => f u*h u) (groundLaw n β hβ) :=
    continuous_integrable (groundLaw n β hβ) _ (f.continuous.mul h.continuous)
  unfold mass pairing
  simp only [ContinuousMap.sub_apply, sub_sq, mul_assoc]
  have ha := integral_add (hf.sub (hfh.const_mul 2)) hh
  have hs := integral_sub hf (hfh.const_mul 2)
  simp only [Pi.sub_apply] at ha
  rw [ha, hs, integral_const_mul]

/-- P squared is used so that no unproved positive-spectrum premise is needed. -/
theorem residual_le_loss (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    mass n β hβ (f-step n β hβ (step n β hβ f)) ≤ loss n β hβ f := by
  rw [mass_sub, pairing_step, pairing_self, loss_mass]
  have h := mass_step_le n β hβ (step n β hβ f)
  linarith

theorem cutoff_mass_le (β : ℝ) (hβ : 0 ≤ β) (χ f : C(Slice n, ℝ))
    (hχ : ∀ u, χ u ∈ Set.Icc 0 1) : mass n β hβ (χ*f) ≤ mass n β hβ f := by
  letI := groundLaw_probability n β hβ
  apply integral_mono
    (continuous_integrable (groundLaw n β hβ) _ ((χ*f).continuous.pow 2))
    (continuous_integrable (groundLaw n β hβ) _ (f.continuous.pow 2))
  intro u
  change (χ u*f u)^2 ≤ (f u)^2
  have h := pow_le_pow_left₀ (hχ u).1 (hχ u).2 2
  simpa only [mul_pow, one_pow, one_mul] using mul_le_mul_of_nonneg_right h (sq_nonneg (f u))

/-- Adjointness turns the input high-density bound into an output estimate
valid for every continuous observable. -/
theorem cutoff_output (β : ℝ) (hβ : 0 < β) (r : ℝ) (hr : 0 ≤ r)
    (he : 4 * WilsonGroundSlabEnergy.envelope β ≤ r / 2) (χ f : C(Slice n, ℝ))
    (hχ : ∀ u, χ u ∈ Set.Icc 0 1)
    (hs : ∀ u, potential character 2 u < r * links n → χ u = 0) :
    mass n β hβ.le (χ*step n β hβ.le f) ≤ Real.exp (-β*r / 2)*mass n β hβ.le f := by
  let k := χ*step n β hβ.le f
  let h := χ*k
  have hid : pairing n β hβ.le h (step n β hβ.le f) = mass n β hβ.le k := by
    unfold pairing mass
    apply integral_congr_ae
    filter_upwards with u
    simp only [h, k, ContinuousMap.mul_apply]
    ring
  have hc := pairing_sq n β hβ.le (step n β hβ.le h) f
  rw [← pairing_step, hid] at hc
  have hd := uniform_highfield_decay n β hβ r hr he h (by
    intro u hu
    change χ u*k u = 0
    rw [hs u hu, zero_mul])
  have hh := cutoff_mass_le n β hβ.le χ k hχ
  have hm := mass_nonneg n β hβ.le f
  have he0 := (Real.exp_pos (-β*r / 2)).le
  have hb := hc.trans (mul_le_mul_of_nonneg_right
    (hd.trans (mul_le_mul_of_nonneg_left hh he0)) hm)
  have hk := mass_nonneg n β hβ.le k
  by_cases hz : mass n β hβ.le k = 0
  · change mass n β hβ.le k ≤ _
    rw [hz]
    exact mul_nonneg he0 hm
  · have hp : 0 < mass n β hβ.le k := lt_of_le_of_ne hk (Ne.symm hz)
    change mass n β hβ.le k ≤ _
    nlinarith

/-- Slow modes of the actual transfer concentrate below the high-density
cutoff. The small remainder is paid by mass, not falsely by loss alone. -/
theorem slow_mode_highfield (β : ℝ) (hβ : 0 < β) (r : ℝ) (hr : 0 ≤ r)
    (he : 4 * WilsonGroundSlabEnergy.envelope β ≤ r / 2) (χ f : C(Slice n, ℝ))
    (hχ : ∀ u, χ u ∈ Set.Icc 0 1)
    (hs : ∀ u, potential character 2 u < r * links n → χ u = 0) :
    mass n β hβ.le (χ*f) ≤
      2*loss n β hβ.le f+2*Real.exp (-β*r / 2)*mass n β hβ.le f := by
  letI := groundLaw_probability n β hβ.le
  let P2 := step n β hβ.le (step n β hβ.le f)
  have hi := integral_mono
    (continuous_integrable (groundLaw n β hβ.le) _ ((χ*f).continuous.pow 2))
    (((continuous_integrable (groundLaw n β hβ.le) _ ((χ*(f-P2)).continuous.pow 2)).const_mul 2).add
      ((continuous_integrable (groundLaw n β hβ.le) _ ((χ*P2).continuous.pow 2)).const_mul 2))
    (fun u => show (χ u*f u)^2 ≤ 2*(χ u*(f u-P2 u))^2+2*(χ u*P2 u)^2 by
      nlinarith [sq_nonneg (χ u*(f u-2*P2 u))])
  simp only [Pi.add_apply] at hi
  rw [integral_add, integral_const_mul, integral_const_mul] at hi
  · change mass n β hβ.le (χ*f) ≤ 2*mass n β hβ.le (χ*(f-P2))+2*mass n β hβ.le (χ*P2) at hi
    have ha := (cutoff_mass_le n β hβ.le χ (f-P2) hχ).trans (residual_le_loss n β hβ.le f)
    have hb := (cutoff_output n β hβ r hr he χ (step n β hβ.le f) hχ hs).trans
      (mul_le_mul_of_nonneg_left (mass_step_le n β hβ.le f) (Real.exp_pos _).le)
    change mass n β hβ.le (χ*P2) ≤ _ at hb
    linarith
  · exact (continuous_integrable (groundLaw n β hβ.le) _ ((χ*(f-P2)).continuous.pow 2)).const_mul 2
  · exact (continuous_integrable (groundLaw n β hβ.le) _ ((χ*P2).continuous.pow 2)).const_mul 2

/-- The physical cutoff is zero at density <=r and one at density >=2r. -/
def energyCutoff (r : ℝ) : C(Slice n, ℝ) :=
  ⟨fun u => min 1 (max 0 ((WilsonHighFieldSector.potentialMap n u-r * links n)/(r * links n))),
    continuous_const.min (continuous_const.max
      (((WilsonHighFieldSector.potentialMap n).continuous.sub continuous_const).div_const _))⟩

theorem energyCutoff_range (r : ℝ) (u : Slice n) : energyCutoff n r u ∈ Set.Icc 0 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

theorem energyCutoff_supported (r : ℝ) (hr : 0 < r) (u : Slice n)
    (hu : potential character 2 u < r * links n) : energyCutoff n r u = 0 := by
  change min 1 (max 0 ((potential character 2 u-r * links n)/(r * links n))) = 0
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu.le)
    (mul_pos hr (links_pos n)).le)]
  norm_num

theorem energyCutoff_one (r : ℝ) (hr : 0 < r) (u : Slice n)
    (hu : 2 * r * links n ≤ potential character 2 u) : energyCutoff n r u = 1 := by
  apply min_eq_left
  apply (le_max_right _ _).trans'
  apply (le_div_iff₀ (mul_pos hr (links_pos n))).mpr
  change 1*(r * links n) ≤ potential character 2 u-r * links n
  linarith

theorem energyCutoff_physical (r : ℝ) (h : SliceGauge n Q) (u : Slice n) :
    energyCutoff n r (gaugeSlice h u) = energyCutoff n r u := by
  change min 1 (max 0 ((potential character 2 (gaugeSlice h u)-r * links n)/(r * links n))) = _
  rw [WilsonSlabGauge.potential_gauge character WilsonSingleLinkStaples.character_classFunction]
  rfl

/-- Fully instantiated high-density concentration for arbitrary observables. -/
theorem energy_localization (β : ℝ) (hβ : 0 < β) (r : ℝ) (hr : 0 < r)
    (he : 4 * WilsonGroundSlabEnergy.envelope β ≤ r / 2) (f : C(Slice n, ℝ)) :
    mass n β hβ.le (energyCutoff n r*f) ≤
      2*loss n β hβ.le f+2*Real.exp (-β*r / 2)*mass n β hβ.le f :=
  slow_mode_highfield n β hβ r hr.le he (energyCutoff n r) f
    (energyCutoff_range n r) (energyCutoff_supported n r hr)

/-- The density threshold itself can go to zero, uniformly in the period. -/
def shrinkingThreshold (β : ℝ) : ℝ := 8 * WilsonGroundSlabEnergy.envelope β

omit n [NeZero n] in
theorem shrinkingThreshold_pos (β : ℝ) (hβ : 0 < β) : 0 < shrinkingThreshold β := by
  have hl : 0 ≤ Real.log (2*β+5) := Real.log_nonneg (by linarith)
  unfold shrinkingThreshold WilsonGroundSlabEnergy.envelope
  positivity

omit n [NeZero n] in
theorem shrinkingThreshold_tendsto :
    Filter.Tendsto shrinkingThreshold Filter.atTop (nhds 0) := by
  simpa only [mul_zero] using WilsonGroundSlabEnergy.envelope_tendsto.const_mul 8

omit n [NeZero n] in
theorem shrinking_rate (β : ℝ) (hβ : 1 ≤ β) :
    Real.exp (-β * shrinkingThreshold β / 2) ≤ 1/β := by
  have hb : 0 < β := lt_of_lt_of_le (by norm_num) hβ
  have hl : Real.log β ≤ Real.log (2*β+5) := Real.log_le_log hb (by linarith)
  have hl0 := Real.log_nonneg hβ
  have he : β * WilsonGroundSlabEnergy.envelope β =
      1568/β+(28/3)*Real.log (2*β+5) := by
    unfold WilsonGroundSlabEnergy.envelope
    field_simp
  have hn : 0 ≤ 1568/β := by positivity
  have hx : -β * shrinkingThreshold β / 2 ≤ -Real.log β := by
    unfold shrinkingThreshold
    nlinarith
  calc
    _ ≤ Real.exp (-Real.log β) := Real.exp_le_exp.mpr hx
    _ = 1/β := by rw [Real.exp_neg, Real.exp_log hb, one_div]

/-- Every continuous source has small mass above a density that tends to zero,
up to its actual loss. This is not a spatial defect or mixing bound. -/
theorem shrinking_localization (β : ℝ) (hβ : 1 ≤ β) (f : C(Slice n, ℝ)) :
    mass n β (by linarith : 0 ≤ β) (energyCutoff n (shrinkingThreshold β)*f) ≤
      2*loss n β (by linarith : 0 ≤ β) f+2/β*mass n β (by linarith : 0 ≤ β) f := by
  have hb : 0 < β := lt_of_lt_of_le (by norm_num) hβ
  have h := energy_localization n β hb (shrinkingThreshold β) (shrinkingThreshold_pos β hb)
    (by unfold shrinkingThreshold; linarith) f
  have hr := mul_le_mul_of_nonneg_right (shrinking_rate β hβ) (mass_nonneg n β hb.le f)
  rw [show (2:ℝ)/β = 2*(1/β) by ring]
  nlinarith

/-- A hard high-energy event is controlled by the proved continuous cutoff. -/
theorem weighted_tail_le_cutoff (β : ℝ) (hβ : 0 ≤ β) (r : ℝ) (hr : 0 < r)
    (f : C(Slice n, ℝ)) :
    (∫ u, {v | 2 * r * links n ≤ potential character 2 v}.indicator (fun v => (f v)^2) u
      ∂groundLaw n β hβ) ≤ mass n β hβ (energyCutoff n r*f) := by
  letI := groundLaw_probability n β hβ
  have hE : MeasurableSet {v : Slice n | 2 * r * links n ≤ potential character 2 v} :=
    measurableSet_le measurable_const (WilsonHighFieldSector.potentialMap n).continuous.measurable
  apply integral_mono
    ((continuous_integrable (groundLaw n β hβ) _ (f.continuous.pow 2)).indicator hE)
    (continuous_integrable (groundLaw n β hβ) _ ((energyCutoff n r*f).continuous.pow 2))
  intro u
  by_cases hu : 2 * r * links n ≤ potential character 2 u
  · rw [Set.indicator_of_mem (show u ∈ {v | 2 * r * links n ≤ potential character 2 v} from hu)]
    simp only [ContinuousMap.mul_apply, energyCutoff_one n r hr u hu, one_mul, le_refl]
  · rw [Set.indicator_of_notMem (show u ∉ {v | 2 * r * links n ≤ potential character 2 v} from hu)]
    exact sq_nonneg _

/-- The actual f-squared weighted tail, with a shrinking density threshold.
This is an L2-mass estimate, not a loss-only variance-pair tail. -/
theorem shrinking_weighted_tail (β : ℝ) (hβ : 1 ≤ β) (f : C(Slice n, ℝ)) :
    (∫ u, {v | 2 * shrinkingThreshold β * links n ≤ potential character 2 v}.indicator
      (fun v => (f v)^2) u ∂groundLaw n β (by linarith : 0 ≤ β)) ≤
      2*loss n β (by linarith : 0 ≤ β) f+2/β*mass n β (by linarith : 0 ≤ β) f :=
  (weighted_tail_le_cutoff n β (by linarith) (shrinkingThreshold β)
    (shrinkingThreshold_pos β (by linarith)) f).trans (shrinking_localization n β hβ f)

end
end UnifiedTheory.Clay.YangMills.WilsonHighFieldReduction
