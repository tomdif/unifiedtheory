/- General two-shift contour transport for the shifted radial Yosida
multiplier and shifted radial resolvent regularizer across the longitudinal
clock exponential, the ordered clock exponential, and both ordered matter
factors. Because the contour shift from 0 to -h/2 only traverses imaginary
parts between y₀ and y₁ = y₀ - h/2, transport holds whenever both endpoints
lie in the analyticity strip [-π ε / 6, π ε / 6], including the forward-shift
pair (h, h/2) for |h| ≤ π ε / 6 as well as the unshifted pair (0, -h/2). -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventShiftedPairing

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventShiftedOrderedTransport
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology FourierTransform
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanConfiguration (Space FrequencyHilbert)
open KFCausalEuclideanClockSplit (TailSpace euclideanSplit euclideanSplit_apply
  euclideanSplit_preserves_volume tail)
open KFCausalEuclideanGaussianCore (gaussian gaussian_continuous gaussian_integrable
  gaussian_memLp exponentialWeight)
open KFCausalClockFloorFullGaussian (clockFactor)
open KFCausalGaussianContourShift (horizontal vertical gaussian_tendsto_zero)
open KFCausalFourierStripDecay (kernel twist kernel_line_norm twist_integral)
open KFCausalClockFourierFubini (clockFourier fourier_iterated)
open KFCausalStripFamilyExponentialGraph (symbol symbol_bound physicalMultiplier
  physicalMultiplier_coe unitState unitState_zero unitState_shift graph_core_lift)
open KFCausalL2FourierIntegral (fourier_toLp_coe)
open KFCausalEuclideanProductCoordinates (split split_preserves_volume)
open KFCausalPairedModeCoordinates (modeIsometry mode_preserves_volume)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockFloorDefectCoordinates (straightening)
open KFCausalMixedStripExponentialGraph (unitary unitary_action unitary_straightening_coe)
open KFCausalClockFloorTransverseFourierGraph (exponential_graph)
open KFCausalClockFloorBoundedInverse (inverseL ordered_graph_iff)
open KFCausalClockMixedClockGraph (halfWeight inverseL_clockMixed_coe)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalClockFloorTrialMatter (matterFactor)
open KFCausalClockFloorFourierCoordinates (coupledFourier)
open KFCausalClockFloorExponential (longitudinalExponential longitudinal_exponential_graph)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPhysicalField (physicalField)
open KFCausalTransverseFieldSquare (fieldSquare)
open KFCausalOrderedOperatorComposition (composition_graph)
open KFCausalClockFloorRadialYosidaOrderedTransport (family family_analytic
  family_line_continuous family_bound shift_bound)
open KFCausalClockFloorRadialResolventShiftedPairing (zero_shift_bound
  neg_shift_bound half_shift_bound)

abbrev shiftedMultiplier := KFCausalClockFloorRadialYosidaOrderedTransport.shifted
abbrev shiftedResolvent := KFCausalClockFloorRadialResolventShifted.shifted

private theorem horizontal_continuous_uIcc (f : ℂ → ℂ) (y r : ℝ)
    (hf : ∀ z : ℂ, z.im ∈ uIcc 0 y → DifferentiableAt ℂ f z) (hr : r ∈ uIcc 0 y) :
    Continuous (horizontal f r) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hz : ((x:ℂ)+(r:ℂ)*I).im ∈ uIcc 0 y := by simpa using hr
  change ContinuousAt (fun x : ℝ => f ((x:ℂ)+(r:ℂ)*I)) x
  exact (hf _ hz).continuousAt.comp (f := fun x : ℝ => (x:ℂ)+(r:ℂ)*I)
    (show ContinuousAt (fun x : ℝ => (x:ℂ)+(r:ℂ)*I) x by fun_prop)

private theorem vertical_norm_bound_uIcc (f : ℂ → ℂ) (a B y T : ℝ)
    (hb : ∀ x r, r ∈ uIcc 0 y → ‖horizontal f r x‖ ≤ B*Real.exp (-a*x^2)) :
    ‖vertical f y T‖ ≤ |y| *(B*Real.exp (-a*T^2)) := by
  unfold vertical
  have hh : ∀ r ∈ uIoc 0 y, ‖f ((T:ℂ)+(r:ℂ)*I)‖ ≤ B*Real.exp (-a*T^2) := by
    intro r hr
    exact hb T r (uIoc_subset_uIcc hr)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hh
  simpa only [sub_zero,mul_comm] using hi

private theorem vertical_tendsto_zero_uIcc (f : ℂ → ℂ) (a B y : ℝ) (ha : 0 < a)
    (hb : ∀ x r, r ∈ uIcc 0 y → ‖horizontal f r x‖ ≤ B*Real.exp (-a*x^2)) :
    Tendsto (vertical f y) atTop (𝓝 0) ∧
      Tendsto (fun T => vertical f y (-T)) atTop (𝓝 0) := by
  have hl : Tendsto (fun T : ℝ => |y| *(B*Real.exp (-a*T^2))) atTop (𝓝 0) := by
    simpa using ((gaussian_tendsto_zero a ha).const_mul B).const_mul |y|
  constructor <;> rw [tendsto_zero_iff_norm_tendsto_zero]
  · exact squeeze_zero (fun _ => norm_nonneg _) (fun T => vertical_norm_bound_uIcc f a B y T hb) hl
  · apply squeeze_zero (fun _ => norm_nonneg _) (fun T => ?_) hl
    simpa only [neg_sq] using vertical_norm_bound_uIcc f a B y (-T) hb

private theorem twist_gaussian_bound_uIcc (f : ℂ → ℂ) (a B y k : ℝ)
    (hb : ∀ x r, r ∈ uIcc 0 y → ‖horizontal f r x‖ ≤ B*Real.exp (-a*x^2)) :
    ∀ x r, r ∈ uIcc 0 y → ‖horizontal (twist f k) r x‖ ≤
      (Real.exp (2*Real.pi*|k| *|y|)*B)*Real.exp (-a*x^2) := by
  intro x r hr
  have hr' : |r| ≤ |y| := by simpa using abs_sub_left_of_mem_uIcc hr
  have hkr : k*r ≤ |k| *|y| := by
    calc
      _ ≤ |k*r| := le_abs_self _
      _ = |k| *|r| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hr' (abs_nonneg _)
  have hk : Real.exp (2*Real.pi*k*r) ≤ Real.exp (2*Real.pi*|k| *|y|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  change ‖kernel k ((x:ℂ)+(r:ℂ)*I)*horizontal f r x‖ ≤ _
  rw [norm_mul,kernel_line_norm]
  have hh := mul_le_mul hk (hb x r hr) (norm_nonneg _) (Real.exp_pos _).le
  convert hh using 1
  ring

private theorem horizontal_integral_eq_uIcc (f : ℂ → ℂ) (a B y : ℝ)
    (hf : ∀ z : ℂ, z.im ∈ uIcc 0 y → DifferentiableAt ℂ f z) (ha : 0 < a)
    (hb : ∀ x r, r ∈ uIcc 0 y → ‖horizontal f r x‖ ≤ B*Real.exp (-a*x^2)) :
    (∫ x, horizontal f 0 x) = ∫ x, horizontal f y x := by
  have hi (r : ℝ) (hr : r ∈ uIcc 0 y) : Integrable (horizontal f r) := by
    apply ((integrable_exp_neg_mul_sq ha).const_mul B).mono'
      (horizontal_continuous_uIcc f y r hf hr).aestronglyMeasurable
    exact Eventually.of_forall (fun x => hb x r hr)
  have hi0 := hi 0 left_mem_uIcc
  have hiy := hi y right_mem_uIcc
  have hv := vertical_tendsto_zero_uIcc f a B y ha hb
  have hr (T : ℝ) :
      (∫ x : ℝ in -T..T, horizontal f 0 x) - (∫ x : ℝ in -T..T, horizontal f y x) +
        I*vertical f y T-I*vertical f y (-T) = 0 := by
    have hh := integral_boundary_rect_eq_zero_of_differentiableOn f (-T) ((T:ℂ)+(y:ℂ)*I)
      (by
        intro z hz
        have hm : z.im ∈ uIcc 0 y := by simpa using hz.2
        exact (hf z hm).differentiableWithinAt)
    simpa only [horizontal,vertical,neg_im,ofReal_im,neg_zero,ofReal_zero,zero_mul,add_zero,
      neg_re,ofReal_re,add_re,mul_re,I_re,mul_zero,I_im,sub_zero,add_im,mul_im,mul_one,
      zero_add,smul_eq_mul,ofReal_neg] using hh
  have ht0 : Tendsto (fun T : ℝ => ∫ x : ℝ in -T..T, horizontal f 0 x) atTop
      (𝓝 (∫ x, horizontal f 0 x)) :=
    intervalIntegral_tendsto_integral hi0 tendsto_neg_atTop_atBot tendsto_id
  have hty : Tendsto (fun T : ℝ => ∫ x : ℝ in -T..T, horizontal f y x) atTop
      (𝓝 (∫ x, horizontal f y x)) :=
    intervalIntegral_tendsto_integral hiy tendsto_neg_atTop_atBot tendsto_id
  have ht := ((ht0.sub hty).add (hv.1.const_mul I)).sub (hv.2.const_mul I)
  have hz : Tendsto (fun T : ℝ =>
      (∫ x : ℝ in -T..T, horizontal f 0 x) - (∫ x : ℝ in -T..T, horizontal f y x) +
        I*vertical f y T-I*vertical f y (-T)) atTop (𝓝 0) := by
    simpa only [hr] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0))
  have he := tendsto_nhds_unique ht hz
  simpa only [mul_zero,add_zero,sub_zero,sub_eq_zero] using he

private theorem fourier_shift_uIcc (f : ℂ → ℂ) (a B y : ℝ)
    (hf : ∀ z : ℂ, z.im ∈ uIcc 0 y → DifferentiableAt ℂ f z) (ha : 0 < a)
    (hb : ∀ x r, r ∈ uIcc 0 y → ‖horizontal f r x‖ ≤ B*Real.exp (-a*x^2)) (k : ℝ) :
    (𝓕 (horizontal f 0)) k = (Real.exp (2*Real.pi*k*y):ℂ)*(𝓕 (horizontal f y)) k := by
  have ht : ∀ z : ℂ, z.im ∈ uIcc 0 y → DifferentiableAt ℂ (twist f k) z := by
    intro z hz
    have hk : DifferentiableAt ℂ (kernel k) z := by unfold kernel; fun_prop
    exact hk.mul (hf z hz)
  have hh := horizontal_integral_eq_uIcc (twist f k)
    a (Real.exp (2*Real.pi*|k| *|y|)*B) y ht ha (twist_gaussian_bound_uIcc f a B y k hb)
  rw [twist_integral,twist_integral] at hh
  simpa only [mul_zero,Real.exp_zero,ofReal_one,one_mul] using hh

private theorem add_mem_strip_of_mem_uIcc {y₀ y₁ s d r : ℝ}
    (hy₀ : |y₀| ≤ d) (hy₁ : |y₁| ≤ d) (hs : y₁ = y₀ + s) (hr : r ∈ uIcc 0 s) :
    |r + y₀| ≤ d := by
  rw [abs_le] at hy₀ hy₁ ⊢
  rcases le_total 0 s with h0s | hs0
  · rw [uIcc_of_le h0s] at hr
    rcases hr with ⟨hr1, hr2⟩
    constructor <;> linarith
  · rw [uIcc_of_ge hs0] at hr
    rcases hr with ⟨hr1, hr2⟩
    constructor <;> linarith

private def translatedFamily (F : ℂ → TailSpace → ℂ) (y₀ : ℝ) (q : ℂ) (z : TailSpace) : ℂ :=
  F (q + (y₀:ℂ)*I) z

private theorem translated_line_eq (F : ℂ → TailSpace → ℂ) (v : Space)
    (y₀ y r : ℝ) (hyr : y = y₀ + r) (w : ℝ × TailSpace) :
    KFCausalGaussianStripFamily.line (translatedFamily F y₀) v r w =
      F ((w.1:ℂ)+(y:ℂ)*I) w.2 * KFCausalGaussianStrip.line (fun _ => 1) v r w := by
  simp only [KFCausalGaussianStripFamily.line, KFCausalGaussianStripFamily.trial,
    translatedFamily, KFCausalGaussianStrip.line, KFCausalGaussianStrip.trial, one_mul]
  have hq : (w.1:ℂ)+(r:ℂ)*I+(y₀:ℂ)*I = (w.1:ℂ)+(y:ℂ)*I := by
    rw [hyr]
    push_cast
    ring
  rw [hq, mul_assoc]

private theorem translated_spectralLine_eq (F : ℂ → TailSpace → ℂ) (v : Space)
    (y₀ y r : ℝ) (hyr : y = y₀ + r) (x : Space) :
    KFCausalGaussianStripFamily.spectralLine (translatedFamily F y₀) v r x =
      symbol F y x * KFCausalGaussianStrip.spectralLine (fun _ => 1) v r x := by
  change KFCausalGaussianStripFamily.line (translatedFamily F y₀) v r (euclideanSplit x) = _
  rw [translated_line_eq F v y₀ y r hyr (euclideanSplit x)]
  rfl

variable (F : ℂ → TailSpace → ℂ) (d M : ℝ)
  (hF : ∀ z q, |q.im| ≤ d → AnalyticAt ℂ (fun q => F q z) q)
  (hC : ∀ y, |y| ≤ d → Continuous (fun w : ℝ × TailSpace => F ((w.1:ℂ)+(y:ℂ)*I) w.2))
  (hM : 0 ≤ M) (hB : ∀ q, |q.im| ≤ d → ∀ z, ‖F q z‖ ≤ M)

include hC in
private theorem translated_line_continuous (v : Space) (y₀ y r : ℝ)
    (hy : |y| ≤ d) (hyr : y = y₀ + r) :
    Continuous (KFCausalGaussianStripFamily.line (translatedFamily F y₀) v r) := by
  have heq : KFCausalGaussianStripFamily.line (translatedFamily F y₀) v r =
      fun w => F ((w.1:ℂ)+(y:ℂ)*I) w.2 * KFCausalGaussianStrip.line (fun _ => 1) v r w := by
    ext w
    exact translated_line_eq F v y₀ y r hyr w
  rw [heq]
  exact (hC y hy).mul (KFCausalGaussianStrip.line_continuous (fun _ => 1) v |r|
    (fun _ _ => analyticAt_const) r le_rfl)

include hC in
private theorem translated_spectralLine_continuous (v : Space) (y₀ y r : ℝ)
    (hy : |y| ≤ d) (hyr : y = y₀ + r) :
    Continuous (KFCausalGaussianStripFamily.spectralLine (translatedFamily F y₀) v r) :=
  (translated_line_continuous F d hC v y₀ y r hy hyr).comp
    ((by fun_prop : Continuous (fun x : Space => x 0)).prodMk KFCausalGaussianStrip.tail_continuous)

include hB in
private theorem translated_spectralLine_bound (v : Space) (y₀ y r : ℝ)
    (hy : |y| ≤ d) (hyr : y = y₀ + r) (x : Space) :
    ‖KFCausalGaussianStripFamily.spectralLine (translatedFamily F y₀) v r x‖ ≤
      (M * Real.exp (Real.pi * r^2)) * ‖gaussian (x + v)‖ := by
  rw [translated_spectralLine_eq F v y₀ y r hyr x, norm_mul]
  have hb1 := symbol_bound F d M hB y hy x
  have hb2 := KFCausalGaussianStrip.spectralLine_bound (fun _ => 1) v |r| 1
    (fun _ _ => by simp) r le_rfl x
  calc
    ‖symbol F y x‖ * ‖KFCausalGaussianStrip.spectralLine (fun _ => 1) v r x‖ ≤
        M * ((1 * Real.exp (Real.pi * r^2)) * ‖gaussian (x + v)‖) :=
      mul_le_mul hb1 hb2 (norm_nonneg _) (le_trans (norm_nonneg _) hb1)
    _ = (M * Real.exp (Real.pi * r^2)) * ‖gaussian (x + v)‖ := by ring

include hC hB in
private theorem translated_spectralLine_integrable (v : Space) (y₀ y r : ℝ)
    (hy : |y| ≤ d) (hyr : y = y₀ + r) :
    Integrable (KFCausalGaussianStripFamily.spectralLine (translatedFamily F y₀) v r) := by
  have hi : Integrable (fun x : Space => gaussian (x + v)) :=
    (measurePreserving_add_right volume v).integrable_comp_of_integrable gaussian_integrable
  apply (hi.norm.const_mul (M * Real.exp (Real.pi * r^2))).mono'
    (translated_spectralLine_continuous F d hC v y₀ y r hy hyr).aestronglyMeasurable
  exact Eventually.of_forall (translated_spectralLine_bound F d M hB v y₀ y r hy hyr)

include hC hM hB in
private theorem translated_spectralLine_memLp (v : Space) (y₀ y r : ℝ)
    (hy : |y| ≤ d) (hyr : y = y₀ + r) :
    MemLp (KFCausalGaussianStripFamily.spectralLine (translatedFamily F y₀) v r) 2 := by
  have hi : MemLp (fun x : Space => gaussian (x + v)) 2 :=
    gaussian_memLp.comp_measurePreserving (measurePreserving_add_right volume v)
  apply (hi.const_mul (M * Real.exp (Real.pi * r^2) : ℂ)).of_le
    (translated_spectralLine_continuous F d hC v y₀ y r hy hyr).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hM, abs_of_pos (Real.exp_pos _)] using
    translated_spectralLine_bound F d M hB v y₀ y r hy hyr x

include hC hB in
private theorem translated_line_integrable (v : Space) (y₀ y r : ℝ)
    (hy : |y| ≤ d) (hyr : y = y₀ + r) :
    Integrable (KFCausalGaussianStripFamily.line (translatedFamily F y₀) v r) := by
  have h := euclideanSplit_preserves_volume.symm.integrable_comp_of_integrable
    (translated_spectralLine_integrable F d M hC hB v y₀ y r hy hyr)
  simpa only [KFCausalGaussianStripFamily.spectralLine, Function.comp_def,
    MeasurableEquiv.apply_symm_apply] using h

include hF hM hB in
private theorem translated_clock_fourier_shift (v : Space) (y₀ y₁ s : ℝ)
    (hy₀ : |y₀| ≤ d) (hy₁ : |y₁| ≤ d) (hs : y₁ = y₀ + s) (z : TailSpace) (k : ℝ) :
    (𝓕 (fun q : ℝ => KFCausalGaussianStripFamily.line (translatedFamily F y₀) v 0 (q, z))) k =
      (Real.exp (2 * Real.pi * k * s) : ℂ) *
        (𝓕 (fun q : ℝ => KFCausalGaussianStripFamily.line (translatedFamily F y₀) v s (q, z))) k := by
  apply fourier_shift_uIcc
    (fun q => KFCausalGaussianStripFamily.trial (translatedFamily F y₀) v q z)
    (Real.pi / 2)
    (M * (1 * ‖gaussian (z + tail v)‖ * Real.exp (Real.pi * (|s|^2 + (v 0)^2)))) s
    _ (by positivity) _ k
  · intro q hq
    have hq' : |(q + (y₀:ℂ)*I).im| ≤ d := by
      simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] using add_mem_strip_of_mem_uIcc hy₀ hy₁ hs hq
    have hF' : AnalyticAt ℂ (fun q => translatedFamily F y₀ q z) q :=
      AnalyticAt.comp_of_eq (hF z (q + (y₀:ℂ)*I) hq')
        (show AnalyticAt ℂ (fun w : ℂ => w + (y₀:ℂ)*I) q by fun_prop) rfl
    have hg : AnalyticAt ℂ (fun q => clockFactor Real.pi (q + (v 0:ℂ))) q := by
      unfold clockFactor
      fun_prop
    exact (((hF'.mul hg).mul analyticAt_const).differentiableAt)
  · intro q r hr
    have hr_strip : |r + y₀| ≤ d := add_mem_strip_of_mem_uIcc hy₀ hy₁ hs hr
    have hr_abs : |r| ≤ |s| := by simpa using abs_sub_left_of_mem_uIcc hr
    change ‖KFCausalGaussianStripFamily.line (translatedFamily F y₀) v r (q, z)‖ ≤ _
    rw [translated_line_eq F v y₀ (y₀ + r) r rfl (q, z), norm_mul]
    have hbF : ‖F ((q:ℂ) + ((y₀ + r : ℝ):ℂ)*I) z‖ ≤ M := by
      apply hB
      simpa [add_comm] using hr_strip
    have hbG := KFCausalGaussianStrip.clockSlice_bound (fun _ => 1) v |s| 1
      (by norm_num) (fun _ _ => by simp) r q hr_abs z
    calc
      ‖F ((q:ℂ) + ((y₀ + r : ℝ):ℂ)*I) z‖ *
          ‖KFCausalGaussianStrip.line (fun _ => 1) v r (q, z)‖ ≤
          M * ((1 * ‖gaussian (z + tail v)‖ * Real.exp (Real.pi * (|s|^2 + (v 0)^2))) *
            Real.exp (-(Real.pi / 2) * q^2)) :=
        mul_le_mul hbF hbG (norm_nonneg _) hM
      _ = _ := (mul_assoc _ _ _).symm

include hF hC hM hB in
private theorem translated_full_fourier_shift (v : Space) (y₀ y₁ hbar : ℝ)
    (hy₀ : |y₀| ≤ d) (hy₁ : |y₁| ≤ d) (hy₀₁ : y₁ = y₀ - hbar / 2) (k : Space) :
    (exponentialWeight hbar k : ℂ) *
        (𝓕 (KFCausalGaussianStripFamily.spectralLine (translatedFamily F y₀) v 0)) k =
      (𝓕 (KFCausalGaussianStripFamily.spectralLine (translatedFamily F y₀) v (-hbar / 2))) k := by
  have hs : y₁ = y₀ + (-hbar / 2) := by linarith
  have h0 : y₀ = y₀ + 0 := by ring
  have hpoint (q : ℝ) (z : TailSpace) :
      (Real.exp (Real.pi * hbar * q) : ℂ) *
          clockFourier (KFCausalGaussianStripFamily.line (translatedFamily F y₀) v 0) (q, z) =
        clockFourier (KFCausalGaussianStripFamily.line (translatedFamily F y₀) v (-hbar / 2)) (q, z) := by
    change (Real.exp (Real.pi * hbar * q) : ℂ) *
      (𝓕 (fun r : ℝ => KFCausalGaussianStripFamily.line (translatedFamily F y₀) v 0 (r, z))) q = _
    rw [translated_clock_fourier_shift F d M hF hM hB v y₀ y₁ (-hbar / 2) hy₀ hy₁ hs z q,
      ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    have he : Real.pi * hbar * q + 2 * Real.pi * q * (-hbar / 2) = 0 := by ring
    rw [he, Real.exp_zero, Complex.ofReal_one, one_mul]
    rfl
  unfold KFCausalGaussianStripFamily.spectralLine
  rw [fourier_iterated _ (translated_line_continuous F d hC v y₀ y₀ 0 hy₀ h0)
      (translated_line_integrable F d M hC hB v y₀ y₀ 0 hy₀ h0),
    fourier_iterated _ (translated_line_continuous F d hC v y₀ y₁ (-hbar / 2) hy₁ hs)
      (translated_line_integrable F d M hC hB v y₀ y₁ (-hbar / 2) hy₁ hs)]
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul, exponentialWeight]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← hpoint]
  ring

include hC hM hB in
private theorem multiplier_unitState_fourier (v : Space) (ε : ℝ) (hε : 0 < ε)
    (y₀ y r : ℝ) (hy : |y| ≤ d) (hyr : y = y₀ + r) :
    coupledFourier ε hε
        (physicalMultiplier F d M hC hM hB ε hε y hy (unitState |r| v ε hε r le_rfl)) =ᵐ[volume]
      𝓕 (KFCausalGaussianStripFamily.spectralLine (translatedFamily F y₀) v r) := by
  have hcoe : straightening ε hε
      (physicalMultiplier F d M hC hM hB ε hε y hy (unitState |r| v ε hε r le_rfl)) =ᵐ[volume]
      KFCausalGaussianStripFamily.spectralLine (translatedFamily F y₀) v r := by
    filter_upwards [physicalMultiplier_coe F d M hC hM hB ε hε y hy (unitState |r| v ε hε r le_rfl),
      KFCausalClockFloorGaussianGraph.physicalState_coe (fun _ => 1) v |r| 1
        (fun _ _ => analyticAt_const) (by norm_num) (fun _ _ => by simp) ε hε r le_rfl]
      with x hm hu
    change (straightening ε hε (unitState |r| v ε hε r le_rfl)) x = _ at hu
    rw [hm, hu, translated_spectralLine_eq F v y₀ y r hyr x]
  have hLp : straightening ε hε
      (physicalMultiplier F d M hC hM hB ε hε y hy (unitState |r| v ε hε r le_rfl)) =
      (translated_spectralLine_memLp F d M hC hM hB v y₀ y r hy hyr).toLp _ := by
    apply Lp.ext
    filter_upwards [hcoe,
      (translated_spectralLine_memLp F d M hC hM hB v y₀ y r hy hyr).coeFn_toLp] with x h1 h2
    rw [h1, h2]
  change (Lp.fourierTransformₗᵢ Space ℂ) (straightening ε hε _) =ᵐ[volume] _
  rw [hLp]
  exact fourier_toLp_coe _ (translated_spectralLine_integrable F d M hC hB v y₀ y r hy hyr)
    (translated_spectralLine_memLp F d M hC hM hB v y₀ y r hy hyr)

include hF hC hM hB in
theorem graph_multiplier_two_shift (ε : ℝ) (hε : 0 < ε) (hbar y₀ y₁ : ℝ)
    (hy₀ : |y₀| ≤ d) (hy₁ : |y₁| ≤ d) (hy₀₁ : y₁ = y₀ - hbar / 2)
    (f g : Hilbert) (hfg : (f, g) ∈ (longitudinalExponential ε hε hbar (1 / 2)).graph) :
    (physicalMultiplier F d M hC hM hB ε hε y₀ hy₀ f,
      physicalMultiplier F d M hC hM hB ε hε y₁ hy₁ g) ∈
      (longitudinalExponential ε hε hbar (1 / 2)).graph := by
  apply graph_core_lift ε hε hbar _ _ _ f g hfg
  intro v
  have h0 : y₀ = y₀ + 0 := by ring
  have hs : y₁ = y₀ + (-hbar / 2) := by linarith
  rw [← unitState_zero |(0:ℝ)| v ε hε hbar le_rfl,
    ← unitState_shift |-hbar / 2| v ε hε hbar le_rfl]
  apply (longitudinal_exponential_graph ε hε hbar (1 / 2) _ _).mpr
  filter_upwards [multiplier_unitState_fourier F d M hC hM hB v ε hε y₀ y₀ 0 hy₀ h0,
    multiplier_unitState_fourier F d M hC hM hB v ε hε y₀ y₁ (-hbar / 2) hy₁ hs] with k hk hl
  rw [hk, hl, ← translated_full_fourier_shift F d M hF hC hM hB v y₀ y₁ hbar hy₀ hy₁ hy₀₁ k]
  congr 3
  unfold exponentialWeight KFCausalClockFloorFourierMultiplier.symbol
  ring

include hF hC hM hB in
theorem graph_action_two_shift (ε : ℝ) (hε : 0 < ε) (hbar y₀ y₁ : ℝ)
    (hy₀ : |y₀| ≤ d) (hy₁ : |y₁| ≤ d) (hy₀₁ : y₁ = y₀ - hbar / 2)
    (f g : Hilbert) (hfg : (f, g) ∈ (longitudinalExponential ε hε hbar (1 / 2)).graph) :
    (KFCausalMixedStripExponentialGraph.action ε hε F d M hC hM hB y₀ hy₀ f,
      KFCausalMixedStripExponentialGraph.action ε hε F d M hC hM hB y₁ hy₁ g) ∈
      (longitudinalExponential ε hε hbar (1 / 2)).graph := by
  apply (exponential_graph ε hε hbar (1 / 2) _ _).mpr
  rw [unitary_action, unitary_action]
  exact graph_multiplier_two_shift F d M hF hC hM hB ε hε hbar y₀ y₁ hy₀ hy₁ hy₀₁ _ _
    ((exponential_graph ε hε hbar (1 / 2) f g).mp hfg)

private theorem inverseL_straightening_unitary_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    straightening ε hε (unitary ε hε (inverseL ε hε f)) =ᵐ[volume]
      fun x => (halfWeight ε hε ((split 2 4 (modeIsometry x)).2 0) : ℂ)⁻¹ *
        (straightening ε hε (unitary ε hε f)) x := by
  filter_upwards [unitary_straightening_coe ε hε (inverseL ε hε f),
    unitary_straightening_coe ε hε f,
    ((split_preserves_volume 2 4).quasiMeasurePreserving.comp
      mode_preserves_volume.quasiMeasurePreserving).ae (inverseL_clockMixed_coe ε hε f)]
    with x h1 h2 h3
  change (straightening ε hε (unitary ε hε (inverseL ε hε f))) x = _ at h1
  change (straightening ε hε (unitary ε hε f)) x = _ at h2
  change (clockMixed ε hε (inverseL ε hε f)) (split 2 4 (modeIsometry x)) =
    (halfWeight ε hε ((split 2 4 (modeIsometry x)).2 0) : ℂ)⁻¹ *
      (clockMixed ε hε f) (split 2 4 (modeIsometry x)) at h3
  rw [h1, h3, h2]

theorem shiftedMultiplier_inverse_commute (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi * ε / 6) (f : Hilbert) :
    inverseL ε hε (shiftedMultiplier ε hε h N hN y hy f) =
      shiftedMultiplier ε hε h N hN y hy (inverseL ε hε f) := by
  apply (unitary ε hε).injective
  apply (straightening ε hε).injective
  apply Lp.ext
  filter_upwards [inverseL_straightening_unitary_coe ε hε (shiftedMultiplier ε hε h N hN y hy f),
    KFCausalMixedStripExponentialGraph.action_coe ε hε (family ε h N) (Real.pi * ε / 6) N
      (family_line_continuous ε hε h N hN) hN.le (family_bound ε hε h N hN) y hy f,
    KFCausalMixedStripExponentialGraph.action_coe ε hε (family ε h N) (Real.pi * ε / 6) N
      (family_line_continuous ε hε h N hN) hN.le (family_bound ε hε h N hN) y hy (inverseL ε hε f),
    inverseL_straightening_unitary_coe ε hε f] with x h1 h2 h3 h4
  change (straightening ε hε (unitary ε hε (shiftedMultiplier ε hε h N hN y hy f))) x = _ at h2
  change (straightening ε hε (unitary ε hε
    (shiftedMultiplier ε hε h N hN y hy (inverseL ε hε f)))) x = _ at h3
  rw [h1, h2, h3, h4]
  ring

theorem shiftedResolvent_inverse_commute (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi * ε / 6) (f : Hilbert) :
    inverseL ε hε (shiftedResolvent ε hε h N hN y hy f) =
      shiftedResolvent ε hε h N hN y hy (inverseL ε hε f) := by
  simp only [shiftedResolvent, KFCausalClockFloorRadialResolventShifted.shifted,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, map_sub, map_smul,
    shiftedMultiplier_inverse_commute ε hε h N hN y hy f]

private theorem resolvent_graph_of_multiplier_graph (T : Hilbert →ₗ.[ℂ] Hilbert)
    (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y₀ y₁ : ℝ) (hy₀ : |y₀| ≤ Real.pi * ε / 6) (hy₁ : |y₁| ≤ Real.pi * ε / 6)
    (f g : Hilbert) (hfg : (f, g) ∈ T.graph)
    (hm : (shiftedMultiplier ε hε h N hN y₀ hy₀ f,
      shiftedMultiplier ε hε h N hN y₁ hy₁ g) ∈ T.graph) :
    (shiftedResolvent ε hε h N hN y₀ hy₀ f,
      shiftedResolvent ε hε h N hN y₁ hy₁ g) ∈ T.graph :=
  T.graph.sub_mem hfg (T.graph.smul_mem (N⁻¹ : ℂ) hm)

theorem longitudinal_graph_shiftedMultiplier (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y₀ y₁ : ℝ) (hy₀ : |y₀| ≤ Real.pi * ε / 6) (hy₁ : |y₁| ≤ Real.pi * ε / 6)
    (hy₀₁ : y₁ = y₀ - h / 2) (f g : Hilbert)
    (hfg : (f, g) ∈ (longitudinalExponential ε hε h (1 / 2)).graph) :
    (shiftedMultiplier ε hε h N hN y₀ hy₀ f,
      shiftedMultiplier ε hε h N hN y₁ hy₁ g) ∈
      (longitudinalExponential ε hε h (1 / 2)).graph :=
  graph_action_two_shift (family ε h N) (Real.pi * ε / 6) N
    (family_analytic ε hε h N hN) (family_line_continuous ε hε h N hN)
    hN.le (family_bound ε hε h N hN) ε hε h y₀ y₁ hy₀ hy₁ hy₀₁ f g hfg

theorem longitudinal_graph_shiftedResolvent (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y₀ y₁ : ℝ) (hy₀ : |y₀| ≤ Real.pi * ε / 6) (hy₁ : |y₁| ≤ Real.pi * ε / 6)
    (hy₀₁ : y₁ = y₀ - h / 2) (f g : Hilbert)
    (hfg : (f, g) ∈ (longitudinalExponential ε hε h (1 / 2)).graph) :
    (shiftedResolvent ε hε h N hN y₀ hy₀ f,
      shiftedResolvent ε hε h N hN y₁ hy₁ g) ∈
      (longitudinalExponential ε hε h (1 / 2)).graph :=
  resolvent_graph_of_multiplier_graph (longitudinalExponential ε hε h (1 / 2))
    ε hε h N hN y₀ y₁ hy₀ hy₁ f g hfg
    (longitudinal_graph_shiftedMultiplier ε hε h N hN y₀ y₁ hy₀ hy₁ hy₀₁ f g hfg)

theorem ordered_graph_shiftedMultiplier (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y₀ y₁ : ℝ) (hy₀ : |y₀| ≤ Real.pi * ε / 6) (hy₁ : |y₁| ≤ Real.pi * ε / 6)
    (hy₀₁ : y₁ = y₀ - h / 2) (f g : Hilbert)
    (hfg : (f, g) ∈ (orderedExponential ε hε h).graph) :
    (shiftedMultiplier ε hε h N hN y₀ hy₀ f,
      shiftedMultiplier ε hε h N hN y₁ hy₁ g) ∈
      (orderedExponential ε hε h).graph := by
  rw [ordered_graph_iff] at hfg ⊢
  rw [shiftedMultiplier_inverse_commute]
  exact longitudinal_graph_shiftedMultiplier ε hε h N hN y₀ y₁ hy₀ hy₁ hy₀₁ (inverseL ε hε f) g hfg

theorem ordered_graph_shiftedResolvent (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y₀ y₁ : ℝ) (hy₀ : |y₀| ≤ Real.pi * ε / 6) (hy₁ : |y₁| ≤ Real.pi * ε / 6)
    (hy₀₁ : y₁ = y₀ - h / 2) (f g : Hilbert)
    (hfg : (f, g) ∈ (orderedExponential ε hε h).graph) :
    (shiftedResolvent ε hε h N hN y₀ hy₀ f,
      shiftedResolvent ε hε h N hN y₁ hy₁ g) ∈
      (orderedExponential ε hε h).graph :=
  resolvent_graph_of_multiplier_graph (orderedExponential ε hε h)
    ε hε h N hN y₀ y₁ hy₀ hy₁ f g hfg
    (ordered_graph_shiftedMultiplier ε hε h N hN y₀ y₁ hy₀ hy₁ hy₀₁ f g hfg)

theorem ordered_domain_shiftedMultiplier (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y₀ y₁ : ℝ) (hy₀ : |y₀| ≤ Real.pi * ε / 6) (hy₁ : |y₁| ≤ Real.pi * ε / 6)
    (hy₀₁ : y₁ = y₀ - h / 2) (f : Hilbert) (hf : f ∈ (orderedExponential ε hε h).domain) :
    shiftedMultiplier ε hε h N hN y₀ hy₀ f ∈ (orderedExponential ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (ordered_graph_shiftedMultiplier ε hε h N hN y₀ y₁ hy₀ hy₁ hy₀₁
    f _ ((orderedExponential ε hε h).mem_graph ⟨f, hf⟩))

theorem ordered_domain_shiftedResolvent (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y₀ y₁ : ℝ) (hy₀ : |y₀| ≤ Real.pi * ε / 6) (hy₁ : |y₁| ≤ Real.pi * ε / 6)
    (hy₀₁ : y₁ = y₀ - h / 2) (f : Hilbert) (hf : f ∈ (orderedExponential ε hε h).domain) :
    shiftedResolvent ε hε h N hN y₀ hy₀ f ∈ (orderedExponential ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (ordered_graph_shiftedResolvent ε hε h N hN y₀ y₁ hy₀ hy₁ hy₀₁
    f _ ((orderedExponential ε hε h).mem_graph ⟨f, hf⟩))

theorem linear_matter_graph_shiftedMultiplier (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y₀ y₁ : ℝ) (hy₀ : |y₀| ≤ Real.pi * ε / 6) (hy₁ : |y₁| ≤ Real.pi * ε / 6)
    (hy₀₁ : y₁ = y₀ - h / 2) (f g : Hilbert)
    (hfg : (f, g) ∈ (matterFactor ε hε h (physicalField pointField)).graph) :
    (shiftedMultiplier ε hε h N hN y₀ hy₀ f,
      shiftedMultiplier ε hε h N hN y₁ hy₁ g) ∈
      (matterFactor ε hε h (physicalField pointField)).graph := by
  rw [matterFactor, composition_graph] at hfg ⊢
  let u := Classical.choose hfg
  have hu : (f, u) ∈ (orderedExponential ε hε h).graph ∧
      (u, g) ∈ (physicalField pointField).graph := Classical.choose_spec hfg
  exact ⟨shiftedMultiplier ε hε h N hN y₁ hy₁ u,
    ordered_graph_shiftedMultiplier ε hε h N hN y₀ y₁ hy₀ hy₁ hy₀₁ f u hu.1,
    KFCausalMixedStripFieldGraph.field_graph_action ε hε (family ε h N) (Real.pi * ε / 6) N
      (family_line_continuous ε hε h N hN) hN.le (family_bound ε hε h N hN)
      y₁ hy₁ u g hu.2⟩

theorem linear_matter_graph_shiftedResolvent (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y₀ y₁ : ℝ) (hy₀ : |y₀| ≤ Real.pi * ε / 6) (hy₁ : |y₁| ≤ Real.pi * ε / 6)
    (hy₀₁ : y₁ = y₀ - h / 2) (f g : Hilbert)
    (hfg : (f, g) ∈ (matterFactor ε hε h (physicalField pointField)).graph) :
    (shiftedResolvent ε hε h N hN y₀ hy₀ f,
      shiftedResolvent ε hε h N hN y₁ hy₁ g) ∈
      (matterFactor ε hε h (physicalField pointField)).graph :=
  resolvent_graph_of_multiplier_graph (matterFactor ε hε h (physicalField pointField))
    ε hε h N hN y₀ y₁ hy₀ hy₁ f g hfg
    (linear_matter_graph_shiftedMultiplier ε hε h N hN y₀ y₁ hy₀ hy₁ hy₀₁ f g hfg)

theorem quadratic_matter_graph_shiftedMultiplier (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y₀ y₁ : ℝ) (hy₀ : |y₀| ≤ Real.pi * ε / 6) (hy₁ : |y₁| ≤ Real.pi * ε / 6)
    (hy₀₁ : y₁ = y₀ - h / 2) (f g : Hilbert)
    (hfg : (f, g) ∈ (matterFactor ε hε h (fieldSquare pointField)).graph) :
    (shiftedMultiplier ε hε h N hN y₀ hy₀ f,
      shiftedMultiplier ε hε h N hN y₁ hy₁ g) ∈
      (matterFactor ε hε h (fieldSquare pointField)).graph := by
  rw [matterFactor, composition_graph] at hfg ⊢
  let u := Classical.choose hfg
  have hu : (f, u) ∈ (orderedExponential ε hε h).graph ∧
      (u, g) ∈ (fieldSquare pointField).graph := Classical.choose_spec hfg
  exact ⟨shiftedMultiplier ε hε h N hN y₁ hy₁ u,
    ordered_graph_shiftedMultiplier ε hε h N hN y₀ y₁ hy₀ hy₁ hy₀₁ f u hu.1,
    KFCausalMixedStripFieldGraph.square_graph_action ε hε (family ε h N) (Real.pi * ε / 6) N
      (family_line_continuous ε hε h N hN) hN.le (family_bound ε hε h N hN)
      y₁ hy₁ u g hu.2⟩

theorem quadratic_matter_graph_shiftedResolvent (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y₀ y₁ : ℝ) (hy₀ : |y₀| ≤ Real.pi * ε / 6) (hy₁ : |y₁| ≤ Real.pi * ε / 6)
    (hy₀₁ : y₁ = y₀ - h / 2) (f g : Hilbert)
    (hfg : (f, g) ∈ (matterFactor ε hε h (fieldSquare pointField)).graph) :
    (shiftedResolvent ε hε h N hN y₀ hy₀ f,
      shiftedResolvent ε hε h N hN y₁ hy₁ g) ∈
      (matterFactor ε hε h (fieldSquare pointField)).graph :=
  resolvent_graph_of_multiplier_graph (matterFactor ε hε h (fieldSquare pointField))
    ε hε h N hN y₀ y₁ hy₀ hy₁ f g hfg
    (quadratic_matter_graph_shiftedMultiplier ε hε h N hN y₀ y₁ hy₀ hy₁ hy₀₁ f g hfg)

theorem narrow_half_shift_bound (ε h : ℝ) (hb : |h| ≤ Real.pi * ε / 6) :
    |h / 2| ≤ Real.pi * ε / 6 := by
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith [abs_nonneg h]

theorem forward_ordered_graph_shiftedResolvent (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hb : |h| ≤ Real.pi * ε / 6) (f g : Hilbert)
    (hfg : (f, g) ∈ (orderedExponential ε hε h).graph) :
    (shiftedResolvent ε hε h N hN h hb f,
      shiftedResolvent ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hb) g) ∈
      (orderedExponential ε hε h).graph :=
  ordered_graph_shiftedResolvent ε hε h N hN h (h / 2) hb (narrow_half_shift_bound ε h hb)
    (by ring) f g hfg

theorem forward_linear_matter_graph_shiftedResolvent (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hb : |h| ≤ Real.pi * ε / 6) (f g : Hilbert)
    (hfg : (f, g) ∈ (matterFactor ε hε h (physicalField pointField)).graph) :
    (shiftedResolvent ε hε h N hN h hb f,
      shiftedResolvent ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hb) g) ∈
      (matterFactor ε hε h (physicalField pointField)).graph :=
  linear_matter_graph_shiftedResolvent ε hε h N hN h (h / 2) hb (narrow_half_shift_bound ε h hb)
    (by ring) f g hfg

theorem forward_quadratic_matter_graph_shiftedResolvent (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hb : |h| ≤ Real.pi * ε / 6) (f g : Hilbert)
    (hfg : (f, g) ∈ (matterFactor ε hε h (fieldSquare pointField)).graph) :
    (shiftedResolvent ε hε h N hN h hb f,
      shiftedResolvent ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hb) g) ∈
      (matterFactor ε hε h (fieldSquare pointField)).graph :=
  quadratic_matter_graph_shiftedResolvent ε hε h N hN h (h / 2) hb (narrow_half_shift_bound ε h hb)
    (by ring) f g hfg

#print axioms narrow_half_shift_bound

#print axioms graph_multiplier_two_shift
#print axioms graph_action_two_shift
#print axioms shiftedMultiplier_inverse_commute
#print axioms shiftedResolvent_inverse_commute
#print axioms longitudinal_graph_shiftedMultiplier
#print axioms longitudinal_graph_shiftedResolvent
#print axioms ordered_graph_shiftedMultiplier
#print axioms ordered_graph_shiftedResolvent
#print axioms ordered_domain_shiftedMultiplier
#print axioms ordered_domain_shiftedResolvent
#print axioms linear_matter_graph_shiftedMultiplier
#print axioms linear_matter_graph_shiftedResolvent
#print axioms quadratic_matter_graph_shiftedMultiplier
#print axioms quadratic_matter_graph_shiftedResolvent
#print axioms forward_ordered_graph_shiftedResolvent
#print axioms forward_linear_matter_graph_shiftedResolvent
#print axioms forward_quadratic_matter_graph_shiftedResolvent
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventShiftedOrderedTransport
