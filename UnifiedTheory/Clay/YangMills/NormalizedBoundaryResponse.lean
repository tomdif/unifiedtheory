/- Exact normalized boundary response of the proved finite gluing law.
The boundary measure is its actual marginal, not a supplied measure. Centered
reflection is its conditional-mean variance; this does not assert nonconstancy. -/
import UnifiedTheory.Clay.YangMills.BoundaryAmplitudeRealization
import UnifiedTheory.Clay.YangMills.CompactGibbsContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.NormalizedBoundaryResponse
noncomputable section
open MeasureTheory BoundaryReflectionGluing

variable {B X : Type*} [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μB : Measure B) (μX : Measure X) [IsProbabilityMeasure μB] [IsProbabilityMeasure μX]

def mass (A : B × X → ℝ) (b : B) : ℝ := ∫ x, Real.exp (-A (b,x)) ∂μX

theorem mass_positive (A : B × X → ℝ) (hA : Continuous A) (b : B) :
    0 < mass μX A b :=
  CompactGibbsContinuity.partition_positive μX (fun x => A (b,x))
    (hA.comp (continuous_const.prodMk continuous_id))

theorem amplitude_boundary (A : B × X → ℝ) (g : B → ℂ) (b : B) :
    amplitude μX A (fun z => g z.1) b = (mass μX A b : ℂ) * g b := by
  change (∫ x, (Real.exp (-A (b,x)) : ℂ) * g b ∂μX) = _
  rw [integral_mul_const, mass, integral_complex_ofReal]

theorem amplitude_one (A : B × X → ℝ) (b : B) :
    amplitude μX A (fun _ => 1) b = (mass μX A b : ℂ) := by
  simpa only [mul_one] using amplitude_boundary μX A (fun _ => 1) b

theorem mass_continuous (A : B × X → ℝ) (hA : Continuous A) : Continuous (mass μX A) := by
  have h := Complex.continuous_re.comp
    (BoundaryAmplitudeRealization.amplitude_continuous μX A hA (fun _ => 1) continuous_const)
  simpa only [Function.comp_def, amplitude_one, Complex.ofReal_re] using h

def response (A : B × X → ℝ) (f : B × X → ℂ) (b : B) : ℂ :=
  amplitude μX A f b / (mass μX A b : ℂ)

theorem response_continuous (A : B × X → ℝ) (hA : Continuous A)
    (f : B × X → ℂ) (hf : Continuous f) : Continuous (response μX A f) :=
  (BoundaryAmplitudeRealization.amplitude_continuous μX A hA f hf).div
    (Complex.continuous_ofReal.comp (mass_continuous μX A hA))
    (fun b => Complex.ofReal_ne_zero.mpr (mass_positive μX A hA b).ne')

@[simp] theorem response_one (A : B × X → ℝ) (hA : Continuous A) (b : B) :
    response μX A (fun _ => 1) b = 1 := by
  rw [response, amplitude_one, div_self]
  exact Complex.ofReal_ne_zero.mpr (mass_positive μX A hA b).ne'

def marginal (w : B → ℝ) (A : B × X → ℝ) : Measure B :=
  (law μB μX w A).map Prod.fst

theorem marginal_probability (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) : IsProbabilityMeasure (marginal μB μX w A) := by
  letI := law_probability μB μX w hcw hw A hA
  exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable

/-- The actual marginal weights the unnormalized boundary measure by the
square of the positive half partition. -/
theorem marginal_integral (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) (g : B → ℂ) (hg : Continuous g) :
    (∫ b, g b ∂marginal μB μX w A) =
      ∫ b, ((mass μX A b : ℂ)^2) * g b
        ∂BoundaryAmplitudeRealization.boundaryMeasure μB μX w A := by
  rw [marginal, integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable]
  have h := BoundaryAmplitudeRealization.pairing_identity μB μX w hcw hw A hA
    (fun _ => 1) (fun z => g z.1) continuous_const (hg.comp continuous_fst)
  simpa only [halfObservable, star_one, one_mul, amplitude_boundary, amplitude_one, mul_one,
    Complex.star_def, Complex.conj_ofReal, pow_two, mul_assoc] using h

/-- Reflection is exactly the ordinary pairing of normalized conditional means. -/
theorem pairing_identity (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A)
    (f g : B × X → ℂ) (hf : Continuous f) (hg : Continuous g) :
    (∫ z, star (halfObservable f (reflection z)) * halfObservable g z ∂law μB μX w A) =
      ∫ b, star (response μX A f b) * response μX A g b ∂marginal μB μX w A := by
  rw [BoundaryAmplitudeRealization.pairing_identity μB μX w hcw hw A hA f g hf hg,
    marginal_integral μB μX w hcw hw A hA (fun b => star (response μX A f b) * response μX A g b)
      ((response_continuous μX A hA f hf).star.mul (response_continuous μX A hA g hg))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun b => by
    have hm : (mass μX A b : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (mass_positive μX A hA b).ne'
    simp only [response, star_div₀, Complex.star_def, Complex.conj_ofReal]
    field_simp)

theorem expectation_identity (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) (f : B × X → ℂ) (hf : Continuous f) :
    (∫ z, halfObservable f z ∂law μB μX w A) =
      ∫ b, response μX A f b ∂marginal μB μX w A := by
  have h := pairing_identity μB μX w hcw hw A hA (fun _ => 1) f continuous_const hf
  simpa only [halfObservable, response_one μX A hA, star_one, one_mul] using h

/-- This response is the expectation under the explicitly normalized half law. -/
theorem response_eq_half_expectation (A : B × X → ℝ) (hA : Continuous A)
    (f : B × X → ℂ) (b : B) :
    response μX A f b = ∫ x, f (b,x) ∂CompactGibbsContinuity.law μX (fun x => A (b,x)) := by
  rw [CompactGibbsContinuity.expectation_formula μX (fun x : X => A (b,x))
    (hA.comp (continuous_const.prodMk continuous_id)) (fun x => f (b,x))]
  simp only [response, mass, amplitude, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  rw [mul_comm]

theorem response_sub_const (A : B × X → ℝ) (hA : Continuous A)
    (f : B × X → ℂ) (hf : Continuous f) (c : ℂ) (b : B) :
    response μX A (fun z => f z - c) b = response μX A f b - c := by
  have he : Continuous (fun x : X => (Real.exp (-A (b,x)) : ℂ)) := by fun_prop
  have hf' : Continuous (fun x : X => f (b,x)) := hf.comp (continuous_const.prodMk continuous_id)
  have hi1 : Integrable (fun x : X => (Real.exp (-A (b,x)) : ℂ) * f (b,x)) μX :=
    (he.mul hf').integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun x : X => (Real.exp (-A (b,x)) : ℂ) * c) μX :=
    (he.mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ha : amplitude μX A (fun z => f z - c) b =
      amplitude μX A f b - (mass μX A b : ℂ) * c := by
    unfold amplitude
    simp_rw [mul_sub]
    rw [integral_sub hi1 hi2, integral_mul_const, integral_complex_ofReal]
    rfl
  have hm : (mass μX A b : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mass_positive μX A hA b).ne'
  rw [response, ha, response]
  field_simp

/-- Exact squared-response formula, including an arbitrary constant subtraction. -/
theorem centered_pairing_identity (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) (f : B × X → ℂ) (hf : Continuous f) (c : ℂ) :
    (∫ z, star (halfObservable f (reflection z) - c) * (halfObservable f z - c)
      ∂law μB μX w A) =
      ((∫ b, ‖response μX A f b - c‖ ^ 2 ∂marginal μB μX w A : ℝ) : ℂ) := by
  have h := pairing_identity μB μX w hcw hw A hA (fun z => f z - c)
    (fun z => f z - c) (hf.sub continuous_const) (hf.sub continuous_const)
  simp only [halfObservable, response_sub_const μX A hA f hf c,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    integral_complex_ofReal] at h
  exact h

/-- The finite OS null condition is exactly constancy of the normalized
boundary response almost everywhere under the actual boundary marginal. -/
theorem centered_zero_iff (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) (f : B × X → ℂ) (hf : Continuous f) (c : ℂ) :
    (∫ z, star (halfObservable f (reflection z) - c) * (halfObservable f z - c)
      ∂law μB μX w A) = 0 ↔
      ∀ᵐ b ∂marginal μB μX w A, response μX A f b = c := by
  letI := marginal_probability μB μX w hcw hw A hA
  rw [centered_pairing_identity μB μX w hcw hw A hA f hf c, Complex.ofReal_eq_zero,
    integral_eq_zero_iff_of_nonneg (fun b => sq_nonneg _)
      (((response_continuous μX A hA f hf).sub continuous_const).norm.pow 2
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp only [Filter.EventuallyEq, Pi.zero_apply, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]

theorem centered_positive_iff (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) (f : B × X → ℂ) (hf : Continuous f) (c : ℂ) :
    0 < (∫ z, star (halfObservable f (reflection z) - c) * (halfObservable f z - c)
      ∂law μB μX w A).re ↔
      ¬ ∀ᵐ b ∂marginal μB μX w A, response μX A f b = c := by
  rw [← centered_zero_iff μB μX w hcw hw A hA f hf c,
    centered_pairing_identity μB μX w hcw hw A hA f hf c,
    Complex.ofReal_re, Complex.ofReal_eq_zero]
  exact (lt_iff_le_and_ne).trans (by
    have h : 0 ≤ ∫ b, ‖response μX A f b - c‖ ^ 2 ∂marginal μB μX w A :=
      integral_nonneg (fun b => sq_nonneg _)
    simp [h, ne_comm])

/-- A boundary probe can certify a reflected lower bound only through a
nonzero response overlap. This is the exact Cauchy--Schwarz estimate under
the actual normalized marginal. -/
theorem source_probe_bound (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) (f : B × X → ℂ) (hf : Continuous f)
    (c : ℂ) (probe : B → ℂ) (hp : Continuous probe) :
    ‖∫ b, star (probe b) * (response μX A f b - c) ∂marginal μB μX w A‖^2 ≤
      (∫ b, ‖probe b‖^2 ∂marginal μB μX w A) *
      (∫ z, star (halfObservable f (reflection z) - c) * (halfObservable f z - c)
        ∂law μB μX w A).re := by
  letI := marginal_probability μB μX w hcw hw A hA
  let P : C(B, ℂ) := ⟨probe, hp⟩
  let F : C(B, ℂ) := ⟨fun b => response μX A f b - c,
    (response_continuous μX A hA f hf).sub continuous_const⟩
  let toL : C(B, ℂ) → Lp ℂ 2 (marginal μB μX w A) :=
    fun g => ContinuousMap.toLp 2 (marginal μB μX w A) ℂ g
  have hn (g : C(B, ℂ)) : ‖toL g‖^2 = ∫ b, ‖g b‖^2 ∂marginal μB μX w A := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    change (inner ℂ (toL g) (toL g)).re = _
    rw [ContinuousMap.inner_toLp]
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq,
      integral_complex_ofReal, Complex.ofReal_re]
  have hi : (∫ b, star (probe b) * (response μX A f b - c) ∂marginal μB μX w A) =
      inner ℂ (toL P) (toL F) := by
    rw [ContinuousMap.inner_toLp]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun b => mul_comm _ _)
  rw [hi, centered_pairing_identity μB μX w hcw hw A hA f hf c, Complex.ofReal_re]
  have h := norm_inner_le_norm (𝕜 := ℂ) (toL P) (toL F)
  have hs := mul_self_le_mul_self (norm_nonneg _) h
  simpa only [← pow_two, mul_pow, hn, P, F, ContinuousMap.coe_mk] using hs

/-- At zero interaction an interior-only observable has constant boundary
response, despite arbitrary fluctuations within its half. -/
theorem zero_action_interior_response (f : X → ℂ) (b : B) :
    response μX (fun _ : B × X => 0) (fun z => f z.2) b = ∫ x, f x ∂μX := by
  simp [response, amplitude, mass]

end
end UnifiedTheory.Clay.YangMills.NormalizedBoundaryResponse
