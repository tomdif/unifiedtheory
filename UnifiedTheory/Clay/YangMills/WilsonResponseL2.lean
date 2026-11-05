/- Annealed control of the actual normalized Wilson boundary response.
Conditional averaging contracts the mean square, with the actual marginal
and full Wilson law. No ultraviolet error estimate is assumed to be proved. -/
import UnifiedTheory.Clay.YangMills.WilsonBoundaryResponse
import UnifiedTheory.Clay.YangMills.ConnectedGramLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonResponseL2
noncomputable section
open MeasureTheory BoundaryReflectionGluing NormalizedBoundaryResponse

section OneMeasure
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]

theorem mean_square_le (F : Y → ℂ) (hF : Continuous F) :
    ‖∫ y, F y ∂μ‖^2 ≤ ∫ y, ‖F y‖^2 ∂μ := by
  have h := ConnectedGramLimit.complex_variance_identity μ F hF
  simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, integral_complex_ofReal, Complex.sub_re,
    Complex.ofReal_re] at h
  have hn : 0 ≤ ∫ y, ‖F y - ∫ x, F x ∂μ‖^2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  linarith
end OneMeasure

section Boundary
variable {B X : Type*} [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μB : Measure B) (μX : Measure X) [IsProbabilityMeasure μB] [IsProbabilityMeasure μX]

theorem response_square_le (A : B × X → ℝ) (hA : Continuous A)
    (F : B × X → ℂ) (hF : Continuous F) (b : B) :
    ‖response μX A F b‖^2 ≤
      (response μX A (fun z => ((‖F z‖^2 : ℝ) : ℂ)) b).re := by
  let ν := CompactGibbsContinuity.law μX (fun x => A (b,x))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability μX _
    (hA.comp (continuous_const.prodMk continuous_id))
  rw [response_eq_half_expectation μX A hA F b,
    response_eq_half_expectation μX A hA (fun z => ((‖F z‖^2 : ℝ) : ℂ)) b,
    integral_complex_ofReal, Complex.ofReal_re]
  exact mean_square_le ν _ (hF.comp (continuous_const.prodMk continuous_id))

/-- The normalization is integrated against its true marginal. No lower
bound on an individual half partition or history probability is used. -/
theorem response_l2_bound (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) (F : B × X → ℂ) (hF : Continuous F) :
    (∫ b, ‖response μX A F b‖^2 ∂marginal μB μX w A) ≤
      ∫ z, ‖halfObservable F z‖^2 ∂law μB μX w A := by
  letI := marginal_probability μB μX w hcw hw A hA
  letI := law_probability μB μX w hcw hw A hA
  have hcQ : Continuous (fun z => ((‖F z‖^2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hF.norm.pow 2)
  have hcR := response_continuous μX A hA _ hcQ
  have hiR : Integrable (response μX A (fun z => ((‖F z‖^2 : ℝ) : ℂ)))
      (marginal μB μX w A) :=
    hcR.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he := congrArg Complex.re (expectation_identity μB μX w hcw hw A hA
    (fun z => ((‖F z‖^2 : ℝ) : ℂ)) hcQ)
  simp only [halfObservable, integral_complex_ofReal, Complex.ofReal_re] at he
  have hri : (∫ b, (response μX A (fun z => ((‖F z‖^2 : ℝ) : ℂ)) b).re
      ∂marginal μB μX w A) =
      (∫ b, response μX A (fun z => ((‖F z‖^2 : ℝ) : ℂ)) b
        ∂marginal μB μX w A).re := integral_re hiR
  calc
    _ ≤ ∫ b, (response μX A (fun z => ((‖F z‖^2 : ℝ) : ℂ)) b).re
        ∂marginal μB μX w A :=
      integral_mono (((response_continuous μX A hA F hF).norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
        hiR.re (response_square_le μX A hA F hF)
    _ = _ := hri.trans he.symm

theorem response_sub_boundary (A : B × X → ℝ) (hA : Continuous A)
    (F : B × X → ℂ) (hF : Continuous F) (g : B → ℂ) (b : B) :
    response μX A (fun z => F z - g z.1) b = response μX A F b - g b := by
  let ν := CompactGibbsContinuity.law μX (fun x => A (b,x))
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability μX _
    (hA.comp (continuous_const.prodMk continuous_id))
  rw [response_eq_half_expectation μX A hA _ b,
    response_eq_half_expectation μX A hA F b]
  change (∫ x, F (b,x) - g b ∂ν) = (∫ x, F (b,x) ∂ν) - g b
  have hi : Integrable (fun x : X => F (b,x)) ν :=
    (hF.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_sub hi (integrable_const _)]
  simp

/-- A mean-square insertion error, averaged under the full interacting law,
controls its conditional mean-square error. An all-boundaries supremum is
not needed for this conclusion. -/
theorem response_error_l2_bound (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) (F : B × X → ℂ) (hF : Continuous F)
    (g : B → ℂ) (hg : Continuous g) :
    (∫ b, ‖response μX A F b - g b‖^2 ∂marginal μB μX w A) ≤
      ∫ z, ‖halfObservable F z - g z.1‖^2 ∂law μB μX w A := by
  have h := response_l2_bound μB μX w hcw hw A hA (fun z => F z - g z.1)
    (hF.sub (hg.comp continuous_fst))
  simpa only [response_sub_boundary μX A hA F hF g, halfObservable] using h
end Boundary

variable (N : ℕ) [NeZero N]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- This is the same inequality under the original periodic Wilson measure,
not a replacement probability law on supplied histories. -/
theorem actual_wilson_response_error (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (β c : ℝ)
    (F : PeriodicHalfSplit.BoundaryConfiguration N G ×
      PeriodicHalfSplit.HalfConfiguration N G → ℂ) (hF : Continuous F)
    (g : PeriodicHalfSplit.BoundaryConfiguration N G → ℂ) (hg : Continuous g) :
    (∫ b, ‖WilsonBoundaryResponse.response N G χ β c F b - g b‖^2
      ∂WilsonBoundaryResponse.marginal N G χ β c) ≤
    ∫ U, ‖PeriodicSiteReflection.observable N G F U -
      g (PeriodicSiteReflection.coordinates N G U).1‖^2
        ∂PeriodicLattice4.wilsonLaw (2*N) G χ β c := by
  have ht := (PeriodicSiteReflection.wilsonLaw_to_boundary N G χ hcχ hχ hinv β c).integral_comp
    (PeriodicSiteReflection.coordinates N G).measurableEmbedding
    (fun z => ‖halfObservable F z - g z.1‖^2)
  change _ ≤ ∫ U, ‖halfObservable F (PeriodicSiteReflection.coordinates N G U) -
    g (PeriodicSiteReflection.coordinates N G U).1‖^2 ∂PeriodicLattice4.wilsonLaw (2*N) G χ β c
  rw [ht]
  exact response_error_l2_bound _ _ _
    (PeriodicSiteReflection.boundaryWeight_continuous N G χ hcχ β c)
    (PeriodicSiteReflection.boundaryWeight_positive N G χ β c) _
    (PeriodicSiteReflection.halfAction_continuous N G χ hcχ β c) F hF g hg

end
end UnifiedTheory.Clay.YangMills.WilsonResponseL2
