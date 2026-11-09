/- The actual periodic Wilson marginal and normalized half response.
For a closed-half supported Schwartz smear, its centered reflected form is
exactly the marginal variance of this response. Nonconstancy is not assumed
proved; in particular this identity supplies no ultraviolet positive floor. -/
import UnifiedTheory.Clay.YangMills.NormalizedBoundaryResponse
import UnifiedTheory.Clay.YangMills.WilsonReflectedJointLimit
import UnifiedTheory.Clay.YangMills.ReflectedWilsonRenormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBoundaryResponse
noncomputable section
open MeasureTheory PeriodicLattice4 PeriodicHalfSplit PeriodicSiteReflection
open PeriodicTimeReflection ContinuumControl

variable (n : ℕ) [NeZero n]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def marginal (χ : G → ℂ) (β c : ℝ) : Measure (BoundaryConfiguration n G) :=
  NormalizedBoundaryResponse.marginal (boundaryMeasure n G) (halfMeasure n G)
    (boundaryWeight n G χ β c) (halfAction n G χ β c)

def response (χ : G → ℂ) (β c : ℝ)
    (F : BoundaryConfiguration n G × HalfConfiguration n G → ℂ) :
    BoundaryConfiguration n G → ℂ :=
  NormalizedBoundaryResponse.response (halfMeasure n G) (halfAction n G χ β c) F

theorem marginal_probability (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ) :
    IsProbabilityMeasure (marginal n G χ β c) :=
  NormalizedBoundaryResponse.marginal_probability _ _ _
    (boundaryWeight_continuous n G χ hcχ β c) (boundaryWeight_positive n G χ β c)
    _ (halfAction_continuous n G χ hcχ β c)

theorem marginal_eq_map (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (β c : ℝ) :
    marginal n G χ β c = (wilsonLaw (2*n) G χ β c).map
      (fun U => (coordinates n G U).1) := by
  unfold marginal NormalizedBoundaryResponse.marginal
  rw [← (wilsonLaw_to_boundary n G χ hcχ hχ hinv β c).map_eq,
    Measure.map_map measurable_fst (coordinates n G).measurable]
  rfl

theorem response_continuous (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ)
    (F : BoundaryConfiguration n G × HalfConfiguration n G → ℂ) (hF : Continuous F) :
    Continuous (response n G χ β c F) :=
  NormalizedBoundaryResponse.response_continuous _ _
    (halfAction_continuous n G χ hcχ β c) F hF

theorem expectation_identity (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (β c : ℝ) (F : BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (hF : Continuous F) :
    (∫ U, observable n G F U ∂wilsonLaw (2*n) G χ β c) =
      ∫ b, response n G χ β c F b ∂marginal n G χ β c := by
  unfold observable
  rw [(wilsonLaw_to_boundary n G χ hcχ hχ hinv β c).integral_comp
    (coordinates n G).measurableEmbedding (BoundaryReflectionGluing.halfObservable F)]
  exact NormalizedBoundaryResponse.expectation_identity _ _ _
    (boundaryWeight_continuous n G χ hcχ β c) (boundaryWeight_positive n G χ β c)
    _ (halfAction_continuous n G χ hcχ β c) F hF

theorem centered_identity (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (β c : ℝ) (F : BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (hF : Continuous F) (center : ℂ) :
    (∫ U, star (observable n G F (reflectConfiguration (2*n) G U) - center) *
      (observable n G F U - center) ∂wilsonLaw (2*n) G χ β c) =
      ((∫ b, ‖response n G χ β c F b - center‖^2 ∂marginal n G χ β c : ℝ) : ℂ) := by
  have ht := (wilsonLaw_to_boundary n G χ hcχ hχ hinv β c).integral_comp
    (coordinates n G).measurableEmbedding
    (fun z => star (BoundaryReflectionGluing.halfObservable F
      (BoundaryReflectionGluing.reflection z) - center) *
        (BoundaryReflectionGluing.halfObservable F z - center))
  have hs : (fun U => star (observable n G F (reflectConfiguration (2*n) G U) - center) *
      (observable n G F U - center)) =
      (fun U => star (BoundaryReflectionGluing.halfObservable F
        (BoundaryReflectionGluing.reflection (coordinates n G U)) - center) *
          (BoundaryReflectionGluing.halfObservable F (coordinates n G U) - center)) := by
    funext U
    simp only [observable]
    rw [show coordinates n G (reflectConfiguration (2*n) G U) =
      BoundaryReflectionGluing.reflection (coordinates n G U) from split_reflection n G U]
  rw [hs, ht]
  exact NormalizedBoundaryResponse.centered_pairing_identity _ _ _
    (boundaryWeight_continuous n G χ hcχ β c) (boundaryWeight_positive n G χ β c)
    _ (halfAction_continuous n G χ hcχ β c) F hF center

/-- A fixed supported Schwartz test is attached to this dictionary under the
original Wilson law; the observable and action characters may differ. -/
theorem smeared_centered_identity (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (β c a : ℝ) (plane : Plane) (ψ : G → ℂ) (hcψ : Continuous ψ)
    (f : CorrelationTest 1) (hs : ClosedHalfSmearing.Supported n a plane 1 f) :
    ReflectedWilsonRenormalization.reflectedForm G (2*n) a plane ψ χ β c f f =
      ((∫ b, ‖response n G χ β c (ClosedHalfSmearing.halfObservable n G a plane ψ 1 f) b -
        (∫ U, WilsonSmearedObservable.observable G (2*n) a plane ψ 1 f U
          ∂wilsonLaw (2*n) G χ β c)‖^2 ∂marginal n G χ β c : ℝ) : ℂ) := by
  let F := ClosedHalfSmearing.halfObservable n G a plane ψ 1 f
  let center := ∫ U, WilsonSmearedObservable.observable G (2*n) a plane ψ 1 f U
    ∂wilsonLaw (2*n) G χ β c
  have he (U : RegulatedGauge.Configuration (Vertex (2*n)) G) :
      WilsonSmearedObservable.observable G (2*n) a plane ψ 1 f U =
        observable n G F (reflectConfiguration (2*n) G U) := by
    rw [ClosedHalfSmearing.half_identification n G a plane ψ 1 f hs,
      ReflectedWilsonKernel.positiveObservable_eq_reflected]
  change (∫ U, star (WilsonSmearedObservable.observable G (2*n) a plane ψ 1 f
      (reflectConfiguration (2*n) G U) - center) *
      (WilsonSmearedObservable.observable G (2*n) a plane ψ 1 f U - center)
        ∂wilsonLaw (2*n) G χ β c) =
    ((∫ b, ‖response n G χ β c F b - center‖^2 ∂marginal n G χ β c : ℝ) : ℂ)
  simp_rw [he]
  have hr := WilsonReflectedJointLimit.integral_reflection n G χ hcχ hχ hinv β c
    (fun U => star (observable n G F (reflectConfiguration (2*n) G U) - center) *
      (observable n G F U - center))
  rw [hr]
  exact centered_identity n G χ hcχ hχ hinv β c F
    (ClosedHalfSmearing.halfObservable_continuous n G a plane ψ hcψ 1 f) center

/-- Strict positivity is equivalent to a genuine nonconstant response. This
does not supply that response estimate, either at finite cutoff or uniformly. -/
theorem smeared_positive_iff (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (β c a : ℝ) (plane : Plane) (ψ : G → ℂ) (hcψ : Continuous ψ)
    (f : CorrelationTest 1) (hs : ClosedHalfSmearing.Supported n a plane 1 f) :
    0 < (ReflectedWilsonRenormalization.reflectedForm G (2*n) a plane ψ χ β c f f).re ↔
      ¬ ∀ᵐ b ∂marginal n G χ β c,
        response n G χ β c (ClosedHalfSmearing.halfObservable n G a plane ψ 1 f) b =
          ∫ U, WilsonSmearedObservable.observable G (2*n) a plane ψ 1 f U
            ∂wilsonLaw (2*n) G χ β c := by
  rw [smeared_centered_identity n G χ hcχ hχ hinv β c a plane ψ hcψ f hs,
    Complex.ofReal_re]
  letI := marginal_probability n G χ hcχ β c
  have hi : Integrable (fun b => ‖response n G χ β c
      (ClosedHalfSmearing.halfObservable n G a plane ψ 1 f) b -
      ∫ U, WilsonSmearedObservable.observable G (2*n) a plane ψ 1 f U
        ∂wilsonLaw (2*n) G χ β c‖^2) (marginal n G χ β c) :=
    ((response_continuous n G χ hcχ β c _
    (ClosedHalfSmearing.halfObservable_continuous n G a plane ψ hcψ 1 f)).sub
      continuous_const).norm.pow 2 |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hz := integral_eq_zero_iff_of_nonneg (fun b => sq_nonneg
    (‖response n G χ β c (ClosedHalfSmearing.halfObservable n G a plane ψ 1 f) b -
      ∫ U, WilsonSmearedObservable.observable G (2*n) a plane ψ 1 f U
        ∂wilsonLaw (2*n) G χ β c‖)) hi
  simp only [Filter.EventuallyEq, Pi.zero_apply, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at hz
  rw [← hz]
  exact lt_iff_le_and_ne |>.trans (by
    have h : 0 ≤ ∫ b, ‖response n G χ β c
        (ClosedHalfSmearing.halfObservable n G a plane ψ 1 f) b -
        ∫ U, WilsonSmearedObservable.observable G (2*n) a plane ψ 1 f U
          ∂wilsonLaw (2*n) G χ β c‖^2 ∂marginal n G χ β c :=
      integral_nonneg (fun b => sq_nonneg _)
    simp [h, ne_comm])

end
end UnifiedTheory.Clay.YangMills.WilsonBoundaryResponse
