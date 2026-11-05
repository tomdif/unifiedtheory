/- Source calculus for the actual interacting periodic Wilson probability law.
The insertion is an actual cell-smeared observable. The range estimate is
volume-independent, but scales with the physical field normalization Z/a^4;
it is not a uniform continuum estimate or a positive reflected witness. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsSource
import UnifiedTheory.Clay.YangMills.BoundedSourceTube
import UnifiedTheory.Clay.YangMills.WilsonBoundaryResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSourceResponse
noncomputable section
open MeasureTheory PeriodicLattice4 ContinuumControl
open scoped NNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (N : ℕ) [NeZero N]

def sourcePartition (χ : G → ℂ) (β c : ℝ)
    (F : RegulatedGauge.Configuration (Vertex N) G → ℝ) (t : ℝ) : ℝ :=
  CompactGibbsSource.partition (wilsonLaw N G χ β c) (fun _ => 0) F t

def sourceExpectation (χ : G → ℂ) (β c : ℝ)
    (F H : RegulatedGauge.Configuration (Vertex N) G → ℝ) (t : ℝ) : ℝ :=
  CompactGibbsSource.expectation (wilsonLaw N G χ β c) (fun _ => 0) F H t

omit [SecondCountableTopology G] in
theorem sourcePartition_formula (χ : G → ℂ) (β c : ℝ)
    (F : RegulatedGauge.Configuration (Vertex N) G → ℝ) (t : ℝ) :
    sourcePartition G N χ β c F t = ∫ U, Real.exp (t*F U) ∂wilsonLaw N G χ β c := by
  simp only [sourcePartition, CompactGibbsSource.partition, CompactGibbsSource.weight,
    CompactGibbsSource.action, zero_sub, neg_neg]

theorem sourcePartition_zero (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (F : RegulatedGauge.Configuration (Vertex N) G → ℝ) :
    sourcePartition G N χ β c F 0 = 1 := by
  letI := wilsonLaw_probability N G χ hχ β c
  simp [sourcePartition_formula]

theorem sourceExpectation_zero (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (F H : RegulatedGauge.Configuration (Vertex N) G → ℝ) (hF : Continuous F) :
    sourceExpectation G N χ β c F H 0 = ∫ U, H U ∂wilsonLaw N G χ β c := by
  letI := wilsonLaw_probability N G χ hχ β c
  rw [sourceExpectation, CompactGibbsSource.expectation_eq_quotient _ _ _ _
    continuous_const hF]
  simp [CompactGibbsSource.moment, CompactGibbsSource.partition,
    CompactGibbsSource.weight, CompactGibbsSource.action]

/-- The logarithmic derivative of the genuine interacting Wilson source
partition is its sourced expectation, at every real source value. -/
theorem log_sourcePartition_hasDerivAt (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (F : RegulatedGauge.Configuration (Vertex N) G → ℝ) (hF : Continuous F) (t : ℝ) :
    HasDerivAt (fun s => Real.log (sourcePartition G N χ β c F s))
      (sourceExpectation G N χ β c F F t) t := by
  letI := wilsonLaw_probability N G χ hχ β c
  exact CompactGibbsSource.log_partition_hasDerivAt _ _ _ continuous_const hF t

/-- A source for F probes the actual connected Wilson correlation with H. -/
theorem sourceExpectation_hasDerivAt_zero (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (F H : RegulatedGauge.Configuration (Vertex N) G → ℝ)
    (hF : Continuous F) (hH : Continuous H) :
    HasDerivAt (sourceExpectation G N χ β c F H)
      ((∫ U, H U*F U ∂wilsonLaw N G χ β c) -
       (∫ U, H U ∂wilsonLaw N G χ β c)*(∫ U, F U ∂wilsonLaw N G χ β c)) 0 := by
  letI := wilsonLaw_probability N G χ hχ β c
  have h := CompactGibbsSource.expectation_hasDerivAt (wilsonLaw N G χ β c)
    (fun _ => 0) F H continuous_const hF hH 0
  change HasDerivAt (sourceExpectation G N χ β c F H)
    (sourceExpectation G N χ β c F (fun U => H U*F U) 0 -
      sourceExpectation G N χ β c F H 0 * sourceExpectation G N χ β c F F 0) 0 at h
  simpa only [sourceExpectation_zero G N χ hχ β c F _ hF] using h

theorem log_sourcePartition_second (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (F : RegulatedGauge.Configuration (Vertex N) G → ℝ) (hF : Continuous F) :
    deriv (fun t => deriv (fun s => Real.log (sourcePartition G N χ β c F s)) t) 0 =
      (∫ U, F U*F U ∂wilsonLaw N G χ β c) - (∫ U, F U ∂wilsonLaw N G χ β c)^2 := by
  have he : (fun t => deriv (fun s => Real.log (sourcePartition G N χ β c F s)) t) =
      sourceExpectation G N χ β c F F := by
    funext t
    exact (log_sourcePartition_hasDerivAt G N χ hχ β c F hF t).deriv
  rw [he]
  simpa only [pow_two] using (sourceExpectation_hasDerivAt_zero G N χ hχ β c F F hF hF).deriv

/-- This range-only upper bound is valid for every coupling and volume. It
does not force any nonzero separated covariance. -/
theorem source_curvature_bounds (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (F : RegulatedGauge.Configuration (Vertex N) G → ℝ) (hF : Continuous F)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ U, |F U| ≤ M) :
    0 ≤ deriv (fun t => deriv (fun s => Real.log (sourcePartition G N χ β c F s)) t) 0 ∧
    deriv (fun t => deriv (fun s => Real.log (sourcePartition G N χ β c F s)) t) 0 ≤ M^2 := by
  letI := wilsonLaw_probability N G χ hχ β c
  rw [log_sourcePartition_second G N χ hχ β c F hF]
  constructor
  · have h := CompactGibbsSource.covariance_self_nonneg (wilsonLaw N G χ β c)
      (fun _ => 0) F F continuous_const hF hF 0
    change 0 ≤ sourceExpectation G N χ β c F (fun U => F U*F U) 0 -
      sourceExpectation G N χ β c F F 0 * sourceExpectation G N χ β c F F 0 at h
    simpa only [sourceExpectation_zero G N χ hχ β c F _ hF, pow_two] using h
  · have hi : Integrable (fun U => F U*F U) (wilsonLaw N G χ β c) :=
      (hF.mul hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hupper : (∫ U, F U*F U ∂wilsonLaw N G χ β c) ≤ M^2 := by
      calc
        _ ≤ ∫ _, M^2 ∂wilsonLaw N G χ β c := by
          apply integral_mono hi (integrable_const _)
          intro U
          have hs := (sq_le_sq₀ (abs_nonneg (F U)) hM).mpr (hbound U)
          nlinarith [sq_abs (F U)]
        _ = _ := by simp
    exact (sub_le_self _ (sq_nonneg _)).trans hupper

def realSmear (a : ℝ) (plane : Plane) (ψ : G → ℂ) (f : CorrelationTest 1)
    (U : RegulatedGauge.Configuration (Vertex N) G) : ℝ :=
  (WilsonSmearedObservable.observable G N a plane ψ 1 f U).re

theorem realSmear_continuous (a : ℝ) (plane : Plane) (ψ : G → ℂ)
    (hψ : Continuous ψ) (f : CorrelationTest 1) :
    Continuous (realSmear G N a plane ψ f) :=
  Complex.continuous_re.comp (WilsonSmearedObservable.observable_continuous G N a plane ψ hψ 1 f)

theorem realSmear_bound (a : ℝ) (plane : Plane) (ψ : G → ℂ)
    (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B) (f : CorrelationTest 1)
    (U : RegulatedGauge.Configuration (Vertex N) G) :
    |realSmear G N a plane ψ f U| ≤ BoundedKernelDistribution.boundSeminorm volume B f := by
  exact (Complex.abs_re_le_norm _).trans (by
    simpa only [pow_one] using WilsonSmearedObservable.observable_bound G N a plane ψ B hB 1 f U)

def physicalSmear (a Z : ℝ) (plane : Plane) (ψ : G → ℂ) (f : CorrelationTest 1)
    (U : RegulatedGauge.Configuration (Vertex N) G) : ℝ :=
  (Z / a^4) * realSmear G N a plane ψ f U

theorem physicalSmear_continuous (a Z : ℝ) (plane : Plane) (ψ : G → ℂ)
    (hψ : Continuous ψ) (f : CorrelationTest 1) :
    Continuous (physicalSmear G N a Z plane ψ f) :=
  continuous_const.mul (realSmear_continuous G N a plane ψ hψ f)

theorem physicalSmear_bound (a Z : ℝ) (plane : Plane) (ψ : G → ℂ)
    (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B) (f : CorrelationTest 1)
    (U : RegulatedGauge.Configuration (Vertex N) G) :
    |physicalSmear G N a Z plane ψ f U| ≤
      |Z/a^4| * BoundedKernelDistribution.boundSeminorm volume B f := by
  rw [physicalSmear, abs_mul]
  exact mul_le_mul_of_nonneg_left (realSmear_bound G N a plane ψ B hB f U) (abs_nonneg _)

/-- Actual Wilson source nonvanishing. The displayed strip width retains
the cutoff-dependent normalization explicitly. -/
theorem physical_source_ne_zero (χ : G → ℂ) (hχ : Continuous χ) (β c a Z : ℝ)
    (plane : Plane) (ψ : G → ℂ) (hψ : Continuous ψ)
    (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B) (f : CorrelationTest 1) (z : ℂ)
    (hz : |z.im| * (|Z/a^4| * BoundedKernelDistribution.boundSeminorm volume B f) < Real.pi/2) :
    (∫ U, Complex.exp (z * (physicalSmear G N a Z plane ψ f U : ℂ))
      ∂wilsonLaw N G χ β c) ≠ 0 := by
  letI := wilsonLaw_probability N G χ hχ β c
  exact BoundedSourceTube.partition_ne_zero _ _
    (physicalSmear_continuous G N a Z plane ψ hψ f) _
    (physicalSmear_bound G N a Z plane ψ B hB f) z hz

theorem physical_source_curvature_bounds (χ : G → ℂ) (hχ : Continuous χ) (β c a Z : ℝ)
    (plane : Plane) (ψ : G → ℂ) (hψ : Continuous ψ)
    (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B) (f : CorrelationTest 1) :
    0 ≤ deriv (fun t => deriv (fun s => Real.log
      (sourcePartition G N χ β c (physicalSmear G N a Z plane ψ f) s)) t) 0 ∧
    deriv (fun t => deriv (fun s => Real.log
      (sourcePartition G N χ β c (physicalSmear G N a Z plane ψ f) s)) t) 0 ≤
      (|Z/a^4| * BoundedKernelDistribution.boundSeminorm volume B f)^2 :=
  source_curvature_bounds G N χ hχ β c _
    (physicalSmear_continuous G N a Z plane ψ hψ f) _
    (mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
    (physicalSmear_bound G N a Z plane ψ B hB f)

def halfSourcePartition (χ : G → ℂ) (β c : ℝ)
    (F : PeriodicHalfSplit.BoundaryConfiguration N G ×
      PeriodicHalfSplit.HalfConfiguration N G → ℝ)
    (b : PeriodicHalfSplit.BoundaryConfiguration N G) (t : ℝ) : ℝ :=
  CompactGibbsSource.partition (PeriodicHalfSplit.halfMeasure N G)
    (fun x => PeriodicSiteReflection.halfAction N G χ β c (b,x)) (fun x => F (b,x)) t

def halfSourceSlope (χ : G → ℂ) (β c : ℝ)
    (F : PeriodicHalfSplit.BoundaryConfiguration N G ×
      PeriodicHalfSplit.HalfConfiguration N G → ℝ)
    (b : PeriodicHalfSplit.BoundaryConfiguration N G) : ℝ :=
  deriv (fun t => Real.log (halfSourcePartition G N χ β c F b t)) 0

/-- The source derivative is the conditional mean under the actual Wilson
half action. The positive integration measure is source-independent. -/
theorem halfSourceSlope_eq_integral (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (F : PeriodicHalfSplit.BoundaryConfiguration N G ×
      PeriodicHalfSplit.HalfConfiguration N G → ℝ) (hF : Continuous F)
    (b : PeriodicHalfSplit.BoundaryConfiguration N G) :
    halfSourceSlope G N χ β c F b =
      ∫ x, F (b,x) ∂CompactGibbsContinuity.law (PeriodicHalfSplit.halfMeasure N G)
        (fun x => PeriodicSiteReflection.halfAction N G χ β c (b,x)) := by
  have hA := (PeriodicSiteReflection.halfAction_continuous N G χ hχ β c).comp
    (continuous_const.prodMk continuous_id : Continuous
      (fun x : PeriodicHalfSplit.HalfConfiguration N G => (b,x)))
  have hf := hF.comp (continuous_const.prodMk continuous_id : Continuous
    (fun x : PeriodicHalfSplit.HalfConfiguration N G => (b,x)))
  have hd := CompactGibbsSource.log_partition_hasDerivAt
    (PeriodicHalfSplit.halfMeasure N G) _ _ hA hf 0
  have ha0 : CompactGibbsSource.action
      (fun x => PeriodicSiteReflection.halfAction N G χ β c (b,x)) (fun x => F (b,x)) 0 =
      (fun x => PeriodicSiteReflection.halfAction N G χ β c (b,x)) := by
    funext x
    simp only [CompactGibbsSource.action, zero_mul, sub_zero]
  simpa only [halfSourceSlope, halfSourcePartition, CompactGibbsSource.expectation,
    Function.comp_def, ha0] using hd.deriv

theorem halfSourceSlope_eq_response (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (F : PeriodicHalfSplit.BoundaryConfiguration N G ×
      PeriodicHalfSplit.HalfConfiguration N G → ℝ) (hF : Continuous F)
    (b : PeriodicHalfSplit.BoundaryConfiguration N G) :
    halfSourceSlope G N χ β c F b =
      (WilsonBoundaryResponse.response N G χ β c (fun z => (F z : ℂ)) b).re := by
  rw [halfSourceSlope_eq_integral G N χ hχ β c F hF b,
    WilsonBoundaryResponse.response, NormalizedBoundaryResponse.response_eq_half_expectation
      _ _ (PeriodicSiteReflection.halfAction_continuous N G χ hχ β c)]
  rw [integral_complex_ofReal]
  rfl

/-- A pointwise marked-insertion remainder bounds the conditional source
derivative with no inverse partition factor. Constructing an ultraviolet-
uniform remainder for the renormalized RG insertion remains a separate task. -/
theorem halfSourceSlope_centered_bound (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (F : PeriodicHalfSplit.BoundaryConfiguration N G ×
      PeriodicHalfSplit.HalfConfiguration N G → ℝ) (hF : Continuous F)
    (q : PeriodicHalfSplit.BoundaryConfiguration N G → ℝ) (M : ℝ)
    (hbound : ∀ b x, |F (b,x) - q b| ≤ M)
    (b : PeriodicHalfSplit.BoundaryConfiguration N G) :
    |halfSourceSlope G N χ β c F b - q b| ≤ M := by
  let A := fun x => PeriodicSiteReflection.halfAction N G χ β c (b,x)
  have hA : Continuous A := (PeriodicSiteReflection.halfAction_continuous N G χ hχ β c).comp
    (continuous_const.prodMk continuous_id)
  let ν := CompactGibbsContinuity.law (PeriodicHalfSplit.halfMeasure N G) A
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability _ A hA
  have hf : Continuous (fun x : PeriodicHalfSplit.HalfConfiguration N G => F (b,x)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  rw [halfSourceSlope_eq_integral G N χ hχ β c F hF b]
  change |(∫ x, F (b,x) ∂ν) - q b| ≤ M
  have he : (∫ x, F (b,x) - q b ∂ν) = (∫ x, F (b,x) ∂ν) - q b := by
    rw [integral_sub (hf.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (integrable_const _)]
    simp
  rw [← he, ← Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le (f := fun x => F (b,x) - q b)
    (integrable_const M : Integrable (fun _ => M) ν)
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound b x))
  simpa using hb

end
end UnifiedTheory.Clay.YangMills.WilsonSourceResponse
