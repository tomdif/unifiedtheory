/- Actual reflected Wilson kernels of countably selected closed-half smeared
tests and the bare hierarchy converge on one strict regulator subsequence.
Their completed positive-kernel Hilbert vacuum matrix elements are exactly
the limiting hierarchy values. No time semigroup or continuum OS reconstruction
is asserted by this site-reflection result. -/
import UnifiedTheory.Clay.YangMills.WilsonSmearedJointLimit
import UnifiedTheory.Clay.YangMills.ClosedHalfSmearing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonReflectedJointLimit
noncomputable section
open Filter MeasureTheory ContinuumControl PeriodicLattice4 PeriodicHalfSplit
open PeriodicTimeReflection PeriodicPlaquetteReflection
open CountableCorrelationCompactness PositiveKernelForm KernelHilbertCompletion
open scoped Topology NNReal ENNReal

variable (n : ℕ) [NeZero n]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {ι : Type*}

theorem integral_reflection (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (beta offset : ℝ) (f : RegulatedGauge.Configuration (Vertex (2 * n)) G → ℂ) :
    (∫ U, f (reflectConfiguration (2*n) G U) ∂wilsonLaw (2*n) G χ beta offset) =
      ∫ U, f U ∂wilsonLaw (2*n) G χ beta offset := by
  have hR := wilsonLaw_preserves_reflection (2*n) G χ hcχ hχ hinv beta offset
  exact hR.integral_comp
    (MeasurableEquiv.ofInvolutive _ (reflectConfiguration_involutive (2*n) G)
      hR.measurable).measurableEmbedding f

theorem half_mean_eq_positive (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (beta offset : ℝ) (f : BoundaryConfiguration n G × HalfConfiguration n G → ℂ) :
    (∫ U, PeriodicSiteReflection.observable n G f U ∂wilsonLaw (2*n) G χ beta offset) =
      ∫ U, ReflectedWilsonKernel.positiveObservable n G f U
        ∂wilsonLaw (2*n) G χ beta offset := by
  simp_rw [ReflectedWilsonKernel.positiveObservable_eq_reflected]
  exact (integral_reflection n G χ hcχ hχ hinv beta offset _).symm

def family (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (order : ι → ℕ) (test : (i : ι) → CorrelationTest (order i)) :
    Option ι → BoundaryConfiguration n G × HalfConfiguration n G → ℂ
  | none => fun _ => 1
  | some i => ClosedHalfSmearing.halfObservable n G a plane χ (order i) (test i)

theorem family_continuous (a : ℝ) (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (order : ι → ℕ) (test : (i : ι) → CorrelationTest (order i)) (i : Option ι) :
    Continuous (family n G a plane χ order test i) := by
  cases i with
  | none => exact continuous_const
  | some i => exact ClosedHalfSmearing.halfObservable_continuous n G a plane χ hcχ _ _

theorem family_bound (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B)
    (order : ι → ℕ) (test : (i : ι) → CorrelationTest (order i))
    (i : Option ι) (z : BoundaryConfiguration n G × HalfConfiguration n G) :
    ‖family n G a plane χ order test i z‖ ≤ WilsonSmearedJointLimit.bound B order test i := by
  cases i with
  | none => simp only [family, WilsonSmearedJointLimit.bound, norm_one, le_refl]
  | some i => exact WilsonSmearedObservable.observable_bound G (2*n) a plane χ B hB _ _ _

/-- Reflection invariance and the actual half-support dictionary identify the
reflected unit cross with the same bare hierarchy, without an assumed bridge. -/
theorem unit_cross_eq_hierarchy (a : ℝ) (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (beta offset : ℝ)
    (order : ι → ℕ) (test : (i : ι) → CorrelationTest (order i)) (i : ι)
    (hs : ClosedHalfSmearing.Supported n a plane (order i) (test i)) :
    ReflectedWilsonKernel.kernel n G χ beta offset (family n G a plane χ order test)
      (none, some i) =
      (WilsonCellHierarchy.hierarchy G (2*n) a plane χ hcχ B hB beta offset).correlation
        (order i) (test i) := by
  calc
    _ = ∫ U, PeriodicSiteReflection.observable n G
        (ClosedHalfSmearing.halfObservable n G a plane χ (order i) (test i)) U
        ∂wilsonLaw (2*n) G χ beta offset := by
      simp only [ReflectedWilsonKernel.kernel, family, PeriodicSiteReflection.observable,
        BoundaryReflectionGluing.halfObservable, star_one, one_mul]
    _ = ∫ U, ReflectedWilsonKernel.positiveObservable n G
        (ClosedHalfSmearing.halfObservable n G a plane χ (order i) (test i)) U
        ∂wilsonLaw (2*n) G χ beta offset :=
      half_mean_eq_positive n G χ hcχ hχ hinv beta offset _
    _ = ∫ U, WilsonSmearedObservable.observable G (2*n) a plane χ (order i) (test i) U
        ∂wilsonLaw (2*n) G χ beta offset := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun U =>
        (ClosedHalfSmearing.half_identification n G a plane χ (order i) (test i) hs U).symm)
    _ = _ := WilsonSmearedObservable.expectation_eq_hierarchy G (2*n) a plane χ hcχ
      B hB beta offset _ _

/-- Under actual half support, the full reflected smeared-pair expectation is
the half-coordinate kernel. Reflection invariance handles the choice of half. -/
theorem reflected_pair_eq_half_kernel (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hcχ : Continuous χ) (hχ : RegulatedGauge.ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (beta offset : ℝ)
    (order : ι → ℕ) (test : (i : ι) → CorrelationTest (order i)) (i j : ι)
    (hi : ClosedHalfSmearing.Supported n a plane (order i) (test i))
    (hj : ClosedHalfSmearing.Supported n a plane (order j) (test j)) :
    (∫ U, star (WilsonSmearedObservable.observable G (2*n) a plane χ (order i) (test i)
      (reflectConfiguration (2*n) G U)) *
      WilsonSmearedObservable.observable G (2*n) a plane χ (order j) (test j) U
        ∂wilsonLaw (2*n) G χ beta offset) =
      ReflectedWilsonKernel.kernel n G χ beta offset (family n G a plane χ order test)
        (some i, some j) := by
  simp_rw [ClosedHalfSmearing.half_identification n G a plane χ (order i) (test i) hi,
    ClosedHalfSmearing.half_identification n G a plane χ (order j) (test j) hj,
    ReflectedWilsonKernel.positiveObservable_eq_reflected]
  exact integral_reflection n G χ hcχ hχ hinv beta offset
    (fun U => star (PeriodicSiteReflection.observable n G
      (ClosedHalfSmearing.halfObservable n G a plane χ (order i) (test i))
      (reflectConfiguration (2*n) G U)) * PeriodicSiteReflection.observable n G
        (ClosedHalfSmearing.halfObservable n G a plane χ (order j) (test j)) U)

/-- Actual site-reflected Gram positivity, Hilbert vacuum normalization, and
all selected vacuum-to-test matrix elements survive on the same subsequence
as the entire Schwartz hierarchy. Each selected test has eventual half support;
actual full smeared reflected-pair expectations converge to the same kernel. -/
theorem exists_joint_reflected_hilbert_limit [Countable ι]
    (period : ℕ → ℕ) [∀ k, NeZero (period k)] (a : ℕ → ℝ)
    (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (beta offset : ℕ → ℝ)
    (order : ι → ℕ) (test : (i : ι) → CorrelationTest (order i))
    (hs : ∀ i, ∀ᶠ k in atTop,
      ClosedHalfSmearing.Supported (period k) (a k) plane (order i) (test i)) :
    ∃ (W : Hierarchy) (K : PositiveKernel (Option ι)) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => WilsonCellHierarchy.hierarchy G (2 * period (phi k)) (a (phi k))
          plane χ hcχ B hB (beta (phi k)) (offset (phi k))) W ∧
      CoordinateConvergence
        (fun k => ReflectedWilsonKernel.kernel (period (phi k)) G χ
          (beta (phi k)) (offset (phi k))
          (family (period (phi k)) G (a (phi k)) plane χ order test)) K.value ∧
      (∀ m f, ‖W.correlation m f‖ ≤
        BoundedKernelDistribution.boundSeminorm volume (B ^ m) f) ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧
      (∀ p, ‖K.value p‖ ≤ WilsonSmearedJointLimit.bound B order test p.1 *
        WilsonSmearedJointLimit.bound B order test p.2) ∧
      K.value (none, none) = 1 ∧ ‖vacuum K none‖ = 1 ∧
      (∀ i, inner ℂ (vacuum K none) (canonical K (some i)) =
        W.correlation (order i) (test i)) ∧
      ∀ i j, Tendsto (fun k => ∫ U,
        star (WilsonSmearedObservable.observable G (2 * period (phi k)) (a (phi k))
          plane χ (order i) (test i) (reflectConfiguration (2 * period (phi k)) G U)) *
        WilsonSmearedObservable.observable G (2 * period (phi k)) (a (phi k))
          plane χ (order j) (test j) U
          ∂wilsonLaw (2 * period (phi k)) G χ (beta (phi k)) (offset (phi k)))
        atTop (𝓝 (K.value (some i, some j))) := by
  let c (k : ℕ) := ReflectedWilsonKernel.kernel (period k) G χ (beta k) (offset k)
    (family (period k) G (a k) plane χ order test)
  let C := WilsonSmearedJointLimit.bound B order test
  have hC := WilsonSmearedJointLimit.bound_nonneg B order test
  obtain ⟨W, w, phi, hphi, hW, hc, hbW, hnW, hbw⟩ :=
    WilsonJointCompactness.exists_hierarchy_coordinate_limit G (fun k => 2 * period k) a
      plane χ hcχ B hB beta offset c (fun p => C p.1 * C p.2)
      (fun k p => ReflectedWilsonKernel.kernel_bound (period k) G χ hcχ (beta k) (offset k)
        (family (period k) G (a k) plane χ order test) C hC
        (family_bound (period k) G (a k) plane χ B hB order test) p)
  have hp : GramPositive (fun i j => (i, j)) w :=
    gram_positive_survives _ w hc _ (fun k => ReflectedWilsonKernel.kernel_positive
      (period (phi k)) G χ hcχ hχ hinv (beta (phi k)) (offset (phi k))
      (family (period (phi k)) G (a (phi k)) plane χ order test)
      (family_continuous (period (phi k)) G (a (phi k)) plane χ hcχ order test))
  let K : PositiveKernel (Option ι) := ⟨w, hp⟩
  have hn : K.value (none, none) = 1 := normalization_survives _ w hc (none, none)
    (fun k => ReflectedWilsonKernel.kernel_normalized (period (phi k)) G χ hcχ
      (beta (phi k)) (offset (phi k))
      (family (period (phi k)) G (a (phi k)) plane χ order test) none (fun _ => rfl))
  have hsphi (i : ι) : ∀ᶠ k in atTop,
      ClosedHalfSmearing.Supported (period (phi k)) (a (phi k)) plane (order i) (test i) :=
    hphi.tendsto_atTop.eventually (hs i)
  refine ⟨W, K, phi, hphi, hW, hc, hbW, hnW, hbw, hn, vacuum_norm K none hn, ?_, ?_⟩
  · intro i
    change inner ℂ (canonical K none) (canonical K (some i)) = _
    rw [canonical_inner]
    apply tendsto_nhds_unique (hc (none, some i))
    exact (tendsto_congr' ((hsphi i).mono (fun k hk =>
      unit_cross_eq_hierarchy (period (phi k)) G (a (phi k)) plane χ hcχ hχ hinv
        B hB (beta (phi k)) (offset (phi k)) order test i hk))).2
      (hW (order i) (test i))
  · intro i j
    exact (tendsto_congr' (((hsphi i).and (hsphi j)).mono (fun k hk =>
      reflected_pair_eq_half_kernel (period (phi k)) G (a (phi k)) plane χ hcχ hχ hinv
        (beta (phi k)) (offset (phi k)) order test i j hk.1 hk.2))).2
      (hc (some i, some j))

end
end UnifiedTheory.Clay.YangMills.WilsonReflectedJointLimit
