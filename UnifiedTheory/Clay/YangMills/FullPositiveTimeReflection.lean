/- Reflection positivity extends from bounded time slabs to every Schwartz
polynomial supported at nonnegative times. Constructed compact cutoffs and the
actual bare L1 bound transfer the mixed complex Gram forms to the same limit. -/
import UnifiedTheory.Clay.YangMills.PositiveTimeCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FullPositiveTimeReflection
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 PeriodicCellSampling
open WilsonReflectedTensor PositiveTimeCutoff CountableCorrelationCompactness
open PositiveKernelForm
open scoped Topology NNReal

/-- Labels impose no upper time bound and no compact spatial support. -/
def Label := Σ m : ℕ, {f : CorrelationTest m // PositiveTimeCutoff.Supported m f}

def kernel (W : Hierarchy) (plane : Plane) (p : Label × Label) : ℂ :=
  W.correlation (p.1.1+p.2.1)
    (reflectedTensor p.1.1 p.2.1 0 plane p.1.2.1 p.2.2.1)

def Positive (W : Hierarchy) (plane : Plane) : Prop :=
  GramPositive (fun i j => (i,j)) (kernel W plane)

def positiveKernel (W : Hierarchy) (plane : Plane) (hp : Positive W plane) :
    PositiveKernel Label := ⟨kernel W plane, hp⟩

theorem correlation_cutoff_tendsto (W : Hierarchy) (plane : Plane) (B : ℝ≥0)
    (hb : OSPositiveTimeKernel.Bounded W B) (m n : ℕ)
    (f : CorrelationTest m) (g : CorrelationTest n) :
    Tendsto (fun R => W.correlation (m+n)
      (reflectedTensor m n 0 plane (cutoff m R f) (cutoff n R g))) atTop
        (𝓝 (W.correlation (m+n) (reflectedTensor m n 0 plane f g))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun R => norm_nonneg _)
    (fun R => show ‖W.correlation (m+n)
      (reflectedTensor m n 0 plane (cutoff m R f) (cutoff n R g)) -
      W.correlation (m+n) (reflectedTensor m n 0 plane f g)‖ ≤
      (B : ℝ)^(m+n) * BoundedKernelDistribution.l1Seminorm volume
        (reflectedTensor m n 0 plane (cutoff m R f) (cutoff n R g) -
          reflectedTensor m n 0 plane f g) from by
      simpa only [map_sub, BoundedKernelDistribution.boundSeminorm,
        Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, NNReal.coe_pow] using
        hb (m+n) (reflectedTensor m n 0 plane (cutoff m R f) (cutoff n R g) -
          reflectedTensor m n 0 plane f g))
  simpa only [mul_zero] using
    (reflected_cutoff_l1_tendsto m n plane f g).const_mul ((B : ℝ)^(m+n))

/-- All finite complex polynomial forms, with arbitrary mixed orders and
unrestricted positive-time Schwartz support, inherit reflection positivity. -/
theorem finite_form_positive (W : Hierarchy) (plane : Plane) (B : ℝ≥0)
    (hb : OSPositiveTimeKernel.Bounded W B) (hp : OSPositiveTimeKernel.Positive W plane)
    (l : ℕ) (order : Fin l → ℕ) (test : (i : Fin l) → CorrelationTest (order i))
    (coeff : Fin l → ℂ) (hs : ∀ i, PositiveTimeCutoff.Supported (order i) (test i)) :
    0 ≤ (∑ i, ∑ j, star (coeff i) * coeff j *
      W.correlation (order i + order j)
        (reflectedTensor (order i) (order j) 0 plane (test i) (test j))).re ∧
    (∑ i, ∑ j, star (coeff i) * coeff j *
      W.correlation (order i + order j)
        (reflectedTensor (order i) (order j) 0 plane (test i) (test j))).im = 0 := by
  let c (R : ℕ) (p : Fin l × Fin l) := W.correlation (order p.1+order p.2)
    (reflectedTensor (order p.1) (order p.2) 0 plane
      (cutoff (order p.1) R (test p.1)) (cutoff (order p.2) R (test p.2)))
  let w (p : Fin l × Fin l) := W.correlation (order p.1+order p.2)
    (reflectedTensor (order p.1) (order p.2) 0 plane (test p.1) (test p.2))
  have hc : CoordinateConvergence c w := fun p =>
    correlation_cutoff_tendsto W plane B hb (order p.1) (order p.2) (test p.1) (test p.2)
  have hpos (R : ℕ) : 0 ≤ (gramValue (fun i j => (i,j)) (c R) l id coeff).re ∧
      (gramValue (fun i j => (i,j)) (c R) l id coeff).im = 0 := by
    exact (hp l (fun i => ⟨order i, cutoff (order i) R (test i),
      cutoff_supported (order i) R (test i) (hs i)⟩) coeff).symm
  have ht := gramValue_tendsto c w hc (fun i j => (i,j)) l id coeff
  change 0 ≤ (gramValue (fun i j => (i,j)) w l id coeff).re ∧
    (gramValue (fun i j => (i,j)) w l id coeff).im = 0
  constructor
  · exact ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp ht)
      (Eventually.of_forall (fun R => (hpos R).1))
  · exact tendsto_nhds_unique (Complex.continuous_im.tendsto _ |>.comp ht)
      (tendsto_const_nhds.congr' (Eventually.of_forall (fun R => (hpos R).2.symm)))

theorem positive_of_bounded_positive (W : Hierarchy) (plane : Plane) (B : ℝ≥0)
    (hb : OSPositiveTimeKernel.Bounded W B) (hp : OSPositiveTimeKernel.Positive W plane) :
    Positive W plane := by
  intro l index coeff
  exact (finite_form_positive W plane B hb hp l (fun i => (index i).1)
    (fun i => (index i).2.1) coeff (fun i => (index i).2.2)).symm

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The extension applies to the same actual Wilson weak limit. The positivity
and bound required above are derived here from the actual lattice hierarchy. -/
theorem actual_limit_positive
    (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hlarge : Tendsto (fun k => (period k : ℝ) * a k) atTop atTop)
    (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ z, (χ z⁻¹).re = (χ z).re)
    (B : ℝ≥0) (hB : ∀ z, ‖χ z‖ ≤ B) (beta offset : ℕ → ℝ)
    (W : Hierarchy)
    (hW : WeakConvergence (fun k => realHierarchy G (2 * period k) (a k) plane χ hcχ B hB
      (beta k) (offset k)) W) : Positive W plane := by
  have hb : OSPositiveTimeKernel.Bounded W B := by
    intro m f
    apply le_of_tendsto (hW m f |>.norm)
    exact Eventually.of_forall (fun k => WilsonCellHierarchy.hierarchy_uniform_bound G
      (2 * period k) (a k) plane (CellReflectionCovariance.realPartCharacter G χ)
      (realPart_continuous G χ hcχ) B (realPart_bound G χ B hB) (beta k) (offset k) m f)
  apply positive_of_bounded_positive W plane B hb
  apply OSPositiveTimeKernel.positive_of_finite_form W plane
  intro l order test coeff R hs
  apply WilsonHierarchyReflectionPositivity.finite_form_positive G period a
    (fun k => ne_of_gt (ha k)) ha0 plane χ hcχ hχ hinv B hB beta offset W hW
    l order test coeff
  intro i
  exact PositiveCellSupport.eventually_supported period a ha hlarge plane
    (order i) (test i) (R i) (hs i)

end
end UnifiedTheory.Clay.YangMills.FullPositiveTimeReflection
