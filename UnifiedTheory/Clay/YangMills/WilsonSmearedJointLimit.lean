/- The ordinary Gram Hilbert vacuum matrix elements of selected countably
many actual smeared Wilson observables equal the corresponding limiting
Schwartz hierarchy values. This is an exact identity across a joint limit,
not an OS reconstruction or a nontriviality assertion for smeared fields. -/
import UnifiedTheory.Clay.YangMills.WilsonJointCompactness
import UnifiedTheory.Clay.YangMills.WilsonSmearedObservable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSmearedJointLimit
noncomputable section
open Filter MeasureTheory ContinuumControl PeriodicLattice4
open ProbabilityGramCompactness CountableCorrelationCompactness
open PositiveKernelForm KernelHilbertCompletion
open scoped Topology NNReal ENNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {ι : Type*}

def family (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (order : ι → ℕ) (test : (i : ι) → CorrelationTest (order i)) :
    Option ι → RegulatedGauge.Configuration (Vertex N) G → ℂ
  | none => fun _ => 1
  | some i => WilsonSmearedObservable.observable G N a plane χ (order i) (test i)

def bound (B : ℝ≥0) (order : ι → ℕ) (test : (i : ι) → CorrelationTest (order i)) :
    Option ι → ℝ
  | none => 1
  | some i => BoundedKernelDistribution.boundSeminorm volume (B ^ order i) (test i)

theorem bound_nonneg (B : ℝ≥0) (order : ι → ℕ)
    (test : (i : ι) → CorrelationTest (order i)) (i : Option ι) :
    0 ≤ bound B order test i := by
  cases i with
  | none => exact zero_le_one
  | some i => exact apply_nonneg (BoundedKernelDistribution.boundSeminorm volume (B ^ order i)) _

theorem family_continuous (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hχ : Continuous χ) (order : ι → ℕ) (test : (i : ι) → CorrelationTest (order i))
    (i : Option ι) : Continuous (family G N a plane χ order test i) := by
  cases i with
  | none => exact continuous_const
  | some i => exact WilsonSmearedObservable.observable_continuous G N a plane χ hχ _ _

theorem family_bound (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B)
    (order : ι → ℕ) (test : (i : ι) → CorrelationTest (order i))
    (i : Option ι) (U : RegulatedGauge.Configuration (Vertex N) G) :
    ‖family G N a plane χ order test i U‖ ≤ bound B order test i := by
  cases i with
  | none => simp only [family, bound, norm_one, le_refl]
  | some i => exact WilsonSmearedObservable.observable_bound G N a plane χ B hB _ _ U

/-- The finite-cutoff unit/selected-test Gram entry is exactly the hierarchy
value, using the actual cell-smearing dictionary. -/
theorem unit_cross_eq_hierarchy (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hχ : Continuous χ) (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (beta offset : ℝ)
    (order : ι → ℕ) (test : (i : ι) → CorrelationTest (order i)) (i : ι) :
    kernel (wilsonLaw N G χ beta offset) (family G N a plane χ order test) (none, some i) =
      (WilsonCellHierarchy.hierarchy G N a plane χ hχ B hB beta offset).correlation
        (order i) (test i) := by
  simp only [kernel, family, star_one, one_mul]
  exact WilsonSmearedObservable.expectation_eq_hierarchy G N a plane χ hχ B hB beta offset _ _

/-- One actual complete ordinary Gram Hilbert space realizes the limiting
vacuum matrix elements of every selected countable Schwartz test, on the same
subsequence as the entire all-orders hierarchy. -/
theorem exists_joint_smeared_hilbert_limit [Countable ι]
    (period : ℕ → ℕ) [∀ k, NeZero (period k)] (a : ℕ → ℝ)
    (plane : Plane) (χ : G → ℂ) (hχ : Continuous χ)
    (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (beta offset : ℕ → ℝ)
    (order : ι → ℕ) (test : (i : ι) → CorrelationTest (order i)) :
    ∃ (W : Hierarchy) (K : PositiveKernel (Option ι)) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => WilsonCellHierarchy.hierarchy G (period (phi k)) (a (phi k))
          plane χ hχ B hB (beta (phi k)) (offset (phi k))) W ∧
      CoordinateConvergence
        (fun k => kernel (wilsonLaw (period (phi k)) G χ (beta (phi k)) (offset (phi k)))
          (family G (period (phi k)) (a (phi k)) plane χ order test)) K.value ∧
      (∀ m f, ‖W.correlation m f‖ ≤
        BoundedKernelDistribution.boundSeminorm volume (B ^ m) f) ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧
      (∀ p, ‖K.value p‖ ≤ bound B order test p.1 * bound B order test p.2) ∧
      K.value (none, none) = 1 ∧ ‖vacuum K none‖ = 1 ∧
      ∀ i, inner ℂ (vacuum K none) (canonical K (some i)) =
        W.correlation (order i) (test i) := by
  obtain ⟨W, K, phi, hphi, hW, hc, hbW, hnW, hbK, hnK, _⟩ :=
    WilsonJointCompactness.exists_hierarchy_gram_limit G period a plane χ hχ B hB beta offset
      (fun k => family G (period k) (a k) plane χ order test)
      (fun k i => family_continuous G (period k) (a k) plane χ hχ order test i)
      (bound B order test) (bound_nonneg B order test)
      (fun k i U => family_bound G (period k) (a k) plane χ B hB order test i U)
      none (fun _ _ => rfl)
  refine ⟨W, K, phi, hphi, hW, hc, hbW, hnW, hbK, hnK, vacuum_norm K none hnK, ?_⟩
  intro i
  change inner ℂ (canonical K none) (canonical K (some i)) = _
  rw [canonical_inner]
  apply tendsto_nhds_unique (hc (none, some i))
  simpa only [unit_cross_eq_hierarchy G _ _ _ _ hχ B hB] using hW (order i) (test i)

end
end UnifiedTheory.Clay.YangMills.WilsonSmearedJointLimit
