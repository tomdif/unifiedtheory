/- Every real physical time translation preserves a weak limit of the actual
bare cell Wilson hierarchy as positive spacing tends to zero. Integer cell
translations are proved symmetries; their errors vanish in the full Schwartz
topology. No time generator or Hamiltonian is constructed here. -/
import UnifiedTheory.Clay.YangMills.CellTranslationCovariance
import UnifiedTheory.Clay.YangMills.AffineCellReflection
import UnifiedTheory.Clay.YangMills.MovingTestLimit
import UnifiedTheory.Clay.YangMills.WilsonCellCompactness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ContinuumTimeTranslation
noncomputable section
open Filter MeasureTheory ContinuumControl PeriodicLattice4
open CellTranslationCovariance SchwartzTranslations
open scoped Topology NNReal

def cellTime (a t : ℝ) : ℝ := a * (⌊t / a⌋ : ℤ)

theorem cellTime_error (a : ℝ) (ha : 0 < a) (t : ℝ) : |cellTime a t - t| ≤ a := by
  have hlo := mul_le_mul_of_nonneg_left (Int.floor_le (t / a)) ha.le
  have hhi := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (t / a)) ha
  rw [mul_div_cancel₀ t (ne_of_gt ha)] at hlo hhi
  change |a * (⌊t / a⌋ : ℤ) - t| ≤ a
  rw [abs_le]
  constructor <;> nlinarith

theorem cellTime_tendsto (a : ℕ → ℝ) (hpos : ∀ k, 0 < a k)
    (ha : Tendsto a atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun k => cellTime (a k) t) atTop (𝓝 t) := by
  have hb (k : ℕ) : ‖cellTime (a k) t - t‖ ≤ a k := by
    simpa only [Real.norm_eq_abs] using cellTime_error (a k) (hpos k) t
  have hd : Tendsto (fun k => cellTime (a k) t - t) atTop (𝓝 0) :=
    squeeze_zero_norm hb ha
  have h := hd.add (tendsto_const_nhds (x := t))
  simpa only [sub_add_cancel, zero_add] using h

theorem timeVector_continuous (m : ℕ) : Continuous (timeVector m) :=
  AffineCellReflection.offsetVector_continuous m

/-- The discrete exact lattice translations approximate any real displacement
in every Schwartz test seminorm, simultaneously at all insertion positions. -/
theorem translated_tests_tendsto (m : ℕ) (f : CorrelationTest m)
    (a : ℕ → ℝ) (hpos : ∀ k, 0 < a k) (ha : Tendsto a atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun k => translationCLM (timeVector m (cellTime (a k) t)) f) atTop
      (𝓝 (translationCLM (timeVector m t) f)) :=
  ((continuous_translation_tests f).tendsto (timeVector m t)).comp
    (((timeVector_continuous m).tendsto t).comp (cellTime_tendsto a hpos ha t))

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Actual limiting Wilson correlations inherit all real time translations.
Neither finite translation invariance nor continuity of moving tests is assumed. -/
theorem hierarchy_time_translation
    (N : ℕ → ℕ) [∀ k, NeZero (N k)] (a : ℕ → ℝ)
    (hpos : ∀ k, 0 < a k) (ha : Tendsto a atTop (𝓝 0))
    (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ) (B : ℝ≥0)
    (hB : ∀ g, ‖χ g‖ ≤ B) (beta offset : ℕ → ℝ) (W : Hierarchy)
    (hW : WeakConvergence
      (fun k => WilsonCellHierarchy.hierarchy G (N k) (a k) plane χ hcχ B hB
        (beta k) (offset k)) W)
    (m : ℕ) (t : ℝ) (f : CorrelationTest m) :
    W.correlation m (translationCLM (timeVector m t) f) = W.correlation m f := by
  let S : ℕ → Hierarchy := fun k =>
    WilsonCellHierarchy.hierarchy G (N k) (a k) plane χ hcχ B hB (beta k) (offset k)
  have hm := MovingTestLimit.hierarchy_moving_limit S W hW
    (fun j => BoundedKernelDistribution.boundSeminorm volume (B ^ j))
    (fun j => BoundedKernelDistribution.boundSeminorm_continuous volume (B ^ j))
    (fun k j g => WilsonCellHierarchy.hierarchy_uniform_bound
      G (N k) (a k) plane χ hcχ B hB (beta k) (offset k) j g)
    m (translationCLM (timeVector m t) f)
    (fun k => translationCLM (timeVector m (cellTime (a k) t)) f)
    (translated_tests_tendsto m f a hpos ha t)
  have he (k : ℕ) : (S k).correlation m
      (translationCLM (timeVector m (cellTime (a k) t)) f) = (S k).correlation m f :=
    hierarchy_translation G (N k) χ hcχ B hB (beta k) (offset k) m (a k)
      (ne_of_gt (hpos k)) plane ⌊t / a k⌋ f
  simp_rw [he] at hm
  exact tendsto_nhds_unique hm (hW m f)

/-- A common actual Wilson subsequential limit exists at all Schwartz orders,
is normalized, has the uniform bare bound, and is invariant under every real
physical time translation. Nontriviality and dynamics do not follow here. -/
theorem exists_time_translation_invariant_limit
    (N : ℕ → ℕ) [∀ k, NeZero (N k)] (a : ℕ → ℝ)
    (hpos : ∀ k, 0 < a k) (ha : Tendsto a atTop (𝓝 0))
    (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ) (B : ℝ≥0)
    (hB : ∀ g, ‖χ g‖ ≤ B) (beta offset : ℕ → ℝ) :
    ∃ (W : Hierarchy) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => WilsonCellHierarchy.hierarchy G (N (phi k)) (a (phi k)) plane χ hcχ B hB
          (beta (phi k)) (offset (phi k))) W ∧
      (∀ m f, ‖W.correlation m f‖ ≤ BoundedKernelDistribution.boundSeminorm volume (B ^ m) f) ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧
      ∀ (m : ℕ) (t : ℝ) (f : CorrelationTest m),
        W.correlation m (translationCLM (timeVector m t) f) = W.correlation m f := by
  obtain ⟨W, phi, hphi, hW, hb, hn⟩ :=
    WilsonCellCompactness.exists_hierarchy_limit G N a plane χ hcχ B hB beta offset
  letI : ∀ k, NeZero ((N ∘ phi) k) := fun k => inferInstanceAs (NeZero (N (phi k)))
  refine ⟨W, phi, hphi, hW, hb, hn, fun m t f => ?_⟩
  exact hierarchy_time_translation G (N ∘ phi) (a ∘ phi) (fun k => hpos (phi k))
    (ha.comp hphi.tendsto_atTop) plane χ hcχ B hB (beta ∘ phi) (offset ∘ phi) W hW m t f

end
end UnifiedTheory.Clay.YangMills.ContinuumTimeTranslation
