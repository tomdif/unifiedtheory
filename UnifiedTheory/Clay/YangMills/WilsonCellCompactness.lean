/- A common all-orders distributional subsequence for the actual bounded,
unrenormalized cell-smeared Wilson hierarchy. This is compactness, not
nontriviality, reflection positivity, or an interacting continuum theory. -/
import UnifiedTheory.Clay.YangMills.WilsonCellHierarchy
import UnifiedTheory.Clay.YangMills.L1HierarchyCompactness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCellCompactness
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4
open scoped Topology NNReal ENNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Every regulator sequence admits one strict subsequence converging at
every correlation order on every Schwartz test. Normalization survives.
The norm bound is the actual Wilson character bound, uniform in the lattice
period, spacing, and coupling. No supplied dense test family is required. -/
theorem exists_hierarchy_limit
    (N : ℕ → ℕ) [∀ k, NeZero (N k)] (a : ℕ → ℝ)
    (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (β c : ℕ → ℝ) :
    ∃ (W : Hierarchy) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => WilsonCellHierarchy.hierarchy G (N (phi k)) (a (phi k))
          plane χ hcχ B hB (β (phi k)) (c (phi k))) W ∧
      (∀ m f, ‖W.correlation m f‖ ≤
        BoundedKernelDistribution.boundSeminorm volume (B ^ m) f) ∧
      ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x := by
  obtain ⟨W, phi, hphi, hW, hbW⟩ :=
    L1HierarchyCompactness.exists_bounded_kernel_hierarchy_limit
      (fun m k => WilsonCellHierarchy.kernel G (N k) (a k) plane χ (β k) (c k) m)
      (fun m k => WilsonCellHierarchy.kernel_measurable G (N k) (a k) plane χ (β k) (c k) m)
      (fun m => B ^ m)
      (fun m k x => by
        simpa only [NNReal.coe_pow] using
          WilsonCellHierarchy.kernel_bound G (N k) (a k) plane χ hcχ B hB (β k) (c k) m x)
  have hc : WeakConvergence
      (fun k => WilsonCellHierarchy.hierarchy G (N (phi k)) (a (phi k))
        plane χ hcχ B hB (β (phi k)) (c (phi k))) W := hW
  refine ⟨W, phi, hphi, hc, hbW, fun f => ?_⟩
  apply tendsto_nhds_unique (hc 0 f)
  simpa only [WilsonCellHierarchy.hierarchy_order_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ x, f x) atTop (𝓝 (∫ x, f x)))

end
end UnifiedTheory.Clay.YangMills.WilsonCellCompactness
