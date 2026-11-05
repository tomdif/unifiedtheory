/- Applying the explicit kernel Hilbert construction to the normalized positive
Wilson Gram subsequence. The result is a Hilbert realization of countably many
limiting loop observables, not an OS reconstruction or continuum local QFT. -/
import UnifiedTheory.Clay.YangMills.KernelHilbertCompletion
import UnifiedTheory.Clay.YangMills.WilsonGramCompactness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonKernelHilbert
noncomputable section
open CountableCorrelationCompactness WilsonGramCompactness
open PositiveKernelForm KernelHilbertCompletion

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {ι : Type*} [Countable ι]
variable (period : ℕ → ℕ) [∀ k, NeZero (period k)] (beta offset : ℕ → ℝ)
  (χ : G → ℂ) (order : ι → ℕ)
  (base : ∀ k i, Fin (order i) → Quiver.Symmetrify (PeriodicLattice4.Vertex (period k)))
  (loops : ∀ k i j, Quiver.Path (base k i j) (base k i j))

/-- The existing Wilson subsequence has an actual complete Hilbert realization
with dense canonical span and normalized vacuum, constructed from its kernel. -/
theorem exists_normalized_wilson_hilbert_kernel (hχ : Continuous χ)
    (unitIndex : ι) (hunit : order unitIndex = 0) :
    ∃ (B : ℝ) (K : PositiveKernel ι) (phi : ℕ → ℕ), 0 < B ∧ StrictMono phi ∧
      CoordinateConvergence (gramCorrelation G period beta offset χ order base loops ∘ phi)
        K.value ∧
      (∀ i, ‖K.value i‖ ≤ B ^ (order i.1 + order i.2)) ∧
      K.value (unitIndex, unitIndex) = 1 ∧
      CompleteSpace (Hilbert K) ∧
      (∀ i j, inner ℂ (canonical K i) (canonical K j) = K.value (i, j)) ∧
      Dense (Submodule.span ℂ (Set.range (canonical K)) : Set (Hilbert K)) ∧
      ‖vacuum K unitIndex‖ = 1 := by
  obtain ⟨B, w, phi, hB, hphi, hc, hb, hp, hn⟩ :=
    exists_normalized_positive_wilson_gram_limit G period beta offset χ order base loops
      hχ unitIndex hunit
  let K : PositiveKernel ι := ⟨w, hp⟩
  exact ⟨B, K, phi, hB, hphi, hc, hb, hn, inferInstance,
    canonical_inner K, dense_canonical_span K, vacuum_norm K unitIndex hn⟩

end
end UnifiedTheory.Clay.YangMills.WilsonKernelHilbert
