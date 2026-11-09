/- One actual normalized Wilson subsequence carries all four Euclidean
translations, unrestricted positive-time reflection positivity, and the
nonnegative self-adjoint maximal generator of its transported OS evolution.
This packages a bare scalar candidate; renormalized Yang--Mills identification,
nontriviality, and a positive excitation gap are not asserted. -/
import UnifiedTheory.Clay.YangMills.TranslationOSCandidate
import UnifiedTheory.Clay.YangMills.FullPositiveTimeHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FullOSHamiltonianCandidate
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 LocalFields
open ExplicitLatticeScales WilsonReflectedTensor CellSpacetimeTranslation SchwartzTranslations
open KernelHilbertCompletion
open scoped NNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The hierarchy, positivity, evolution, and maximal generator are all
constructed on one actual Wilson subsequence. None is an input premise. -/
theorem exists_candidate (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (beta offset : ℕ → ℝ) :
    ∃ (W : Hierarchy) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => realHierarchy G (2 * halfPeriod (phi k)) (spacing (phi k))
          plane χ hcχ B hB (beta (phi k)) (offset (phi k))) W ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧
      OSPositiveTimeKernel.Stationary W ∧
      (∀ (m : ℕ) (v : Spacetime) (f : CorrelationTest m),
        W.correlation m (translationCLM (displacement m v) f) = W.correlation m f) ∧
      ∃ (hb : OSPositiveTimeKernel.Bounded W B)
        (hp : OSPositiveTimeKernel.Positive W plane)
        (hfull : FullPositiveTimeReflection.Positive W plane)
        (D : OSScalarDynamics.Evolution W plane hp),
        IsSelfAdjoint (FullPositiveTimeHamiltonian.hamiltonian W plane hp hfull B hb D) ∧
        Dense ((FullPositiveTimeHamiltonian.hamiltonian W plane hp hfull B hb D).domain :
          Set (FullPositiveTimeHamiltonian.State W plane hfull)) ∧
        (∀ x : (FullPositiveTimeHamiltonian.hamiltonian W plane hp hfull B hb D).domain,
          0 ≤ (inner ℂ (x : FullPositiveTimeHamiltonian.State W plane hfull)
            (FullPositiveTimeHamiltonian.hamiltonian W plane hp hfull B hb D x)).re) ∧
        (∀ (t : ℝ≥0) (i : FullPositiveTimeReflection.Label),
          FullPositiveTimeDynamics.operator W plane hp hfull B hb D t
            (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) i) =
          canonical (FullPositiveTimeReflection.positiveKernel W plane hfull)
            (FullPositiveTimeDynamics.shift t i)) ∧
        ∀ v w : FullPositiveTimeHamiltonian.State W plane hfull,
          HasDerivWithinAt (fun t : ℝ =>
            FullPositiveTimeDynamics.operator W plane hp hfull B hb D t.toNNReal v)
              w (Set.Ici 0) 0 ↔
            (v,-w) ∈ (FullPositiveTimeHamiltonian.hamiltonian W plane hp hfull B hb D).graph := by
  obtain ⟨W,phi,hphi,hW,hn,hb,ht,h4,hp,⟨D⟩⟩ :=
    TranslationOSCandidate.exists_candidate G plane χ hcχ hχ hinv B hB beta offset
  letI : ∀ k, NeZero (halfPeriod (phi k)) := fun k => halfPeriod_ne_zero (phi k)
  have hfull : FullPositiveTimeReflection.Positive W plane :=
    FullPositiveTimeReflection.actual_limit_positive G
      (fun k => halfPeriod (phi k)) (fun k => spacing (phi k))
      (fun k => spacing_pos (phi k)) (spacing_to_zero.comp hphi.tendsto_atTop)
      (half_extent_to_infinity.comp hphi.tendsto_atTop)
      plane χ hcχ hχ hinv B hB (beta ∘ phi) (offset ∘ phi) W hW
  exact ⟨W,phi,hphi,hW,hn,ht,h4,hb,hp,hfull,D,
    FullPositiveTimeHamiltonian.selfAdjoint W plane hp hfull B hb D,
    FullPositiveTimeHamiltonian.dense_domain W plane hp hfull B hb D,
    FullPositiveTimeHamiltonian.nonnegative W plane hp hfull B hb D,
    FullPositiveTimeDynamics.operator_canonical W plane hp hfull B hb D,
    FullPositiveTimeHamiltonian.derivative_iff_graph W plane hp hfull B hb D⟩

end
end UnifiedTheory.Clay.YangMills.FullOSHamiltonianCandidate
