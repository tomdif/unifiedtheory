/- One actual vanishing-mesh Wilson limit carries the constructed nonnegative
self-adjoint generator and its normalized zero-energy vacuum. A renormalized
nontrivial Yang--Mills identification and positive excitation gap remain open. -/
import UnifiedTheory.Clay.YangMills.OSGeneratorDomain
import UnifiedTheory.Clay.YangMills.OSHamiltonianVacuum
import UnifiedTheory.Clay.YangMills.TranslationOSCandidate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSHamiltonianCandidate
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 LocalFields
open ExplicitLatticeScales WilsonReflectedTensor CellSpacetimeTranslation SchwartzTranslations
open OSPositiveTimeKernel OSScalarDynamics OSLaplaceHamiltonian OSVacuumSector
open scoped NNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- No limiting hierarchy, time evolution, Hamiltonian, inverse law, or
spectral gap is postulated: the hierarchy and generator are constructed from
the actual Wilson sequence. The spectral statement supplied here is at -1. -/
theorem exists_candidate (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (beta offset : ℕ → ℝ) :
    ∃ (W : Hierarchy) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => realHierarchy G (2 * halfPeriod (phi k)) (spacing (phi k))
          plane χ hcχ B hB (beta (phi k)) (offset (phi k))) W ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧
      Bounded W B ∧ Stationary W ∧
      (∀ (m : ℕ) (v : Spacetime) (f : CorrelationTest m),
        W.correlation m (translationCLM (displacement m v) f) = W.correlation m f) ∧
      ∃ (hp : Positive W plane) (D : Evolution W plane hp),
        IsSelfAdjoint (hamiltonian D) ∧ (hamiltonian D).IsClosed ∧
        Dense ((hamiltonian D).domain : Set (OSLaplaceResolvent.State (hp := hp))) ∧
        (∀ x : (hamiltonian D).domain,
          0 ≤ (inner ℂ (x : OSLaplaceResolvent.State (hp := hp)) (hamiltonian D x)).re) ∧
        ‖vacuum W plane hp‖ = 1 ∧ (vacuum W plane hp,0) ∈ (hamiltonian D).graph ∧
        SpectralGap.InRealResolvent (hamiltonian D) (-1) ∧
        ∀ v w : OSLaplaceResolvent.State (hp := hp),
          HasDerivWithinAt (fun t : ℝ => D.operator t.toNNReal v) w (Set.Ici 0) 0 ↔
            (v,-w) ∈ (hamiltonian D).graph := by
  obtain ⟨W,phi,hphi,hW,hn,hb,ht,h4,hp,⟨D⟩⟩ :=
    TranslationOSCandidate.exists_candidate G plane χ hcχ hχ hinv B hB beta offset
  exact ⟨W,phi,hphi,hW,hn,hb,ht,h4,hp,D,selfAdjoint D,closed D,dense_domain D,
    nonnegative D,vacuum_norm W plane hp hn,OSHamiltonianVacuum.vacuum_graph D,
    ⟨OSHamiltonianVacuum.negativeOneResolvent D⟩,OSGeneratorDomain.derivative_iff_graph D⟩

end
end UnifiedTheory.Clay.YangMills.OSHamiltonianCandidate
