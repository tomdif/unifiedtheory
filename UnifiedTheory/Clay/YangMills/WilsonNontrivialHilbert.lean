/- An actual non-vacuum Hilbert state from bounded-coupling Wilson laws.
The labels are the constant observable and a plaquette. The uniform positive
connected floor is proved for these laws, not assumed. This ordinary Gram
reconstruction does not supply an OS semigroup or a continuum local field. -/
import UnifiedTheory.Clay.YangMills.ConnectedGramLimit
import UnifiedTheory.Clay.YangMills.UnitaryUniformVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonNontrivialHilbert
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonMomentBounds WilsonCrossingKernel
open UnitaryCharacterObservables UnitaryUniformVariance ProbabilityGramCompactness
open ConnectedGramLimit CountableCorrelationCompactness PositiveKernelForm KernelHilbertCompletion

variable {d G : Type*} [Fintype d] [DecidableEq d] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def plaquetteFamily (n : ℕ) [NeZero n] (ρ : G →* Matrix.unitaryGroup d ℂ)
    (x : Vertex n) (μ ν : Fin 4) (b : Bool) (U : Configuration (Vertex n) G) : ℂ :=
  if b then loopObservable (Vertex n) G (unitaryCharacter ρ) (plaquette n x μ ν) U else 1

theorem plaquetteFamily_continuous (n : ℕ) [NeZero n]
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (x : Vertex n) (μ ν : Fin 4) (b : Bool) :
    Continuous (plaquetteFamily n ρ x μ ν b) := by
  cases b
  · exact continuous_const
  · exact loopObservable_continuous (Vertex n) G (unitaryCharacter ρ)
      (unitaryCharacter_continuous ρ hρ) _

theorem plaquetteFamily_bound (n : ℕ) [NeZero n]
    (ρ : G →* Matrix.unitaryGroup d ℂ) (x : Vertex n) (μ ν : Fin 4)
    (b : Bool) (U : Configuration (Vertex n) G) :
    ‖plaquetteFamily n ρ x μ ν b U‖ ≤ max 1 (Fintype.card d : ℝ) := by
  cases b
  · simpa only [plaquetteFamily, Bool.false_eq_true, ↓reduceIte, norm_one] using
      (le_max_left (1 : ℝ) (Fintype.card d : ℝ))
  · exact (loopObservable_bound (Vertex n) G (unitaryCharacter ρ)
      (Fintype.card d : ℝ) (fun g => unitary_trace_bound (ρ g))
      (plaquette n x μ ν) U).trans (le_max_right _ _)

/-- Every sequence of periods and bounded couplings has a positive Gram
subsequence whose completed Hilbert space contains a state outside the vacuum
line. The positive quantitative floor is independent of every period. -/
theorem exists_bounded_coupling_nontrivial_kernel
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ) (g : G) (hg : ρ g ≠ 1)
    (period : ℕ → ℕ) [∀ k, NeZero (period k)] [∀ k, Fact (1 < period k)]
    (beta offset : ℕ → ℝ) (betaMax : ℝ) (hbeta : ∀ k, |beta k| ≤ betaMax)
    (x : ∀ k, Vertex (period k)) (μ ν : Fin 4) (hμν : μ ≠ ν) :
    ∃ (K : PositiveKernel Bool) (phi : ℕ → ℕ), StrictMono phi ∧
      CoordinateConvergence
        (fun k => kernel (wilsonLaw (period (phi k)) G (unitaryCharacter ρ)
          (beta (phi k)) (offset (phi k)))
          (plaquetteFamily (period (phi k)) ρ (x (phi k)) μ ν)) K.value ∧
      K.value (false, false) = 1 ∧
      0 < varianceFloor ρ betaMax ∧
      varianceFloor ρ betaMax ≤ connectedVariance K false true ∧
      canonical K true ∉ Submodule.span ℂ ({vacuum K false} : Set (Hilbert K)) := by
  letI : ∀ k, IsProbabilityMeasure
      (wilsonLaw (period k) G (unitaryCharacter ρ) (beta k) (offset k)) := fun k =>
    wilsonLaw_probability (period k) G (unitaryCharacter ρ)
      (unitaryCharacter_continuous ρ hρ) (beta k) (offset k)
  have hpos := varianceFloor_pos ρ hρ g hg betaMax
  obtain ⟨K, phi, hphi, hc, _, hn, hv, hnontrivial⟩ :=
    exists_nontrivial_hilbert_kernel
      (fun k => wilsonLaw (period k) G (unitaryCharacter ρ) (beta k) (offset k))
      (fun k => plaquetteFamily (period k) ρ (x k) μ ν)
      (fun k b => plaquetteFamily_continuous (period k) ρ hρ (x k) μ ν b)
      (fun _ => max 1 (Fintype.card d : ℝ))
      (fun _ => le_trans zero_le_one (le_max_left _ _))
      (fun k b U => plaquetteFamily_bound (period k) ρ (x k) μ ν b U)
      false true (fun _ _ => rfl) (varianceFloor ρ betaMax) hpos
      (fun k => bounded_coupling_plaquette_variance (period k) ρ hρ betaMax
        (beta k) (offset k) (hbeta k) (x k) μ ν hμν)
  exact ⟨K, phi, hphi, hc, hn, hpos, hv, hnontrivial⟩

end
end UnifiedTheory.Clay.YangMills.WilsonNontrivialHilbert
