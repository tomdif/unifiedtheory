/- The same regulator subsequence carries both the actual bare Schwartz
hierarchy limit and a nontrivial ordinary Wilson Gram Hilbert kernel.
The unsmeared Gram state is not identified with a continuum smeared state. -/
import UnifiedTheory.Clay.YangMills.WilsonJointCompactness
import UnifiedTheory.Clay.YangMills.WilsonNontrivialHilbert

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonJointNontrivial
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 WilsonCrossingKernel
open UnitaryCharacterObservables UnitaryUniformVariance WilsonNontrivialHilbert
open ProbabilityGramCompactness CountableCorrelationCompactness
open PositiveKernelForm KernelHilbertCompletion
open scoped NNReal ENNReal

variable {d G : Type*} [Fintype d] [DecidableEq d] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def unitaryBareHierarchy (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ) (beta offset : ℝ) : Hierarchy :=
  WilsonCellHierarchy.hierarchy G N a plane (unitaryCharacter ρ)
    (unitaryCharacter_continuous ρ hρ) (Fintype.card d)
    (fun g => unitary_trace_bound (ρ g)) beta offset

/-- The quantitative nontriviality floor and the all-orders distributional
limit coexist on exactly the same strict subsequence. No equality between
these two limiting objects, nor OS positivity of their identification, is claimed. -/
theorem exists_joint_nontrivial_limit
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ) (g : G) (hg : ρ g ≠ 1)
    (period : ℕ → ℕ) [∀ k, NeZero (period k)] [∀ k, Fact (1 < period k)]
    (a : ℕ → ℝ) (plane : Plane) (beta offset : ℕ → ℝ)
    (betaMax : ℝ) (hbeta : ∀ k, |beta k| ≤ betaMax)
    (x : ∀ k, Vertex (period k)) (μ ν : Fin 4) (hμν : μ ≠ ν) :
    ∃ (W : Hierarchy) (K : PositiveKernel Bool) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => unitaryBareHierarchy (period (phi k)) (a (phi k)) plane ρ hρ
          (beta (phi k)) (offset (phi k))) W ∧
      CoordinateConvergence
        (fun k => kernel (wilsonLaw (period (phi k)) G (unitaryCharacter ρ)
          (beta (phi k)) (offset (phi k)))
          (plaquetteFamily (period (phi k)) ρ (x (phi k)) μ ν)) K.value ∧
      (∀ m f, ‖W.correlation m f‖ ≤ BoundedKernelDistribution.boundSeminorm volume
        ((Fintype.card d : ℝ≥0) ^ m) f) ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ y, f y) ∧
      K.value (false, false) = 1 ∧ 0 < varianceFloor ρ betaMax ∧
      varianceFloor ρ betaMax ≤ connectedVariance K false true ∧
      canonical K true ∉ Submodule.span ℂ ({vacuum K false} : Set (Hilbert K)) := by
  obtain ⟨W, K, phi, hphi, hW, hc, hbW, hnW, _, hnK, hfloor⟩ :=
    WilsonJointCompactness.exists_hierarchy_gram_limit G period a plane (unitaryCharacter ρ)
      (unitaryCharacter_continuous ρ hρ) (Fintype.card d)
      (fun g => unitary_trace_bound (ρ g)) beta offset
      (fun k => plaquetteFamily (period k) ρ (x k) μ ν)
      (fun k b => plaquetteFamily_continuous (period k) ρ hρ (x k) μ ν b)
      (fun _ => max 1 (Fintype.card d : ℝ))
      (fun _ => le_trans zero_le_one (le_max_left _ _))
      (fun k b U => plaquetteFamily_bound (period k) ρ (x k) μ ν b U)
      false (fun _ _ => rfl)
  have hpos := varianceFloor_pos ρ hρ g hg betaMax
  have hv : varianceFloor ρ betaMax ≤ connectedVariance K false true :=
    hfloor true (varianceFloor ρ betaMax) (fun k =>
      bounded_coupling_plaquette_variance (period k) ρ hρ betaMax
        (beta k) (offset k) (hbeta k) (x k) μ ν hμν)
  exact ⟨W, K, phi, hphi, hW, hc, hbW, hnW, hnK, hpos, hv,
    canonical_not_vacuum_span K false true hnK (hpos.trans_le hv)⟩

end
end UnifiedTheory.Clay.YangMills.WilsonJointNontrivial
