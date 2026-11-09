/- The actual order-zero vacuum for full Schwartz time evolution is fixed,
belongs to the maximal Hamiltonian domain, and has zero energy. These are
vacuum statements, with no vacuum-uniqueness or excitation-gap assertion. -/
import UnifiedTheory.Clay.YangMills.FullSchwartzHamiltonian
import UnifiedTheory.Clay.YangMills.RenormalizedFullOSLimit
import UnifiedTheory.Clay.YangMills.OSHamiltonianVacuum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FullSchwartzVacuum
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 KernelHilbertCompletion
open FullSchwartzHamiltonian RenormalizedFullOSLimit
open scoped NNReal

variable (W : Hierarchy) (plane : Plane)
  (hp : OSPositiveTimeKernel.Positive W plane)
  (hfull : FullPositiveTimeReflection.Positive W plane)
  (D : OSScalarDynamics.Evolution W plane hp)

theorem equivalence_vacuum :
    FullSchwartzHilbert.equivalence W plane hp hfull (OSVacuumSector.vacuum W plane hp) =
      fullVacuum W plane hfull :=
  embedding_vacuum W plane hp hfull

theorem inverse_vacuum :
    (FullSchwartzHilbert.equivalence W plane hp hfull).symm (fullVacuum W plane hfull) =
      OSVacuumSector.vacuum W plane hp := by
  rw [← equivalence_vacuum W plane hp hfull, LinearIsometryEquiv.symm_apply_apply]

theorem evolution_vacuum (t : ℝ≥0) :
    FullSchwartzDynamics.operator W plane hp hfull D t (fullVacuum W plane hfull) =
      fullVacuum W plane hfull := by
  rw [FullSchwartzDynamics.operator_apply, inverse_vacuum, OSVacuumSector.evolution_vacuum,
    equivalence_vacuum]

theorem resolvent_vacuum :
    resolvent W plane hp hfull D (fullVacuum W plane hfull) = fullVacuum W plane hfull := by
  rw [resolvent_apply, inverse_vacuum, OSHamiltonianVacuum.resolvent_vacuum, equivalence_vacuum]

def vacuumPoint : (hamiltonian W plane hp hfull D).domain :=
  ⟨fullVacuum W plane hfull, ⟨fullVacuum W plane hfull,
    resolvent_vacuum W plane hp hfull D⟩⟩

@[simp] theorem vacuumPoint_value :
    (vacuumPoint W plane hp hfull D : State W plane hfull) = fullVacuum W plane hfull := rfl

@[simp] theorem vacuum_energy :
    hamiltonian W plane hp hfull D (vacuumPoint W plane hp hfull D) = 0 := by
  have he : vacuumPoint W plane hp hfull D =
      rangePoint W plane hp hfull D (fullVacuum W plane hfull) := by
    apply Subtype.ext
    exact (resolvent_vacuum W plane hp hfull D).symm
  rw [he, apply_range, resolvent_vacuum, sub_self]

theorem vacuum_graph :
    (fullVacuum W plane hfull,0) ∈ (hamiltonian W plane hp hfull D).graph :=
  (hamiltonian W plane hp hfull D).mem_graph_iff.mpr
    ⟨vacuumPoint W plane hp hfull D,rfl,vacuum_energy W plane hp hfull D⟩

theorem zero_not_in_resolvent
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) :
    ¬ SpectralGap.InRealResolvent (hamiltonian W plane hp hfull D) 0 :=
  SpectralGap.vacuum_not_in_resolvent (hamiltonian W plane hp hfull D)
    (fullVacuum W plane hfull) (fullVacuum_norm W plane hp hfull hn)
    (vacuum_graph W plane hp hfull D)

def negativeOneResolvent : SpectralGap.ResolventWitness (hamiltonian W plane hp hfull D) (-1) where
  inverse := resolvent W plane hp hfull D
  right_inverse y := by
    apply (hamiltonian W plane hp hfull D).mem_graph_iff.mpr
    refine ⟨rangePoint W plane hp hfull D y,rfl,?_⟩
    rw [apply_range]
    simp [sub_eq_add_neg]
  left_inverse x := by
    have he := (graph_iff W plane hp hfull D x
      (hamiltonian W plane hp hfull D x)).mp
      ((hamiltonian W plane hp hfull D).mem_graph_iff.mpr ⟨x,rfl,rfl⟩)
    simpa using he

end
end UnifiedTheory.Clay.YangMills.FullSchwartzVacuum
