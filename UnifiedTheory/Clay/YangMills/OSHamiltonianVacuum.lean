/- The normalized order-zero vacuum belongs to the actual Laplace Hamiltonian
domain and has zero energy. No uniqueness or positive excitation is assumed. -/
import UnifiedTheory.Clay.YangMills.OSLaplaceHamiltonian
import UnifiedTheory.Clay.YangMills.OSVacuumSector
import UnifiedTheory.Clay.YangMills.SpectralGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSHamiltonianVacuum
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 OSPositiveTimeKernel
open OSScalarDynamics OSVacuumSector OSLaplaceResolvent OSLaplaceHamiltonian

variable {W : Hierarchy} {plane : Plane} {hp : Positive W plane} (D : Evolution W plane hp)

theorem resolvent_vacuum : resolvent D (vacuum W plane hp) = vacuum W plane hp := by
  rw [resolvent_apply]
  simp only [integrand, evolution_vacuum, integral_smul_const, integral_exp_neg_Ioi_zero, one_smul]

def vacuumPoint : (hamiltonian D).domain :=
  ⟨vacuum W plane hp,⟨vacuum W plane hp,resolvent_vacuum D⟩⟩

@[simp] theorem vacuumPoint_value : (vacuumPoint D : State (hp := hp)) = vacuum W plane hp := rfl

@[simp] theorem vacuum_energy : hamiltonian D (vacuumPoint D) = 0 := by
  have he : vacuumPoint D = rangePoint D (vacuum W plane hp) := by
    apply Subtype.ext
    exact (resolvent_vacuum D).symm
  rw [he, apply_range, resolvent_vacuum, sub_self]

theorem vacuum_graph : (vacuum W plane hp,0) ∈ (hamiltonian D).graph :=
  (hamiltonian D).mem_graph_iff.mpr ⟨vacuumPoint D,rfl,vacuum_energy D⟩

/-- The precise existing spectral interface detects the normalized vacuum
at zero; no positive spectral-gap interval is claimed. -/
theorem zero_not_in_resolvent
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) :
    ¬ SpectralGap.InRealResolvent (hamiltonian D) 0 :=
  SpectralGap.vacuum_not_in_resolvent (hamiltonian D) (vacuum W plane hp)
    (vacuum_norm W plane hp hn) (vacuum_graph D)

/-- The constructed Laplace inverse is a bounded two-sided witness at -1
in the repository's actual unbounded spectral interface. -/
def negativeOneResolvent : SpectralGap.ResolventWitness (hamiltonian D) (-1) where
  inverse := resolvent D
  right_inverse y := by
    apply (hamiltonian D).mem_graph_iff.mpr
    refine ⟨rangePoint D y,rfl,?_⟩
    rw [apply_range]
    simp [sub_eq_add_neg]
  left_inverse x := by
    simpa using resolvent_left D x

end
end UnifiedTheory.Clay.YangMills.OSHamiltonianVacuum
