/- A nonzero reflected witness gives an actual nonzero vacuum-orthogonal
vector in the Hamiltonian domain by Laplace-resolvent regularization. Its
energy is finite and nonnegative, but need not be strictly positive. This
does not prove the SpectralGap.FiniteExcitation requirement. -/
import UnifiedTheory.Clay.YangMills.FullSchwartzVacuum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSResolventWitnessState
noncomputable section
open ContinuumControl PeriodicLattice4 KernelHilbertCompletion
open FullSchwartzHamiltonian RenormalizedFullOSLimit

variable (W : Hierarchy) (plane : Plane)
  (hp : OSPositiveTimeKernel.Positive W plane)
  (hfull : FullPositiveTimeReflection.Positive W plane)
  (D : OSScalarDynamics.Evolution W plane hp)

theorem resolvent_norm_le (w : State W plane hfull) :
    ‖resolvent W plane hp hfull D w‖ ≤ ‖w‖ := by
  rw [resolvent_apply, LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    OSLaplaceResolvent.resolvent_contraction D
      ((FullSchwartzHilbert.equivalence W plane hp hfull).symm w)

theorem resolvent_orthogonal (w : State W plane hfull)
    (ho : inner ℂ (fullVacuum W plane hfull) w = 0) :
    inner ℂ (fullVacuum W plane hfull) (resolvent W plane hp hfull D w) = 0 := by
  rw [← resolvent_symmetric, FullSchwartzVacuum.resolvent_vacuum]
  exact ho

theorem resolvent_nonzero (w : State W plane hfull) (hw : w ≠ 0) :
    resolvent W plane hp hfull D w ≠ 0 := by
  intro he
  apply hw
  exact resolvent_injective W plane hp hfull D (by simpa only [map_zero] using he)

theorem energy_bounds (w : State W plane hfull) :
    0 ≤ (inner ℂ (rangePoint W plane hp hfull D w : State W plane hfull)
      (hamiltonian W plane hp hfull D (rangePoint W plane hp hfull D w))).re ∧
    (inner ℂ (rangePoint W plane hp hfull D w : State W plane hfull)
      (hamiltonian W plane hp hfull D (rangePoint W plane hp hfull D w))).re ≤ ‖w‖^2 := by
  refine ⟨nonnegative W plane hp hfull D _, ?_⟩
  rw [rangePoint_value, apply_range, inner_sub_right, Complex.sub_re]
  have hs : (inner ℂ (resolvent W plane hp hfull D w)
      (resolvent W plane hp hfull D w)).re = ‖resolvent W plane hp hfull D w‖^2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hs]
  have hc := re_inner_le_norm (𝕜 := ℂ) (resolvent W plane hp hfull D w) w
  change (inner ℂ (resolvent W plane hp hfull D w) w).re ≤
    ‖resolvent W plane hp hfull D w‖ * ‖w‖ at hc
  have hb := mul_le_mul_of_nonneg_right (resolvent_norm_le W plane hp hfull D w) (norm_nonneg w)
  nlinarith [sq_nonneg ‖resolvent W plane hp hfull D w‖]

theorem hamiltonian_norm_bound (w : State W plane hfull) :
    ‖hamiltonian W plane hp hfull D (rangePoint W plane hp hfull D w)‖ ≤ 2*‖w‖ := by
  rw [apply_range]
  have ht := norm_sub_le w (resolvent W plane hp hfull D w)
  have hb := resolvent_norm_le W plane hp hfull D w
  linarith

/-- The positive reflected witness survives regularization into the exact
Hamiltonian domain. No lower bound for its energy or regularized norm follows. -/
theorem exists_domain_state (w : State W plane hfull) (hw : w ≠ 0)
    (ho : inner ℂ (fullVacuum W plane hfull) w = 0) :
    ∃ x : (hamiltonian W plane hp hfull D).domain,
      (x : State W plane hfull) ≠ 0 ∧
      inner ℂ (fullVacuum W plane hfull) (x : State W plane hfull) = 0 ∧
      ‖(x : State W plane hfull)‖ ≤ ‖w‖ ∧
      ‖hamiltonian W plane hp hfull D x‖ ≤ 2*‖w‖ ∧
      0 ≤ (inner ℂ (x : State W plane hfull) (hamiltonian W plane hp hfull D x)).re ∧
      (inner ℂ (x : State W plane hfull) (hamiltonian W plane hp hfull D x)).re ≤ ‖w‖^2 :=
  ⟨rangePoint W plane hp hfull D w, resolvent_nonzero W plane hp hfull D w hw,
    resolvent_orthogonal W plane hp hfull D w ho, resolvent_norm_le W plane hp hfull D w,
    hamiltonian_norm_bound W plane hp hfull D w, energy_bounds W plane hp hfull D w⟩

end
end UnifiedTheory.Clay.YangMills.OSResolventWitnessState
