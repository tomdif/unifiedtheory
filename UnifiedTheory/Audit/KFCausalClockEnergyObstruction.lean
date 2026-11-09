/- Energy is not a coercive bound for clock momentum in the exact
classical vacuum subfamily. This prevents replacing occupation control
by an energy estimate without another proved dynamical argument. -/
import UnifiedTheory.Audit.KFCausalPolynomialClockObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalClockEnergyObstruction
noncomputable section
open UnifiedTheory.Audit.KFCausalPolynomialClockObstruction

theorem vacuum_energy_at_zero (p : ℝ) : exactVacuumHamiltonian 0 p=1/2+Real.exp p := by
  simp [exactVacuumHamiltonian,exactClock,exactVacuumPotential,exactLongitudinal]

theorem negative_momentum_energy_bound (p : ℝ) (hp : p ≤ 0) :
    1/2 < exactVacuumHamiltonian 0 p ∧ exactVacuumHamiltonian 0 p ≤ 3/2 := by
  rw [vacuum_energy_at_zero]
  have he : Real.exp p ≤ 1 := by simpa using Real.exp_le_exp.mpr hp
  constructor
  · linarith [Real.exp_pos p]
  · linarith

/-- Every momentum threshold is exceeded on the same fixed finite
energy interval (1/2,3/2]. The clock position is fixed at s=0. -/
theorem bounded_energy_unbounded_momentum (B : ℝ) :
    ∃ p : ℝ, p ≤ 0 ∧ exactVacuumHamiltonian 0 p ≤ 3/2 ∧ B < p^2 := by
  let p := -(|B|+2)
  have hp : p ≤ 0 := by dsimp [p]; linarith [abs_nonneg B]
  refine ⟨p,hp,(negative_momentum_energy_bound p hp).2,?_⟩
  dsimp [p]
  nlinarith [le_abs_self B,abs_nonneg B,sq_nonneg |B|]

theorem no_affine_energy_control (C D : ℝ) (hC : 0 ≤ C) :
    ¬∀ p : ℝ, p^2 ≤ C*exactVacuumHamiltonian 0 p+D := by
  intro h
  obtain ⟨p,_,he,hp⟩ := bounded_energy_unbounded_momentum (C*(3/2)+D)
  have hbound := mul_le_mul_of_nonneg_left he hC
  linarith [h p]

#print axioms vacuum_energy_at_zero
#print axioms negative_momentum_energy_bound
#print axioms bounded_energy_unbounded_momentum
#print axioms no_affine_energy_control

end
end UnifiedTheory.Audit.KFCausalClockEnergyObstruction
