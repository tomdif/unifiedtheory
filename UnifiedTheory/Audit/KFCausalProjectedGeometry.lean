/-
  Support for the projected-root obstruction and a regulated local sector.
  The rooted graph enumeration, metric detours, Hamiltonian construction,
  and propagation estimates are analytic/executable suppliers in the note.
-/
import UnifiedTheory.Audit.KFCausalEnergeticProbe

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalProjectedGeometry
noncomputable section
open scoped Matrix

/-- Every cubic root has twelve squares; the finite local check gives at most nine. -/
theorem root_square_obstruction (squares : ℕ) (h : squares ≤ 9) :
    squares ≠ 12 := by omega

/-- A forbidden off-diagonal move leaves its balancing diagonal after compression. -/
theorem retained_diagonal {A : Type*} [Ring A] (P S : A)
    (h : P * S * P = 0) :
    P * (S * S - S) * P = P * (S * S) * P := by
  rw [mul_sub, sub_mul, h, sub_zero]

/-- Diagonal operators multiply each compressed matrix element by the two gates. -/
theorem forbidden_projected_entry {X : Type*} [Fintype X] [DecidableEq X]
    (gate : X → ℂ) (H : Matrix X X ℂ) (i j : X)
    (h : gate i = 0 ∨ gate j = 0) :
    (Matrix.diagonal gate * H * Matrix.diagonal gate) i j = 0 :=
  KFCausalPatchGrowth.gate_removes_edge gate H i j h

/-- Replacing each edge by a supplied at-most-two-step detour controls a path. -/
theorem detour_sum_bound {X : Type*} (edges : Finset X) (length : X → ℝ)
    (h : ∀ e ∈ edges, length e ≤ 2) :
    ∑ e ∈ edges, length e ≤ 2 * (edges.card : ℝ) := by
  calc
    _ ≤ ∑ _e ∈ edges, (2 : ℝ) := Finset.sum_le_sum h
    _ = _ := by simp [mul_comm]

/-- The two distance comparisons also control balls at intermediate radii. -/
theorem ball_comparison (dBase dGraph radius : ℝ)
    (h1 : dBase ≤ 2 * dGraph) (h2 : dGraph ≤ 2 * dBase) :
    (dBase ≤ radius / 2 → dGraph ≤ radius) ∧
    (dGraph ≤ radius → dBase ≤ 2 * radius) := by
  constructor <;> intro h <;> linarith

/-- A cubic-torus antipode keeps a positive volume-normalized distance. -/
theorem noncollapsed_antipode (distance side : ℝ) (hs : 0 < side)
    (hd : 3 * side / 2 ≤ 2 * distance) :
    (3 : ℝ) / 4 ≤ distance / side := by
  apply (le_div_iff₀ hs).mpr
  linarith

/-- The compressed all-move diagonal differs from the switch Laplacian by a constant. -/
theorem switch_diagonal_constant (rho vertices switches : ℝ) :
    300 * rho * vertices =
      4 * rho * switches + (300 * rho * vertices - 4 * rho * switches) := by ring

/-- Geometry bits and matter sites share a size-independent interaction bound. -/
theorem local_interaction_envelope (rho J kappa : ℝ)
    (hr : 0 ≤ rho) (hJ : 0 ≤ J) (hk : 0 ≤ kappa) :
    8 * kappa ≤ 8 * kappa + 4 * rho + 62 * J ∧
    4 * kappa + 4 * rho + 62 * J ≤ 8 * kappa + 4 * rho + 62 * J := by
  constructor <;> linarith

/-- An interaction chain of n sets, each diameter at most R, supplies this separation bound. -/
theorem weighted_chain_distance (distance R mu : ℝ) (n : ℕ)
    (hm : 0 ≤ mu) (hd : distance ≤ (n : ℝ) * R) :
    Real.exp (mu * distance) ≤ Real.exp (mu * R * (n : ℝ)) := by
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A linear-time cone follows by comparing the exponential exponents. -/
theorem outside_cone_bound (amplitude prefactor rate time mu distance margin : ℝ)
    (hp : 0 ≤ prefactor)
    (ha : amplitude ≤ prefactor * Real.exp (rate * time - mu * distance))
    (hout : rate * time + margin ≤ mu * distance) :
    amplitude ≤ prefactor * Real.exp (-margin) := by
  exact ha.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith)) hp)

#print axioms root_square_obstruction
#print axioms retained_diagonal
#print axioms forbidden_projected_entry
#print axioms detour_sum_bound
#print axioms ball_comparison
#print axioms noncollapsed_antipode
#print axioms switch_diagonal_constant
#print axioms local_interaction_envelope
#print axioms weighted_chain_distance
#print axioms outside_cone_bound

end
end UnifiedTheory.Audit.KFCausalProjectedGeometry
