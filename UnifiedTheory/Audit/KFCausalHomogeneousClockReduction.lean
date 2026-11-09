/-
  Exact classical reduction of the homogeneous diagonal vacuum constraint.
  The clock is tau=(x+y+z)/3; spatial volume is proportional to exp(3*tau/2).
  The negative trace momentum is solved on one branch of the constraint.
  This is a finite-dimensional continuum target, not a spin realization,
  an inhomogeneous reduction, or a quantum positivity theorem.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalHomogeneousClockReduction
noncomputable section

def originalMomenta (pTau u v : ℝ) : Fin 3 → ℝ :=
  ![pTau/3+u/2+v/6, pTau/3-u/2+v/6, pTau/3-v/3]

/-- Equality of canonical one-forms, evaluated on arbitrary velocities,
    for x=tau+beta1+beta2, y=tau-beta1+beta2, z=tau-2*beta2. -/
theorem canonical_one_form (pTau u v dt du dv : ℝ) :
    originalMomenta pTau u v 0 * (dt+du+dv) +
      originalMomenta pTau u v 1 * (dt-du+dv) +
      originalMomenta pTau u v 2 * (dt-2*dv) = pTau*dt+u*du+v*dv := by
  simp [originalMomenta]
  ring

theorem momentum_coordinates_inverse (pTau u v : ℝ) :
    let p := originalMomenta pTau u v
    p 0+p 1+p 2 = pTau ∧ p 0-p 1 = u ∧ p 0+p 1-2*p 2 = v := by
  dsimp [originalMomenta]
  constructor
  · ring
  constructor <;> ring

def constraint (pTau u v : ℝ) : ℝ := -pTau^2/6+u^2/2+v^2/6

theorem dewitt_in_clock_coordinates (pTau u v : ℝ) :
    let p := originalMomenta pTau u v
    p 0^2+p 1^2+p 2^2-(p 0+p 1+p 2)^2/2 = constraint pTau u v := by
  dsimp [originalMomenta, constraint]
  ring

def reducedEnergy (u v : ℝ) : ℝ := Real.sqrt (3*u^2+v^2)

theorem reducedEnergy_sq (u v : ℝ) : (reducedEnergy u v)^2 = 3*u^2+v^2 := by
  exact Real.sq_sqrt (by nlinarith [sq_nonneg u, sq_nonneg v])

theorem reducedEnergy_nonneg (u v : ℝ) : 0 ≤ reducedEnergy u v := Real.sqrt_nonneg _

theorem reducedEnergy_pos (u v : ℝ) (hn : u ≠ 0 ∨ v ≠ 0) :
    0 < reducedEnergy u v := by
  apply Real.sqrt_pos.2
  rcases hn with hu | hv
  · nlinarith [sq_pos_of_ne_zero hu, sq_nonneg v]
  · nlinarith [sq_pos_of_ne_zero hv, sq_nonneg u]

/-- The chosen time orientation removes the independent negative trace
    momentum. The physical Hamiltonian is -pTau=sqrt(3*u^2+v^2). -/
theorem negative_branch_iff (pTau u v : ℝ) :
    (constraint pTau u v = 0 ∧ pTau ≤ 0) ↔ pTau = -reducedEnergy u v := by
  have hs := reducedEnergy_sq u v
  have hp := reducedEnergy_nonneg u v
  constructor
  · rintro ⟨hc, ht⟩
    dsimp [constraint] at hc
    nlinarith
  · intro he
    rw [he]
    constructor
    · dsimp [constraint]
      nlinarith
    · linarith

/-- Pure homogeneous trace motion is not admissible nonzero vacuum data. -/
theorem pure_trace_constraint_iff (pTau : ℝ) :
    constraint pTau 0 0 = 0 ↔ pTau = 0 := by
  dsimp [constraint]
  constructor <;> intro h
  · nlinarith [sq_nonneg pTau]
  · simp [h]

theorem reducedEnergy_zero_iff (u v : ℝ) :
    reducedEnergy u v = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro hz
    have hs := reducedEnergy_sq u v
    rw [hz] at hs
    constructor <;> nlinarith [sq_nonneg u, sq_nonneg v]
  · rintro ⟨rfl, rfl⟩
    simp [reducedEnergy]

/-- The positive lapse/metric factor cancels from physical shape velocities. -/
theorem clock_monotone (c u v : ℝ) (hc : 0 < c) (hn : u ≠ 0 ∨ v ≠ 0) :
    0 < -c * (-reducedEnergy u v) / 3 := by
  have hp := reducedEnergy_pos u v hn
  rw [neg_mul_neg]
  exact div_pos (mul_pos hc hp) (by norm_num)

theorem reduced_rates (c u v : ℝ) (hc : c ≠ 0) (hn : u ≠ 0 ∨ v ≠ 0) :
    (c*u)/(-c*(-reducedEnergy u v)/3) = 3*u/reducedEnergy u v ∧
      (c*v/3)/(-c*(-reducedEnergy u v)/3) = v/reducedEnergy u v := by
  have he := ne_of_gt (reducedEnergy_pos u v hn)
  constructor <;> field_simp

/-- These rates are derivatives of the actual reduced Hamiltonian. -/
theorem reducedEnergy_deriv_u (u v : ℝ) (hn : u ≠ 0 ∨ v ≠ 0) :
    HasDerivAt (fun s => reducedEnergy s v) (3*u/reducedEnergy u v) u := by
  have hp : 0 < 3*u^2+v^2 := (Real.sqrt_pos.mp (reducedEnergy_pos u v hn))
  have hd := ((((hasDerivAt_id u).pow 2).const_mul 3).add_const (v^2)).sqrt (ne_of_gt hp)
  convert hd using 1
  dsimp [reducedEnergy]
  field_simp

theorem reducedEnergy_deriv_v (u v : ℝ) (hn : u ≠ 0 ∨ v ≠ 0) :
    HasDerivAt (fun s => reducedEnergy u s) (v/reducedEnergy u v) v := by
  have hp : 0 < 3*u^2+v^2 := (Real.sqrt_pos.mp (reducedEnergy_pos u v hn))
  have hd := (((hasDerivAt_id v).pow 2).const_add (3*u^2)).sqrt (ne_of_gt hp)
  convert hd using 1
  dsimp [reducedEnergy]
  field_simp

/-- Affine trajectory identity, used on the differentiable nonzero branch. -/
theorem reduced_trajectory (q1 q2 u v tau : ℝ) :
    HasDerivAt (fun t => q1+(3*u/reducedEnergy u v)*t)
      (3*u/reducedEnergy u v) tau ∧
    HasDerivAt (fun t => q2+(v/reducedEnergy u v)*t)
      (v/reducedEnergy u v) tau := by
  constructor <;> convert ((hasDerivAt_id tau).const_mul _).const_add _ using 1 <;> simp

/-- Explicit solutions of the reduced Hamilton equations at every clock time;
    the zero-momentum point is excluded because the clock stalls there. -/
theorem reduced_hamilton_equations (q1 q2 u v tau : ℝ) (hn : u ≠ 0 ∨ v ≠ 0) :
    HasDerivAt (fun t => q1+(3*u/reducedEnergy u v)*t)
      (deriv (fun s => reducedEnergy s v) u) tau ∧
    HasDerivAt (fun t => q2+(v/reducedEnergy u v)*t)
      (deriv (fun s => reducedEnergy u s) v) tau ∧
    HasDerivAt (fun _ : ℝ => u) 0 tau ∧ HasDerivAt (fun _ : ℝ => v) 0 tau := by
  rw [(reducedEnergy_deriv_u u v hn).deriv, (reducedEnergy_deriv_v u v hn).deriv]
  exact ⟨(reduced_trajectory q1 q2 u v tau).1, (reduced_trajectory q1 q2 u v tau).2,
    hasDerivAt_const tau u, hasDerivAt_const tau v⟩

theorem clock_stalls_at_vacuum (c : ℝ) : -c*(-reducedEnergy 0 0)/3 = 0 := by
  simp [reducedEnergy]

#print axioms canonical_one_form
#print axioms dewitt_in_clock_coordinates
#print axioms negative_branch_iff
#print axioms pure_trace_constraint_iff
#print axioms clock_monotone
#print axioms reduced_rates
#print axioms reducedEnergy_deriv_u
#print axioms reducedEnergy_deriv_v
#print axioms reduced_trajectory
#print axioms reduced_hamilton_equations
#print axioms clock_stalls_at_vacuum

end
end UnifiedTheory.Audit.KFCausalHomogeneousClockReduction
