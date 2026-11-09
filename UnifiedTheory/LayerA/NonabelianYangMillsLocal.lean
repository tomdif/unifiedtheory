/-
Verified algebraic ingredients for the actual DeTurck--Yang--Mills nonlinearity.
The Fourier-space local existence and Galerkin convergence proof is analytic
in NONABELIAN_YANG_MILLS_LOCAL_LIMIT.md; it is not wholly formalized here.
-/
import UnifiedTheory.LayerA.GaugeTransportStability
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.NonabelianYangMillsLocal
noncomputable section

def comm {R : Type*} [Ring R] (a b : R) : R := a*b-b*a

section RingAlgebra
variable {R : Type*} [Ring R]

theorem comm_self (a : R) : comm a a = 0 := by simp [comm]

theorem comm_antisymm (a b : R) : comm a b = -comm b a := by
  dsimp [comm]
  noncomm_ring

/-- Differentiating a commutator uses precisely these two Leibniz terms. -/
def commJet (a da b db : R) : R := comm da b + comm a db

/-- First component of the expanded two-dimensional DeTurck nonlinearity. -/
def nonlinearityOne (a b dax day dbx : R) : R :=
  comm a dax + 2 * comm b day - comm b dbx + comm b (comm b a)

/-- Jet-level cancellation of mixed second derivatives and divergence brackets.
`lap` is the sum of pure second derivatives and `mixed` the mixed derivative. -/
theorem deturck_component_identity (a b dax day dbx dby lap mixed : R) :
    lap - mixed + commJet b dby a day + comm b (day - dbx + comm b a) +
      mixed + comm a (dax + dby) = lap + nonlinearityOne a b dax day dbx := by
  dsimp [nonlinearityOne, commJet, comm]
  noncomm_ring

theorem comm_difference (a b c d : R) :
    comm a b - comm c d = comm (a-c) b + comm c (b-d) := by
  dsimp [comm]
  noncomm_ring

theorem double_comm_difference (a b c d : R) :
    comm a (comm a b) - comm c (comm c d) =
      comm (a-c) (comm a b) + comm c (comm (a-c) b) + comm c (comm c (b-d)) := by
  dsimp [comm]
  noncomm_ring

end RingAlgebra

section NormEstimates
variable {R : Type*} [NormedRing R]

theorem comm_norm (a b : R) : ‖comm a b‖ ≤ 2 * ‖a‖ * ‖b‖ := by
  calc
    ‖comm a b‖ ≤ ‖a*b‖ + ‖b*a‖ := norm_sub_le _ _
    _ ≤ ‖a‖*‖b‖ + ‖b‖*‖a‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖a‖ * ‖b‖ := by ring

theorem double_comm_norm (a b : R) : ‖comm a (comm a b)‖ ≤ 4 * ‖a‖^2 * ‖b‖ := by
  calc
    _ ≤ 2 * ‖a‖ * ‖comm a b‖ := comm_norm _ _
    _ ≤ 2 * ‖a‖ * (2 * ‖a‖ * ‖b‖) :=
      mul_le_mul_of_nonneg_left (comm_norm a b) (by positivity)
    _ = 4 * ‖a‖^2 * ‖b‖ := by ring

theorem comm_difference_norm (a b c d : R) :
    ‖comm a b - comm c d‖ ≤ 2*‖a-c‖*‖b‖ + 2*‖c‖*‖b-d‖ := by
  rw [comm_difference]
  exact (norm_add_le _ _).trans (add_le_add (comm_norm _ _) (comm_norm _ _))

end NormEstimates

def nonlinearBound (r : ℝ) := 16 * Real.pi * r^2 + 4*r^3
def nonlinearLipschitz (r : ℝ) := 32 * Real.pi * r + 12*r^2

theorem nonlinear_bound_relation (r : ℝ) (hr : 0 ≤ r) :
    nonlinearBound r ≤ r * nonlinearLipschitz r / 2 := by
  dsimp [nonlinearBound, nonlinearLipschitz]
  nlinarith [pow_nonneg hr 3]

theorem nonlinearLipschitz_pos (r : ℝ) (hr : 0 < r) : 0 < nonlinearLipschitz r := by
  dsimp [nonlinearLipschitz]
  positivity

theorem contraction_ball (r k : ℝ) (hr : 0 ≤ r) (hk : 0 ≤ k)
    (hsmall : k * nonlinearLipschitz r ≤ 1 / 2) :
    r/2 + k * nonlinearBound r ≤ 3*r/4 := by
  have hb := mul_le_mul_of_nonneg_left (nonlinear_bound_relation r hr) hk
  have hs := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ r / 2 by positivity)
  nlinarith

/-- The absorption step used for the full-sequence Galerkin estimate. -/
theorem absorb_cutoff_error (e tail c : ℝ) (he : 0 ≤ e) (hc : c ≤ 1 / 2)
    (h : e ≤ tail + c * e) : e ≤ 2*tail := by
  nlinarith [mul_le_mul_of_nonneg_right hc he]

section QuaternionWitness
open scoped Quaternion

def axisOne (a : ℝ) : Quaternion ℝ := ⟨0,a,0,0⟩
def axisTwo (a : ℝ) : Quaternion ℝ := ⟨0,0,a,0⟩
def axisThree (a : ℝ) : Quaternion ℝ := ⟨0,0,0,a⟩

theorem homogeneous_curvature (a : ℝ) :
    comm (axisOne a) (axisTwo a) = axisThree (2*a^2) := by
  ext <;> simp [comm, axisOne, axisTwo, axisThree, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

theorem homogeneous_rhs_one (a : ℝ) :
    comm (axisTwo a) (comm (axisTwo a) (axisOne a)) = axisOne (-4*a^3) := by
  ext <;> simp [comm, axisOne, axisTwo, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

theorem homogeneous_rhs_two (a : ℝ) :
    comm (axisOne a) (comm (axisOne a) (axisTwo a)) = axisTwo (-4*a^3) := by
  ext <;> simp [comm, axisOne, axisTwo, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

theorem homogeneous_curvature_nonzero (a : ℝ) (ha : a ≠ 0) :
    comm (axisOne a) (axisTwo a) ≠ 0 := by
  rw [homogeneous_curvature]
  intro hz
  have hk := congrArg (fun z : Quaternion ℝ => z.imK) hz
  simp only [axisThree, Quaternion.imK_zero] at hk
  exact ha (by nlinarith [sq_nonneg a])

theorem homogeneous_curvature_normSq (a : ℝ) :
    Quaternion.normSq (comm (axisOne a) (axisTwo a)) = 4*a^4 := by
  rw [homogeneous_curvature, Quaternion.normSq_def']
  simp [axisThree]
  ring

def amplitude (a t : ℝ) := a / Real.sqrt (1 + 8*a^2*t)

/-- An actual nonlinear solution, not only a polynomial identity for its RHS. -/
theorem amplitude_hasDerivAt (a t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (amplitude a) (-4*(amplitude a t)^3) t := by
  have hu : 0 < 1 + 8*a^2*t := by positivity
  have hs : Real.sqrt (1 + 8*a^2*t) ≠ 0 := (Real.sqrt_pos.2 hu).ne'
  have hd : HasDerivAt (fun x : ℝ => 1 + 8*a^2*x) (8*a^2) t := by
    convert (hasDerivAt_id t).const_mul (8*a^2) |>.const_add 1 using 1
    ring
  have hroot := hd.sqrt hu.ne'
  have hquot := (hasDerivAt_const t a).div hroot hs
  convert hquot using 1
  dsimp [amplitude]
  field_simp
  ring

end QuaternionWitness
end
end UnifiedTheory.LayerA.NonabelianYangMillsLocal
