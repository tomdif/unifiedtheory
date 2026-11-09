/-
  Exact external gauge coupling for local quantum walks.
  The links and gauge group representation are supplied. Unitarity,
  covariance, finite-history cancellation, and loop traces are derived.
  No gauge-field dynamics, anomaly cancellation, or mirror removal is
  asserted. Matrix-valued links permit non-Abelian examples.
-/
import UnifiedTheory.Audit.KFCausalWeylWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalGaugeWalk
noncomputable section
open scoped BigOperators

section Algebra
variable {R : Type*} [Ring R] [StarRing R]

def conjugate (g A : R) : R := g * A * star g

theorem conjugate_mul (g A B : R) (hg : star g * g = 1) :
    conjugate g A * conjugate g B = conjugate g (A * B) := by
  unfold conjugate
  calc
    _ = g * A * (star g * g) * B * star g := by noncomm_ring
    _ = _ := by rw [hg]; simp only [mul_one, mul_assoc]

theorem star_conjugate (g A : R) : star (conjugate g A) = conjugate g (star A) := by
  simp only [conjugate, star_mul, star_star, mul_assoc]

/-- A spin projection controls forward versus reverse gauge transport. -/
def controlled (P T : R) : R := P * T + (1 - P) * star T

theorem controlled_left_unitary (P T : R) (hP : star P = P) (hPP : P * P = P)
    (hPT : P * T = T * P) (hT : star T * T = 1) (hTr : T * star T = 1) :
    star (controlled P T) * controlled P T = 1 := by
  have hpq : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
  have hqp : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
  have hqq : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, hpq, sub_zero]
  have hfirst : star T * P * T = P := by
    rw [mul_assoc, hPT, ← mul_assoc, hT, one_mul]
  have hTq : T * (1 - P) = (1 - P) * T := by
    simp only [mul_sub, sub_mul, mul_one, one_mul, hPT]
  have hsecond : T * (1 - P) * star T = 1 - P := by
    rw [hTq, mul_assoc, hTr, mul_one]
  calc
    _ = star T * (P * P) * T + star T * (P * (1 - P)) * star T +
        T * ((1 - P) * P) * T + T * ((1 - P) * (1 - P)) * star T := by
      simp only [controlled, star_add, star_mul, star_sub, star_one, star_star, hP]
      noncomm_ring
    _ = star T * P * T + T * (1 - P) * star T := by
      rw [hPP, hpq, hqp, hqq]
      simp
    _ = 1 := by rw [hfirst, hsecond]; abel

theorem controlled_star (P T : R) (hP : star P = P) (hPT : P * T = T * P) :
    star (controlled P T) = controlled P (star T) := by
  have hs : star T * P = P * star T := by
    simpa only [star_mul, hP] using congrArg star hPT
  have hTq : T * (1 - P) = (1 - P) * T := by
    simp only [mul_sub, sub_mul, mul_one, one_mul, hPT]
  simp only [controlled, star_add, star_mul, star_sub, star_one, star_star, hP, hs, hTq]

theorem controlled_right_unitary (P T : R) (hP : star P = P) (hPP : P * P = P)
    (hPT : P * T = T * P) (hT : star T * T = 1) (hTr : T * star T = 1) :
    controlled P T * star (controlled P T) = 1 := by
  have hs : P * star T = star T * P := by
    simpa only [star_mul, hP] using (congrArg star hPT).symm
  have h := controlled_left_unitary P (star T) hP hPP hs
    (by simpa only [star_star] using hTr) (by simpa only [star_star] using hT)
  rw [← controlled_star P T hP hPT, star_star] at h
  exact h

theorem controlled_covariant (P T g : R) (hPg : P * g = g * P) :
    controlled P (conjugate g T) = conjugate g (controlled P T) := by
  have hQg : (1 - P) * g = g * (1 - P) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hPg]
  simp only [controlled, conjugate, star_mul, star_star, mul_add, add_mul,
    ← mul_assoc, hPg, hQg]

def propagator (F : ℕ → R) : ℕ → R
  | 0 => 1
  | n + 1 => F n * propagator F n

def gaugedStep (G F : ℕ → R) (n : ℕ) : R := G (n + 1) * F n * star (G n)

/-- A temporal link joins the frames at consecutive times. -/
theorem spacetime_step_covariant (g0 g1 V S : R) (hg0 : star g0 * g0 = 1) :
    (g1 * V * star g0) * conjugate g0 S = g1 * (V * S) * star g0 := by
  unfold conjugate
  calc
    _ = g1 * V * (star g0 * g0) * S * star g0 := by noncomm_ring
    _ = _ := by rw [hg0]; simp only [mul_one, mul_assoc]

/-- The unnormalized branch state transforms at the final endpoint. -/
theorem branch_covariant (g0 g1 K rho : R) (hg0 : star g0 * g0 = 1) :
    (g1 * K * star g0) * conjugate g0 rho * star (g1 * K * star g0) =
      conjugate g1 (K * rho * star K) := by
  simp only [conjugate, star_mul, star_star]
  calc
    _ = g1 * K * (star g0 * g0) * rho * (star g0 * g0) * star K * star g1 := by
      noncomm_ring
    _ = _ := by rw [hg0]; simp only [mul_one, mul_assoc]

/-- Endpoint covariance at every finite length. Steps may also be
nonunitary outcome operators; only the frame changes must be unitary. -/
theorem propagator_covariant (G F : ℕ → R)
    (hG : ∀ n, star (G n) * G n = 1) (hG0 : G 0 * star (G 0) = 1) (n : ℕ) :
    propagator (gaugedStep G F) n = G n * propagator F n * star (G 0) := by
  induction n with
  | zero => simpa only [propagator, mul_one] using hG0.symm
  | succ n ih =>
    simp only [propagator, gaugedStep, ih]
    calc
      _ = G (n + 1) * F n * (star (G n) * G n) * propagator F n * star (G 0) := by
        noncomm_ring
      _ = _ := by rw [hG n]; simp only [mul_one, mul_assoc]

theorem conjugate_powers (g F : R) (hg : star g * g = 1) (hgr : g * star g = 1)
    (n : ℕ) : (conjugate g F) ^ n = conjugate g (F ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, conjugate, mul_one] using hgr.symm
  | succ n ih => rw [pow_succ, ih, conjugate_mul g _ _ hg, pow_succ]

def holonomy (T U : R) : R := T * U * star T * star U

theorem holonomy_covariant (g T U : R) (hg : star g * g = 1) :
    holonomy (conjugate g T) (conjugate g U) = conjugate g (holonomy T U) := by
  simp only [holonomy, star_conjugate]
  rw [conjugate_mul g _ _ hg, conjugate_mul g _ _ hg, conjugate_mul g _ _ hg]
end Algebra

open Matrix

section Transport
variable {site R : Type*} [Fintype site] [DecidableEq site] [Ring R] [StarRing R]

/-- L x transports from p⁻¹ x to x. Entries can themselves be color matrices. -/
def transport (p : Equiv.Perm site) (L : site → R) : Matrix site site R :=
  fun x y => if x = p y then L x else 0

omit [Fintype site] [StarRing R] in
theorem transport_identity : transport (Equiv.refl site) (fun _ => (1 : R)) = 1 := by
  ext x y
  simp [transport, Matrix.one_apply]

omit [StarRing R] in
theorem transport_mul (p q : Equiv.Perm site) (L M : site → R) :
    transport p L * transport q M =
      transport (q.trans p) (fun x => L x * M (p.symm x)) := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (p.symm x)]
  · by_cases h : x = p (q y)
    · simp [transport, h]
    · simp [transport, Equiv.symm_apply_eq, h]
  · intro z _ hne
    have hx : x ≠ p z := by
      intro h
      have hz : z = p.symm x := by simpa using (congrArg p.symm h).symm
      exact hne hz
    simp [transport, hx]
  · simp

omit [Fintype site] in
theorem transport_adjoint (p : Equiv.Perm site) (L : site → R) :
    (transport p L)ᴴ = transport p.symm (fun x => star (L (p x))) := by
  ext x y
  by_cases h : y = p x
  · subst y
    simp [transport, Matrix.conjTranspose_apply]
  · have hx : x ≠ p.symm y := by
      intro heq
      exact h ((p.apply_eq_iff_eq_symm_apply).2 heq).symm
    simp [transport, Matrix.conjTranspose_apply, h, hx]

theorem transport_left_unitary (p : Equiv.Perm site) (L : site → R)
    (hL : ∀ x, star (L x) * L x = 1) :
    (transport p L)ᴴ * transport p L = 1 := by
  rw [transport_adjoint, transport_mul]
  simpa only [Equiv.self_trans_symm, Equiv.symm_symm, hL] using
    (transport_identity (site := site) (R := R))

theorem transport_right_unitary (p : Equiv.Perm site) (L : site → R)
    (hL : ∀ x, L x * star (L x) = 1) :
    transport p L * (transport p L)ᴴ = 1 := by
  rw [transport_adjoint, transport_mul]
  simpa only [Equiv.symm_trans_self, Equiv.apply_symm_apply, hL] using
    (transport_identity (site := site) (R := R))

def gaugeLinks (p : Equiv.Perm site) (g L : site → R) (x : site) : R :=
  g x * L x * star (g (p.symm x))

/-- The site-dependent endpoint rule yields the actual matrix covariance. -/
theorem transport_covariant (p : Equiv.Perm site) (g L : site → R) :
    transport p (gaugeLinks p g L) =
      Matrix.diagonal g * transport p L * (Matrix.diagonal g)ᴴ := by
  ext x y
  simp only [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : x = p y
  · subst x
    simp [transport, gaugeLinks]
  · simp [transport, h]

theorem diagonal_left_unitary (g : site → R) (hg : ∀ x, star (g x) * g x = 1) :
    (Matrix.diagonal g)ᴴ * Matrix.diagonal g = 1 := by
  simp [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, hg]

theorem diagonal_right_unitary (g : site → R) (hg : ∀ x, g x * star (g x) = 1) :
    Matrix.diagonal g * (Matrix.diagonal g)ᴴ = 1 := by
  simp [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, hg]
end Transport

section Predictions
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Operator" => Matrix ι ι ℂ

theorem conjugate_trace (g A : Operator) (hg : gᴴ * g = 1) :
    (g * A * gᴴ).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, hg, Matrix.one_mul]

theorem gauge_expectation (g rho O : Operator) (hg : gᴴ * g = 1) :
    ((g * rho * gᴴ) * (g * O * gᴴ)).trace = (rho * O).trace := by
  change (conjugate g rho * conjugate g O).trace = _
  rw [conjugate_mul g rho O hg]
  exact conjugate_trace g _ hg

/-- All finite branch weights agree, with covariantly transformed preparation
and final effect. Positivity is needed to interpret these traces as probabilities,
but not for the equality itself. No reset or normalization at intermediate times. -/
theorem history_expectation (G F : ℕ → Operator) (rho O : Operator)
    (hG : ∀ n, (G n)ᴴ * G n = 1) (hG0 : G 0 * (G 0)ᴴ = 1) (n : ℕ) :
    ((propagator (gaugedStep G F) n * conjugate (G 0) rho *
      (propagator (gaugedStep G F) n)ᴴ) * conjugate (G n) O).trace =
      ((propagator F n * rho * (propagator F n)ᴴ) * O).trace := by
  rw [propagator_covariant G F hG hG0 n]
  change (((G n * propagator F n * star (G 0)) * conjugate (G 0) rho *
    star (G n * propagator F n * star (G 0))) * conjugate (G n) O).trace = _
  rw [branch_covariant (G 0) (G n) (propagator F n) rho (hG 0)]
  exact gauge_expectation (G n) _ O (hG n)

theorem wilson_trace_invariant (g T U : Operator) (hg : gᴴ * g = 1) :
    (holonomy (conjugate g T) (conjugate g U)).trace = (holonomy T U).trace := by
  rw [holonomy_covariant g T U hg]
  exact conjugate_trace g _ hg
end Predictions

#print axioms controlled_left_unitary
#print axioms controlled_right_unitary
#print axioms controlled_covariant
#print axioms spacetime_step_covariant
#print axioms branch_covariant
#print axioms propagator_covariant
#print axioms conjugate_powers
#print axioms holonomy_covariant
#print axioms transport_mul
#print axioms transport_adjoint
#print axioms transport_left_unitary
#print axioms transport_right_unitary
#print axioms transport_covariant
#print axioms diagonal_left_unitary
#print axioms diagonal_right_unitary
#print axioms gauge_expectation
#print axioms history_expectation
#print axioms wilson_trace_invariant

end
end UnifiedTheory.Audit.KFCausalGaugeWalk
