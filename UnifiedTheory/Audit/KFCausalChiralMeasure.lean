/-
  Algebra for constructing and comparing local chiral bases.
  Tangents, inverse Gram factors, and spanning frames have explicit hypotheses.
  Analytic existence, smoothness, and Kato evolution are assembled in
  CHIRAL_MEASURE_CONSTRUCTION.md; a gauge-invariant local measure current
  for the physical fermion multiplet is not constructed here.
-/
import UnifiedTheory.Audit.KFCausalOverlapChirality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalChiralMeasure
noncomputable section

section Algebra
variable {R : Type*} [Ring R]

def comm (A B : R) : R := A * B - B * A
def kato (P A : R) : R := comm A P

/-- Differentiating P²=P gives AP+PA=A; its diagonal block vanishes. -/
theorem tangent_diagonal_zero (P A : R) (hP : P * P = P)
    (hA : A * P + P * A = A) : P * A * P = 0 := by
  have h := congrArg (fun X => P * X) hA
  simpa only [mul_add, ← mul_assoc, hP, add_eq_right] using h

theorem kato_intertwining_generator (P A : R) (hP : P * P = P)
    (hA : A * P + P * A = A) : comm (kato P A) P = A := by
  have hp := tangent_diagonal_zero P A hP hA
  calc
    _ = A * P + P * A - (P * A * P + P * A * P) := by
      have hp (x : R) : P * (P * x) = P * x := by rw [← mul_assoc, hP]
      simp only [kato, comm]
      noncomm_ring [hP, hp]
    _ = A := by rw [hp, hA]; simp

theorem kato_diagonal_zero (P A : R) (hP : P * P = P) :
    P * kato P A * P = 0 := by
  have hp (x : R) : P * (P * x) = P * x := by rw [← mul_assoc, hP]
  simp only [kato, comm]
  noncomm_ring [hP, hp]

theorem kato_complement (P A : R) : kato (1 - P) (-A) = kato P A := by
  unfold kato comm
  noncomm_ring

variable [StarRing R]

theorem kato_skew (P A : R) (hP : star P = P) (hA : star A = A) :
    star (kato P A) = -kato P A := by
  simp only [kato, comm, star_sub, star_mul, hP, hA]
  abel

omit [StarRing R] in
/-- The unnormalized direct rotation from the P subspace to the Q subspace. -/
def bridge (P Q : R) : R := Q * P + (1 - Q) * (1 - P)

omit [StarRing R] in
theorem bridge_intertwines (P Q : R) (hP : P * P = P) (hQ : Q * Q = Q) :
    Q * bridge P Q = bridge P Q * P := by
  have hp (x : R) : P * (P * x) = P * x := by rw [← mul_assoc, hP]
  have hq (x : R) : Q * (Q * x) = Q * x := by rw [← mul_assoc, hQ]
  unfold bridge
  noncomm_ring [hP, hQ, hp, hq]

theorem bridge_star (P Q : R) (hP : star P = P) (hQ : star Q = Q) :
    star (bridge P Q) = bridge Q P := by
  simp only [bridge, star_add, star_mul, star_sub, star_one, hP, hQ]

/-- If ||P-Q||<1, this Gram matrix is positive definite (analytic step). -/
theorem bridge_gram (P Q : R) (hP : P * P = P) (hQ : Q * Q = Q)
    (hsP : star P = P) (hsQ : star Q = Q) :
    star (bridge P Q) * bridge P Q = 1 - (P - Q) * (P - Q) := by
  rw [bridge_star P Q hsP hsQ]
  have hp (x : R) : P * (P * x) = P * x := by rw [← mul_assoc, hP]
  have hq (x : R) : Q * (Q * x) = Q * x := by rw [← mul_assoc, hQ]
  unfold bridge
  noncomm_ring [hP, hQ, hp, hq]

omit [StarRing R] in
theorem bridge_gram_commutes (P Q : R) (hP : P * P = P) (hQ : Q * Q = Q) :
    P * (1 - (P - Q) * (P - Q)) = (1 - (P - Q) * (P - Q)) * P := by
  have hp (x : R) : P * (P * x) = P * x := by rw [← mul_assoc, hP]
  have hq (x : R) : Q * (Q * x) = Q * x := by rw [← mul_assoc, hQ]
  noncomm_ring [hP, hQ, hp, hq]

end Algebra

open Matrix
section Frames
variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
local notation "Op" => Matrix n n ℂ
local notation "Frame" => Matrix n k ℂ

def patchFrame (P : Op) (W : Frame) (S : Matrix k k ℂ) : Frame := P * W * S

omit [DecidableEq n] [DecidableEq k] in
theorem patchFrame_in_range (P : Op) (W : Frame) (S : Matrix k k ℂ)
    (hP : P * P = P) : P * patchFrame P W S = patchFrame P W S := by
  simp only [patchFrame, ← Matrix.mul_assoc, hP]

omit [DecidableEq n] in
/-- S is the inverse positive square root of W†PW in the analytic construction.
The algebra only needs the displayed normalization identity. -/
theorem patchFrame_isometry (P : Op) (W : Frame) (S : Matrix k k ℂ)
    (hP : P * P = P) (hsP : Pᴴ = P)
    (hS : Sᴴ * (Wᴴ * P * W) * S = 1) :
    (patchFrame P W S)ᴴ * patchFrame P W S = 1 := by
  simp only [patchFrame, Matrix.conjTranspose_mul, hsP]
  calc
    _ = Sᴴ * Wᴴ * (P * P) * W * S := by simp only [Matrix.mul_assoc]
    _ = Sᴴ * (Wᴴ * P * W) * S := by rw [hP]; simp only [Matrix.mul_assoc]
    _ = 1 := hS

omit [DecidableEq k] in
/-- Simultaneously changing the reference frame is essential here. -/
theorem patchFrame_covariant (P G : Op) (W : Frame) (S : Matrix k k ℂ)
    (hG : Gᴴ * G = 1) :
    patchFrame (G * P * Gᴴ) (G * W) S = G * patchFrame P W S := by
  unfold patchFrame
  calc
    _ = G * P * (Gᴴ * G) * W * S := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hG]; simp only [Matrix.mul_one, Matrix.mul_assoc]

def transition (V W : Frame) : Matrix k k ℂ := Vᴴ * W

omit [DecidableEq n] [DecidableEq k] in
theorem transition_reconstructs (P : Op) (V W : Frame)
    (hV : V * Vᴴ = P) (hW : P * W = W) : V * transition V W = W := by
  rw [transition, ← Matrix.mul_assoc, hV, hW]

omit [DecidableEq n] in
theorem transition_unitary (P : Op) (V W : Frame)
    (hV : V * Vᴴ = P) (hW : P * W = W) (hWi : Wᴴ * W = 1) :
    (transition V W)ᴴ * transition V W = 1 := by
  simp only [transition, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    _ = Wᴴ * (V * Vᴴ) * W := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hV, Matrix.mul_assoc, hW, hWi]

omit [DecidableEq n] [DecidableEq k] in
theorem transition_cocycle (P : Op) (V W Z : Frame)
    (hW : W * Wᴴ = P) (hZ : P * Z = Z) :
    transition V W * transition W Z = transition V Z := by
  unfold transition
  calc
    _ = Vᴴ * (W * Wᴴ) * Z := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hW, Matrix.mul_assoc, hZ]

omit [DecidableEq n] in
theorem determinant_transition_cocycle (P : Op) (V W Z : Frame)
    (hW : W * Wᴴ = P) (hZ : P * Z = Z) :
    (transition V W).det * (transition W Z).det = (transition V Z).det := by
  rw [← Matrix.det_mul, transition_cocycle P V W Z hW hZ]

end Frames

section Curvature
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Op" => Matrix n n ℂ

/-- Berry curvature for two commuting parameter variations, convention i Tr(P[dP,dP]). -/
def curvature (P A B : Op) : ℂ := Complex.I * Matrix.trace (P * comm A B)

theorem curvature_antisymmetric (P A B : Op) : curvature P B A = -curvature P A B := by
  have h : comm B A = -comm A B := by unfold comm; abel
  simp only [curvature, h, mul_neg, Matrix.trace_neg]

/-- Opposite chiralities of the SAME projector family cancel this curvature.
This is vectorlike pairing, not cancellation for a chiral SM multiplet. -/
theorem complement_curvature_cancels (P A B : Op) :
    curvature P A B + curvature (1 - P) (-A) (-B) = 0 := by
  have h : comm (-A) (-B) = comm A B := by unfold comm; simp
  rw [curvature, curvature, h, ← mul_add, ← Matrix.trace_add,
    ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
  simp only [comm, Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self, mul_zero]

/-- The curvature in a gauge-orbit direction is a variation of a trace density.
This finite identity does not solve the local-current reconstruction problem. -/
theorem gauge_direction_curvature (P X B : Op) (hP : P * P = P)
    (hB : B * P + P * B = B) :
    curvature P (comm X P) B = -Complex.I * Matrix.trace (X * B) := by
  have hp (A : Op) : P * (P * A) = P * A := by rw [← Matrix.mul_assoc, hP]
  have hb := tangent_diagonal_zero P B hP hB
  have hfirst : Matrix.trace (P * X * P * B) = 0 := by
    calc
      _ = Matrix.trace ((X * P * B) * P) := by
        rw [Matrix.mul_assoc P X P, Matrix.mul_assoc P (X * P) B,
          Matrix.trace_mul_comm]
      _ = Matrix.trace (X * (P * B * P)) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hb]; simp
  have hsecond : Matrix.trace (P * B * X * P) = Matrix.trace (X * (P * B)) := by
    calc
      _ = Matrix.trace (P * (P * B * X)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (P * B * X) := by simp only [Matrix.mul_assoc, hp]
      _ = _ := Matrix.trace_mul_comm _ _
  have hthird : Matrix.trace (P * X * B) = Matrix.trace (X * (B * P)) := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm P (X * B), Matrix.mul_assoc]
  have hexpand : P * comm (comm X P) B =
      P * X * P * B - P * X * B - P * B * X * P + P * B * P * X := by
    simp only [comm]
    noncomm_ring [hP, hp]
  have hsum : Matrix.trace (X * (B * P)) + Matrix.trace (X * (P * B)) =
      Matrix.trace (X * B) := by
    rw [← Matrix.trace_add, ← Matrix.mul_add, hB]
  rw [curvature, hexpand, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    hfirst, hsecond, hthird, hb]
  simp only [Matrix.zero_mul, Matrix.trace_zero, add_zero, zero_sub]
  linear_combination -Complex.I * hsum

end Curvature

#print axioms tangent_diagonal_zero
#print axioms kato_intertwining_generator
#print axioms kato_diagonal_zero
#print axioms kato_complement
#print axioms kato_skew
#print axioms bridge_intertwines
#print axioms bridge_star
#print axioms bridge_gram
#print axioms bridge_gram_commutes
#print axioms patchFrame_in_range
#print axioms patchFrame_isometry
#print axioms patchFrame_covariant
#print axioms transition_reconstructs
#print axioms transition_unitary
#print axioms transition_cocycle
#print axioms determinant_transition_cocycle
#print axioms curvature_antisymmetric
#print axioms complement_curvature_cancels
#print axioms gauge_direction_curvature

end
end UnifiedTheory.Audit.KFCausalChiralMeasure
