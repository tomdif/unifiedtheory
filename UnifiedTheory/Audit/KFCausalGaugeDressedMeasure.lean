/-
  Link-derived gauge dressing and a finite Weyl measure.
  Path transport supplies the frame; simultaneous fermion/antifermion
  dressing preserves the Weyl matrix. A finite divergence solver exposes
  why solving the Ward equation alone does not establish spacetime locality.
  Analytic patch existence and physical scope are in GAUGE_DRESSED_MEASURE.md.
-/
import UnifiedTheory.Audit.KFCausalChiralMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalGaugeDressedMeasure
noncomputable section
open scoped BigOperators

section Paths
variable {V G : Type*} [Group G]

def gaugeLink (g : V → G) (L : V → V → G) (x y : V) : G :=
  g x * L x y * (g y)⁻¹

def endpoint (r : V) : List V → V
  | [] => r
  | x :: xs => endpoint x xs

/-- Product of oriented transports along a supplied path beginning at r. -/
def pathFrame (L : V → V → G) (r : V) : List V → G
  | [] => 1
  | x :: xs => pathFrame L x xs * L x r

theorem pathFrame_gauge (g : V → G) (L : V → V → G) (r : V) (p : List V) :
    pathFrame (gaugeLink g L) r p = g (endpoint r p) * pathFrame L r p * (g r)⁻¹ := by
  induction p generalizing r with
  | nil => simp [pathFrame, endpoint]
  | cons x xs ih =>
    simp only [pathFrame, endpoint, gaugeLink, ih]
    group

def dressing (L : V → V → G) (r : V) (paths : V → List V) (x : V) : G :=
  pathFrame L r (paths x)

theorem dressing_gauge (g : V → G) (L : V → V → G) (r : V)
    (paths : V → List V) (hpaths : ∀ x, endpoint r (paths x) = x) (x : V) :
    dressing (gaugeLink g L) r paths x =
      g x * dressing L r paths x * (g r)⁻¹ := by
  simp only [dressing, pathFrame_gauge, hpaths]

def dressedLink (L : V → V → G) (c : V → G) (x y : V) : G :=
  (c x)⁻¹ * L x y * c y

theorem dressedLink_gauge (g c : V → G) (L : V → V → G) (r x y : V) :
    dressedLink (gaugeLink g L) (fun z => g z * c z * (g r)⁻¹) x y =
      g r * dressedLink L c x y * (g r)⁻¹ := by
  unfold dressedLink gaugeLink
  group

theorem dressedLink_based_invariant (g c : V → G) (L : V → V → G)
    (r x y : V) (hg : g r = 1) :
    dressedLink (gaugeLink g L) (fun z => g z * c z * (g r)⁻¹) x y =
      dressedLink L c x y := by
  rw [dressedLink_gauge, hg]
  simp

theorem dressedLink_reconstructs (c : V → G) (L : V → V → G) (x y : V) :
    c x * dressedLink L c x y * (c y)⁻¹ = L x y := by
  unfold dressedLink
  group

theorem treeLink_is_one (c : V → G) (L : V → V → G) (x y : V)
    (hc : c x = L x y * c y) : dressedLink L c x y = 1 := by
  unfold dressedLink
  rw [hc]
  group

end Paths

section Abelian
variable {V G : Type*} [CommGroup G]

/-- In U(1), even the residual root conjugation is trivial. -/
theorem dressedLink_abelian_invariant (g : V → G) (L : V → V → G) (r : V)
    (paths : V → List V) (hpaths : ∀ x, endpoint r (paths x) = x) (x y : V) :
    dressedLink (gaugeLink g L) (dressing (gaugeLink g L) r paths) x y =
      dressedLink L (dressing L r paths) x y := by
  have hc : dressing (gaugeLink g L) r paths =
      fun z => g z * dressing L r paths z * (g r)⁻¹ := by
    funext z
    exact dressing_gauge g L r paths hpaths z
  rw [hc, dressedLink_gauge]
  rw [mul_comm (g r), mul_assoc, mul_inv_cancel, mul_one]

end Abelian

open Matrix
section WeylMatrix
variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
local notation "Op" => Matrix n n ℂ
local notation "Frame" => Matrix n k ℂ

def weylMatrix (D : Op) (V B : Frame) : Matrix k k ℂ := Bᴴ * D * V

omit [Fintype k] [DecidableEq k] in
theorem weylMatrix_dressing (C D : Op) (V B : Frame) (hC : Cᴴ * C = 1) :
    weylMatrix (C * D * Cᴴ) (C * V) (C * B) = weylMatrix D V B := by
  simp only [weylMatrix, Matrix.conjTranspose_mul]
  calc
    _ = Bᴴ * (Cᴴ * C) * D * (Cᴴ * C) * V := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hC]; simp

theorem weylDet_dressing (C D : Op) (V B : Frame) (hC : Cᴴ * C = 1) :
    (weylMatrix (C * D * Cᴴ) (C * V) (C * B)).det = (weylMatrix D V B).det := by
  rw [weylMatrix_dressing C D V B hC]

omit [DecidableEq n] in
/-- The exact scalar correction between two choices of chiral bases. -/
theorem weylDet_basis_change (D : Op) (V B : Frame) (R S : Matrix k k ℂ) :
    (weylMatrix D (V * R) (B * S)).det =
      Sᴴ.det * (weylMatrix D V B).det * R.det := by
  have h : weylMatrix D (V * R) (B * S) = Sᴴ * weylMatrix D V B * R := by
    simp only [weylMatrix, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [h, Matrix.det_mul, Matrix.det_mul]

omit [DecidableEq k] in
/-- Inhomogeneous part of i Tr(V†dV) under a moving ambient frame. -/
theorem frame_connection_dressing (C dC : Op) (V dV : Frame) (hC : Cᴴ * C = 1) :
    Matrix.trace ((C * V)ᴴ * (dC * V + C * dV)) =
      Matrix.trace (Vᴴ * dV) + Matrix.trace ((Cᴴ * dC) * (V * Vᴴ)) := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.trace_add]
  have hfirst : Matrix.trace (Vᴴ * Cᴴ * (dC * V)) =
      Matrix.trace ((Cᴴ * dC) * (V * Vᴴ)) := by
    calc
      _ = Matrix.trace (Vᴴ * ((Cᴴ * dC) * V)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have hsecond : Vᴴ * Cᴴ * (C * dV) = Vᴴ * dV := by
    calc
      _ = Vᴴ * (Cᴴ * C) * dV := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hC]; simp
  rw [hfirst, hsecond]
  abel

omit [DecidableEq k] in
/-- Antifermions contribute the opposite basis connection. -/
theorem measure_connection_dressing (C dC : Op) (V dV B dB : Frame)
    (hC : Cᴴ * C = 1) :
    Matrix.trace ((C * V)ᴴ * (dC * V + C * dV)) -
        Matrix.trace ((C * B)ᴴ * (dC * B + C * dB)) =
      (Matrix.trace (Vᴴ * dV) - Matrix.trace (Bᴴ * dB)) +
        Matrix.trace ((Cᴴ * dC) * (V * Vᴴ - B * Bᴴ)) := by
  rw [frame_connection_dressing C dC V dV hC,
    frame_connection_dressing C dC B dB hC, Matrix.mul_sub, Matrix.trace_sub]
  abel

end WeylMatrix

section WardCurrent
variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]

/-- B is the based gauge-gradient matrix and A its tree left inverse. -/
theorem horizontal_kills_gauge (B : Matrix E V ℝ) (A : Matrix V E ℝ)
    (hAB : A * B = 1) : (1 - B * A) * B = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hAB, Matrix.mul_one, sub_self]

/-- Every horizontal one-form supplies a current with the prescribed Ward divergence. -/
theorem constructed_current_ward (B : Matrix E V ℝ) (A : Matrix V E ℝ)
    (ell : Matrix E Unit ℝ) (a : Matrix V Unit ℝ) (hAB : A * B = 1) :
    Bᵀ * ((1 - B * A)ᵀ * ell - Aᵀ * a) = -a := by
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
    horizontal_kills_gauge B A hAB, Matrix.transpose_zero, Matrix.zero_mul,
    ← Matrix.mul_assoc, ← Matrix.transpose_mul, hAB, Matrix.transpose_one,
    Matrix.one_mul, zero_sub]

omit [DecidableEq V] in
/-- Conversely, the same decomposition captures every solution of the Ward equation. -/
theorem ward_current_complete (B : Matrix E V ℝ) (A : Matrix V E ℝ)
    (j : Matrix E Unit ℝ) (a : Matrix V Unit ℝ) (hj : Bᵀ * j = -a) :
    (1 - B * A)ᵀ * j - Aᵀ * a = j := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hj, Matrix.mul_neg]
  abel

end WardCurrent

section Divergence
variable {R : Type*} [AddCommGroup R]

/-- Oriented current on the edge from site n to n+1 of a rooted line. -/
def prefixCurrent (a : ℕ → R) (n : ℕ) : R := ∑ j ∈ Finset.range (n + 1), a j

theorem prefixCurrent_first (a : ℕ → R) : prefixCurrent a 0 = a 0 := by
  simp [prefixCurrent]

theorem prefixCurrent_divergence (a : ℕ → R) (n : ℕ) :
    prefixCurrent a (n + 1) - prefixCurrent a n = a (n + 1) := by
  simp [prefixCurrent, Finset.sum_range_succ]

/-- The last site closes exactly when the total source vanishes. -/
theorem prefixCurrent_last (a : ℕ → R) (n : ℕ)
    (ha : ∑ j ∈ Finset.range (n + 2), a j = 0) :
    -prefixCurrent a n = a (n + 1) := by
  rw [Finset.sum_range_succ] at ha
  simpa only [prefixCurrent] using (neg_eq_iff_add_eq_zero.mpr ha)

theorem prefixCurrent_unique (a j : ℕ → R) (h0 : j 0 = a 0)
    (hj : ∀ n, j (n + 1) - j n = a (n + 1)) (n : ℕ) : j n = prefixCurrent a n := by
  induction n with
  | zero => simpa [prefixCurrent] using h0
  | succ n ih =>
    have h := hj n
    rw [sub_eq_iff_eq_add, ih] at h
    have hs : prefixCurrent a (n + 1) = prefixCurrent a n + a (n + 1) := by
      unfold prefixCurrent
      rw [Finset.sum_range_succ]
    rw [hs, h, add_comm]

end Divergence

section LongRange
def dipole (far : ℕ) (j : ℕ) : ℤ :=
  (if j = 0 then 1 else 0) - (if j = far then 1 else 0)

/-- A remote dipole forces unit current across every intervening tree edge. -/
theorem dipole_current (far n : ℕ) (hn : n < far) : prefixCurrent (dipole far) n = 1 := by
  have hf : far ∉ Finset.range (n + 1) := by simp; omega
  simp [prefixCurrent, dipole, Finset.sum_sub_distrib, hf]

theorem dipole_zero_total (far : ℕ) : prefixCurrent (dipole far) far = 0 := by
  simp [prefixCurrent, dipole, Finset.sum_sub_distrib]

theorem arbitrarily_remote_tree_response (radius : ℕ) :
    prefixCurrent (dipole (2 * radius + 3)) (radius + 1) = 1 := by
  apply dipole_current
  omega

end LongRange

#print axioms pathFrame_gauge
#print axioms dressing_gauge
#print axioms dressedLink_gauge
#print axioms dressedLink_based_invariant
#print axioms dressedLink_reconstructs
#print axioms treeLink_is_one
#print axioms dressedLink_abelian_invariant
#print axioms weylMatrix_dressing
#print axioms weylDet_dressing
#print axioms weylDet_basis_change
#print axioms frame_connection_dressing
#print axioms measure_connection_dressing
#print axioms horizontal_kills_gauge
#print axioms constructed_current_ward
#print axioms ward_current_complete
#print axioms prefixCurrent_first
#print axioms prefixCurrent_divergence
#print axioms prefixCurrent_last
#print axioms prefixCurrent_unique
#print axioms dipole_current
#print axioms dipole_zero_total
#print axioms arbitrarily_remote_tree_response

end
end UnifiedTheory.Audit.KFCausalGaugeDressedMeasure
