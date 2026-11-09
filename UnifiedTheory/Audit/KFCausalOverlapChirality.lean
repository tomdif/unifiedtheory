/-
  A boundary on fixed momentum filters, and the overlap chiral algebra.
  The overlap construction is a Euclidean regulator, not a completed
  real-time Weyl gauge theory. Its fermion measure, anomaly cancellation,
  dynamical fields, and gravity are not supplied by these identities.
-/
import UnifiedTheory.Audit.KFCausalGaugeWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalOverlapChirality
noncomputable section
open scoped BigOperators

section OverlapAlgebra
variable {R : Type*} [Ring R] [StarRing R]

def overlap (g e : R) : R := 1 + g * e
def chirality (g D : R) : R := g * (1 - D)

omit [StarRing R] in
theorem overlap_gw (g e : R) (hg : g * g = 1) (he : e * e = 1) :
    g * overlap g e + overlap g e * g = overlap g e * g * overlap g e := by
  have hc (x : R) : g * (g * x) = x := by rw [← mul_assoc, hg, one_mul]
  simp only [overlap, mul_add, add_mul, one_mul, mul_one, mul_assoc, hc, he]
  abel

theorem overlap_gammaHermitian (g e : R) (hgs : star g = g) (hes : star e = e)
    (hg : g * g = 1) : star (overlap g e) = g * overlap g e * g := by
  simp only [overlap, star_add, star_one, star_mul, hgs, hes,
    mul_add, add_mul, one_mul, mul_one, ← mul_assoc, hg]

theorem overlap_polar_unitary (g e : R) (hgs : star g = g) (hes : star e = e)
    (hg : g * g = 1) (he : e * e = 1) : star (g * e) * (g * e) = 1 := by
  simp only [star_mul, hgs, hes]
  calc
    _ = e * (g * g) * e := by noncomm_ring
    _ = 1 := by rw [hg, mul_one, he]

omit [StarRing R] in
theorem overlap_chirality (g e : R) (hg : g * g = 1) :
    chirality g (overlap g e) = -e := by
  simp [chirality, overlap, ← mul_assoc, hg]

omit [StarRing R] in
theorem chirality_square (g e : R) (hg : g * g = 1) (he : e * e = 1) :
    chirality g (overlap g e) * chirality g (overlap g e) = 1 := by
  rw [overlap_chirality g e hg]
  simpa using he

theorem chirality_selfadjoint (g e : R) (hg : g * g = 1) (hes : star e = e) :
    star (chirality g (overlap g e)) = chirality g (overlap g e) := by
  simp [overlap_chirality g e hg, hes]

omit [StarRing R] in
/-- The deformed chirality exchanges the domain and codomain chiral sectors. -/
theorem chirality_intertwining (g e : R) (hg : g * g = 1) (he : e * e = 1) :
    overlap g e * chirality g (overlap g e) = -g * overlap g e := by
  rw [overlap_chirality g e hg]
  have hc (x : R) : g * (g * x) = x := by rw [← mul_assoc, hg, one_mul]
  simp only [overlap, mul_neg, neg_mul, mul_add, add_mul, one_mul, mul_one,
    mul_assoc, he, hc]
  abel

open UnifiedTheory.Audit.KFCausalGaugeWalk (conjugate)

theorem overlap_covariant (g e U : R) (hcomm : g * U = U * g)
    (hU : U * star U = 1) :
    overlap g (conjugate U e) = conjugate U (overlap g e) := by
  simp only [overlap, conjugate, mul_add, add_mul, mul_one,
    ← mul_assoc, hcomm, hU]

theorem chirality_covariant (g D U : R) (hcomm : g * U = U * g)
    (hU : U * star U = 1) :
    chirality g (conjugate U D) = conjugate U (chirality g D) := by
  have hgu : U * g * star U = g := by rw [← hcomm, mul_assoc, hU, mul_one]
  simp only [chirality, conjugate, mul_sub, sub_mul, mul_one, ← mul_assoc, hcomm, hgu]
end OverlapAlgebra

open Matrix
section Projectors
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Operator" => Matrix ι ι ℂ

def plus (J : Operator) : Operator := (1/2 : ℂ) • (1 + J)
def minus (J : Operator) : Operator := (1/2 : ℂ) • (1 - J)

theorem plus_square (J : Operator) (hJ : J * J = 1) : plus J * plus J = plus J := by
  simp only [plus, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hJ]
  module

theorem minus_square (J : Operator) (hJ : J * J = 1) : minus J * minus J = minus J := by
  simp only [minus, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hJ]
  module

theorem projectors_orthogonal (J : Operator) (hJ : J * J = 1) : plus J * minus J = 0 := by
  simp only [plus, minus, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hJ]
  module

omit [Fintype ι] in
theorem minus_selfadjoint (J : Operator) (hJ : Jᴴ = J) : (minus J)ᴴ = minus J := by
  simp [minus, Matrix.conjTranspose_smul, hJ]

theorem projectors_intertwine (g e : Operator) (hg : g * g = 1) (he : e * e = 1) :
    overlap g e * minus (chirality g (overlap g e)) = plus g * overlap g e := by
  simp only [minus, plus, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
    Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, chirality_intertwining g e hg he,
    Matrix.neg_mul, sub_neg_eq_add]

/-- Independent sign changes at each site are a subgroup of local U(1).
They already force a fixed commuting operator to have no inter-site entries. -/
def siteSign {site : Type*} [DecidableEq site] (record : ι → site) (x : site) : Operator :=
  Matrix.diagonal (fun i => if record i = x then (-1 : ℂ) else 1)

theorem siteSign_unitary {site : Type*} [DecidableEq site]
    (record : ι → site) (x : site) : (siteSign record x)ᴴ * siteSign record x = 1 := by
  unfold siteSign
  apply UnifiedTheory.Audit.KFCausalGaugeWalk.diagonal_left_unitary
  intro i
  split_ifs <;> norm_num

theorem fixed_filter_no_interSite {site : Type*} [DecidableEq site]
    (record : ι → site) (P : Operator)
    (hP : ∀ x, P * siteSign record x = siteSign record x * P)
    (i j : ι) (hij : record i ≠ record j) : P i j = 0 := by
  have h := congrFun (congrFun (hP (record i)) i) j
  have hji : record j ≠ record i := Ne.symm hij
  simp [siteSign, Matrix.mul_diagonal, Matrix.diagonal_mul, hji] at h
  linear_combination (1/2 : ℂ) * h
end Projectors

section FreeGap

def wilsonMass (a b c d : ℝ) : ℝ := a + b + c + d - 1

/-- For a_mu = 1-cos(q_mu), this is the exact free Wilson-kernel gap identity. -/
theorem free_gap_identity (a b c d : ℝ) :
    (2*a-a^2) + (2*b-b^2) + (2*c-c^2) + (2*d-d^2) + wilsonMass a b c d ^ 2 =
      1 + 2 * (a*b + a*c + a*d + b*c + b*d + c*d) := by
  unfold wilsonMass
  ring

theorem free_gap_lower (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    1 ≤ (2*a-a^2) + (2*b-b^2) + (2*c-c^2) + (2*d-d^2) + wilsonMass a b c d ^ 2 := by
  rw [free_gap_identity]
  have hp : 0 ≤ a*b + a*c + a*d + b*c + b*d + c*d := by positivity
  linarith

theorem free_trig_gap (x y z t : ℝ) :
    1 ≤ Real.sin x ^ 2 + Real.sin y ^ 2 + Real.sin z ^ 2 + Real.sin t ^ 2 +
      wilsonMass (1-Real.cos x) (1-Real.cos y) (1-Real.cos z) (1-Real.cos t) ^ 2 := by
  have hs (u : ℝ) : Real.sin u ^ 2 = 2*(1-Real.cos u)-(1-Real.cos u)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  rw [hs x, hs y, hs z, hs t]
  exact free_gap_lower _ _ _ _ (sub_nonneg.mpr (Real.cos_le_one x))
    (sub_nonneg.mpr (Real.cos_le_one y)) (sub_nonneg.mpr (Real.cos_le_one z))
    (sub_nonneg.mpr (Real.cos_le_one t))

theorem free_gap_upper (a b c d : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha2 : a ≤ 2) (hb2 : b ≤ 2) (hc2 : c ≤ 2) (hd2 : d ≤ 2) :
    (2*a-a^2) + (2*b-b^2) + (2*c-c^2) + (2*d-d^2) + wilsonMass a b c d ^ 2 ≤ 49 := by
  have bound (u v : ℝ) (hv : 0 ≤ v) (hu2 : u ≤ 2) (hv2 : v ≤ 2) : u*v ≤ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hu2 hv]
  rw [free_gap_identity]
  linarith [bound a b hb ha2 hb2, bound a c hc ha2 hc2, bound a d hd ha2 hd2,
    bound b c hc hb2 hc2, bound b d hd hb2 hd2, bound c d hd hc2 hd2]

theorem nonzero_corner_mass (n : ℕ) (hn : 1 ≤ n) : 0 < (2 : ℝ) * n - 1 := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- Under a gap, the positive scalar in D†D can vanish only when all sine
components vanish and the Wilson mass has negative sign. -/
theorem pole_scalar_iff (B w s0 s1 s2 s3 : ℝ) (hw : 0 < w)
    (hs : w ^ 2 = s0 ^ 2 + s1 ^ 2 + s2 ^ 2 + s3 ^ 2 + B ^ 2) :
    1 + B/w = 0 ↔ s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0 ∧ B < 0 := by
  constructor
  · intro hz
    have hb : B = -w := by
      have hh := (div_eq_iff (ne_of_gt hw)).mp (show B/w = -1 by linarith)
      linarith
    have hsum : s0 ^ 2 + s1 ^ 2 + s2 ^ 2 + s3 ^ 2 = 0 := by nlinarith
    have h0 : s0 = 0 := by nlinarith [sq_nonneg s1, sq_nonneg s2, sq_nonneg s3]
    have h1 : s1 = 0 := by nlinarith [sq_nonneg s0, sq_nonneg s2, sq_nonneg s3]
    have h2 : s2 = 0 := by nlinarith [sq_nonneg s0, sq_nonneg s1, sq_nonneg s3]
    have h3 : s3 = 0 := by nlinarith [sq_nonneg s0, sq_nonneg s1, sq_nonneg s2]
    exact ⟨h0, h1, h2, h3, by linarith⟩
  · rintro ⟨rfl, rfl, rfl, rfl, hB⟩
    have hb : B = -w := by nlinarith
    rw [hb, neg_div, div_self (ne_of_gt hw)]
    ring
end FreeGap

#print axioms overlap_gw
#print axioms overlap_gammaHermitian
#print axioms overlap_polar_unitary
#print axioms overlap_chirality
#print axioms chirality_square
#print axioms chirality_selfadjoint
#print axioms chirality_intertwining
#print axioms overlap_covariant
#print axioms chirality_covariant
#print axioms plus_square
#print axioms minus_square
#print axioms projectors_orthogonal
#print axioms minus_selfadjoint
#print axioms projectors_intertwine
#print axioms siteSign_unitary
#print axioms fixed_filter_no_interSite
#print axioms free_gap_identity
#print axioms free_gap_lower
#print axioms free_trig_gap
#print axioms free_gap_upper
#print axioms nonzero_corner_mass
#print axioms pole_scalar_iff

end
end UnifiedTheory.Audit.KFCausalOverlapChirality
