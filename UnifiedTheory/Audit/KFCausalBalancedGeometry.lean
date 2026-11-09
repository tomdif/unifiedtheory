/-
  The revised quantum-geometry candidate uses balanced elementary moves.
  These lemmas prove their polynomial/projection identities and the
  finite weighted-Laplacian quadratic form. Physical phase selection is open.
-/
import UnifiedTheory.Audit.KFCausalQuantumGeometryPhase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBalancedGeometry
noncomputable section
open scoped BigOperators

/-- The diagonal counterterm is part of the new Hamiltonian. -/
theorem balanced_move_square {A : Type*} [Ring A] (S : A) (hS : S ^ 3 = S) :
    (S ^ 2 - S) ^ 2 = 2 * (S ^ 2 - S) := by
  have h4 : S ^ 4 = S ^ 2 := by
    calc
      S ^ 4 = S ^ 3 * S := by rw [pow_succ]
      _ = S ^ 2 := by rw [hS, pow_two]
  have he : (S ^ 2 - S) ^ 2 = S ^ 4 - 2 * S ^ 3 + S ^ 2 := by noncomm_ring
  rw [he, h4, hS]
  noncomm_ring

theorem balanced_move_selfadjoint {A : Type*} [Ring A] [StarRing A]
    (S : A) (hS : star S = S) : star (S ^ 2 - S) = S ^ 2 - S := by
  simp [star_sub, star_pow, hS]

/-- For Hermitian S, the balanced operator is half its own adjoint square. -/
theorem balanced_move_gram {A : Type*} [Ring A] [StarRing A]
    (S : A) (hS : star S = S) (h3 : S ^ 3 = S) :
    star (S ^ 2 - S) * (S ^ 2 - S) = 2 * (S ^ 2 - S) := by
  rw [balanced_move_selfadjoint S hS, ← pow_two]
  exact balanced_move_square S h3

section Laplacian
variable {X : Type*} [Fintype X]

def laplacian (w : X → X → ℝ) (f : X → ℝ) (x : X) : ℝ :=
  ∑ y, w x y * (f x - f y)

theorem laplacian_constant (w : X → X → ℝ) (c : ℝ) (x : X) :
    laplacian w (fun _ => c) x = 0 := by
  simp [laplacian]

/-- Exact finite matrix quadratic form, not a state-count normalization. -/
theorem laplacian_quadratic (w : X → X → ℝ) (f : X → ℝ)
    (hsym : ∀ x y, w x y = w y x) :
    (∑ x, f x * laplacian w f x) =
      (∑ x, ∑ y, w x y * (f x - f y) ^ 2) / 2 := by
  have he : (∑ x, ∑ y, w x y * f y ^ 2) = ∑ x, ∑ y, w x y * f x ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun x _ =>
      Finset.sum_congr rfl (fun y _ => by rw [hsym y x]))
  simp only [laplacian, Finset.mul_sum, mul_sub]
  have hterm : ∀ x y, w x y * (f x - f y) ^ 2 =
      w x y * f x ^ 2 - 2 * (f x * (w x y * f y)) + w x y * f y ^ 2 := by
    intro x y
    ring
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [he]
  have hterm2 : ∀ x y, f x * (w x y * f x) = w x y * f x ^ 2 := by
    intro x y
    ring
  simp_rw [hterm2]
  simp only [← Finset.mul_sum]
  ring

theorem laplacian_nonnegative (w : X → X → ℝ) (f : X → ℝ)
    (hsym : ∀ x y, w x y = w y x) (hw : ∀ x y, 0 ≤ w x y) :
    0 ≤ ∑ x, f x * laplacian w f x := by
  rw [laplacian_quadratic w f hsym]
  exact div_nonneg (Finset.sum_nonneg (fun x _ => Finset.sum_nonneg
    (fun y _ => mul_nonneg (hw x y) (sq_nonneg _)))) (by norm_num)

/-- A zero-energy vector is constant along every positive-conductance edge. -/
theorem zero_energy_edge_equality (w : X → X → ℝ) (f : X → ℝ)
    (hw : ∀ x y, 0 ≤ w x y)
    (hz : (∑ x, ∑ y, w x y * (f x - f y) ^ 2) = 0)
    (a b : X) (hab : 0 < w a b) : f a = f b := by
  have hrow : ∀ x, (∑ y, w x y * (f x - f y) ^ 2) = 0 := by
    intro x
    exact ((Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Finset.sum_nonneg
      (fun y _ => mul_nonneg (hw x y) (sq_nonneg _)))).mp hz) x (by simp)
  have hentry : w a b * (f a - f b) ^ 2 = 0 := by
    exact ((Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => mul_nonneg (hw a y) (sq_nonneg _))).mp (hrow a)) b (by simp)
  have hs : (f a - f b) ^ 2 = 0 := (mul_eq_zero.mp hentry).resolve_left hab.ne'
  nlinarith [sq_nonneg (f a - f b)]

end Laplacian

/-- The previous two-state lowering mechanism is absent when removal costs energy. -/
theorem balanced_pair_energy (b δ x y : ℝ) (hb : 0 ≤ b) (hδ : 0 ≤ δ) :
    0 ≤ b * x ^ 2 - 2 * b * x * y + (b + δ) * y ^ 2 := by
  nlinarith [mul_nonneg hb (sq_nonneg (x - y)), mul_nonneg hδ (sq_nonneg y)]

/-- Conductance multiplicities must be added after balancing each elementary move. -/
theorem multiplicity_counterterm (c : ℝ) :
    c ^ 2 - c = c * (c - 1) := by ring

#print axioms balanced_move_square
#print axioms balanced_move_selfadjoint
#print axioms balanced_move_gram
#print axioms laplacian_constant
#print axioms laplacian_quadratic
#print axioms laplacian_nonnegative
#print axioms zero_energy_edge_equality
#print axioms balanced_pair_energy
#print axioms multiplicity_counterterm

end
end UnifiedTheory.Audit.KFCausalBalancedGeometry
