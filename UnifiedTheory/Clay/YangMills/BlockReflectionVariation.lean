/- Exact nearest-neighbor disagreement accounting for block labels on an
even three-dimensional torus. Reflection lowers the average variation
strictly when a cut crosses a disagreement. This is geometric bookkeeping;
identifying these labels with a Wilson block deletion family is separate. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonHalfCopies

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.BlockReflectionVariation
noncomputable section
open WilsonTimeSlab SpatialHalfEdgeGeometry SpatialPlaquetteCutGeometry
open SpatialWilsonHalfCopies

variable (n : ℕ) [NeZero n] {A : Type*} [DecidableEq A]

def positiveCopy (f : SpatialVertex (2 * n) → A) (x : SpatialVertex (2 * n)) : A := by
  classical
  exact if VertexPositive n x then f x else f (reflectVertex (2 * n) x)

def negativeCopy (f : SpatialVertex (2 * n) → A) (x : SpatialVertex (2 * n)) : A := by
  classical
  exact if VertexPositive n x then f (reflectVertex (2 * n) x) else f x

def edgeCost (f : SpatialVertex (2 * n) → A) (e : Link (2 * n)) : ℕ :=
  if f e.1 = f (spatialStep (2 * n) e.1 e.2) then 0 else 1

def variation (f : SpatialVertex (2 * n) → A) : ℕ := ∑ e, edgeCost n f e

def CrossEdge (e : Link (2 * n)) : Prop :=
  e.2 = 0 ∧ reflectVertex (2 * n) e.1 = spatialStep (2 * n) e.1 0

theorem edge_partition (e : Link (2 * n)) :
    (VertexPositive n (spatialStep (2 * n) e.1 e.2) ↔ VertexPositive n e.1) ∨ CrossEdge n e := by
  by_cases hi : e.2 = 0
  · rcases normal_partition n e.1 with h | h
    · left
      simpa only [hi] using h.symm
    · exact Or.inr ⟨hi,h⟩
  · exact Or.inl (tangent_side n e.1 e.2 hi)

omit [NeZero n] in
theorem reflected_cost (f : SpatialVertex (2 * n) → A) (e : Link (2 * n)) :
    edgeCost n (fun x => f (reflectVertex (2 * n) x)) e =
      edgeCost n f (reflectLink (2 * n) e) := by
  classical
  by_cases hi : e.2 = 0
  · simp only [edgeCost, reflectLink, hi, ↓reduceIte, reflectVertex_step_normal]
    simp only [eq_comm]
  · simp only [edgeCost, reflectLink, if_neg hi, reflectVertex_step_tangent _ _ _ hi]

omit [NeZero n] in
theorem interior_cost (f : SpatialVertex (2 * n) → A) (e : Link (2 * n))
    (he : VertexPositive n (spatialStep (2 * n) e.1 e.2) ↔ VertexPositive n e.1) :
    edgeCost n (positiveCopy n f) e + edgeCost n (negativeCopy n f) e =
      edgeCost n f e + edgeCost n f (reflectLink (2 * n) e) := by
  classical
  rw [← reflected_cost]
  by_cases hx : VertexPositive n e.1 <;>
    simp only [edgeCost, positiveCopy, negativeCopy, he, hx, ↓reduceIte, add_comm]

theorem crossing_cost (f : SpatialVertex (2 * n) → A) (e : Link (2 * n)) (he : CrossEdge n e) :
    edgeCost n (positiveCopy n f) e = 0 ∧ edgeCost n (negativeCopy n f) e = 0 := by
  classical
  have hs : VertexPositive n (spatialStep (2 * n) e.1 e.2) ↔ ¬ VertexPositive n e.1 := by
    rw [he.1, ← he.2]
    exact vertex_reflected_side n e.1
  have hr : reflectVertex (2 * n) (spatialStep (2 * n) e.1 e.2) = e.1 := by
    rw [he.1, ← he.2, reflectVertex_involutive (2 * n) e.1]
  have hv : reflectVertex (2 * n) e.1 = spatialStep (2 * n) e.1 e.2 := by rw [he.1, he.2]
  by_cases hx : VertexPositive n e.1 <;>
    simp [edgeCost, positiveCopy, negativeCopy, hs, hx, hr, hv]

theorem cost_le (f : SpatialVertex (2 * n) → A) (e : Link (2 * n)) :
    edgeCost n (positiveCopy n f) e + edgeCost n (negativeCopy n f) e ≤
      edgeCost n f e + edgeCost n f (reflectLink (2 * n) e) := by
  rcases edge_partition n e with he | he
  · exact (interior_cost n f e he).le
  · rw [(crossing_cost n f e he).1, (crossing_cost n f e he).2]
    exact Nat.zero_le _

theorem cost_strict (f : SpatialVertex (2 * n) → A) (e : Link (2 * n))
    (he : CrossEdge n e) (hd : f e.1 ≠ f (spatialStep (2 * n) e.1 e.2)) :
    edgeCost n (positiveCopy n f) e + edgeCost n (negativeCopy n f) e <
      edgeCost n f e + edgeCost n f (reflectLink (2 * n) e) := by
  rw [(crossing_cost n f e he).1, (crossing_cost n f e he).2]
  have h : edgeCost n f e = 1 := if_neg hd
  rw [h]
  omega

theorem reflected_sum (f : SpatialVertex (2 * n) → A) :
    ∑ e, edgeCost n f (reflectLink (2 * n) e) = variation n f :=
  Equiv.sum_comp ((reflectLink_involutive (2 * n)).toPerm) (edgeCost n f)

theorem variation_le (f : SpatialVertex (2 * n) → A) :
    variation n (positiveCopy n f) + variation n (negativeCopy n f) ≤ 2 * variation n f := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun e _ => cost_le n f e)
  simpa only [Finset.sum_add_distrib, reflected_sum, variation, two_mul] using h

/-- The strict decrease needed in the chessboard extremal argument. -/
theorem variation_strict (f : SpatialVertex (2 * n) → A) (e : Link (2 * n))
    (he : CrossEdge n e) (hd : f e.1 ≠ f (spatialStep (2 * n) e.1 e.2)) :
    variation n (positiveCopy n f) + variation n (negativeCopy n f) < 2 * variation n f := by
  have h := Finset.sum_lt_sum (fun q (_ : q ∈ (Finset.univ : Finset (Link (2 * n)))) =>
    cost_le n f q) ⟨e,Finset.mem_univ _,cost_strict n f e he hd⟩
  simpa only [Finset.sum_add_distrib, reflected_sum, variation, two_mul] using h

omit [NeZero n] [DecidableEq A] in
theorem step_iterate (f : SpatialVertex (2 * n) → A)
    (h : ∀ x j, f (spatialStep (2 * n) x j) = f x)
    (x : SpatialVertex (2 * n)) (j : Fin 3) (k : ℕ) :
    f (x + Pi.single j (k : ZMod (2 * n))) = f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : x + Pi.single j ((k + 1 : ℕ) : ZMod (2 * n)) =
        spatialStep (2 * n) (x + Pi.single j (k : ZMod (2 * n))) j := by
      simp only [Nat.cast_add, Nat.cast_one, Pi.single_add, spatialStep]
      abel
    rw [he, h, ih]

omit [DecidableEq A] in
theorem coordinate_shift (f : SpatialVertex (2 * n) → A)
    (h : ∀ x j, f (spatialStep (2 * n) x j) = f x)
    (x : SpatialVertex (2 * n)) (j : Fin 3) (z : ZMod (2 * n)) :
    f (x + Pi.single j z) = f x := by
  simpa only [ZMod.natCast_zmod_val] using step_iterate n f h x j z.val

omit [DecidableEq A] in
theorem constant_of_step (f : SpatialVertex (2 * n) → A)
    (h : ∀ x j, f (spatialStep (2 * n) x j) = f x)
    (x y : SpatialVertex (2 * n)) : f x = f y := by
  have he : x = ((y + Pi.single 0 (x 0 - y 0)) + Pi.single 1 (x 1 - y 1)) +
      Pi.single 2 (x 2 - y 2) := by
    funext j
    fin_cases j <;> simp
  rw [he, coordinate_shift n f h, coordinate_shift n f h, coordinate_shift n f h]

theorem variation_zero_iff (f : SpatialVertex (2 * n) → A) :
    variation n f = 0 ↔ ∀ x y, f x = f y := by
  constructor
  · intro hz
    apply constant_of_step n f
    intro x j
    have he : edgeCost n f (x,j) = 0 :=
      (Finset.sum_eq_zero_iff.mp hz) (x,j) (Finset.mem_univ _)
    unfold edgeCost at he
    split_ifs at he with h
    exact h.symm
  · intro h
    exact Finset.sum_eq_zero (fun e _ => if_pos (h e.1 (spatialStep (2 * n) e.1 e.2)))

theorem exists_disagreement (f : SpatialVertex (2 * n) → A) (h : 0 < variation n f) :
    ∃ e : Link (2 * n), f e.1 ≠ f (spatialStep (2 * n) e.1 e.2) := by
  by_contra! hn
  have hc := constant_of_step n f (fun x j => (hn (x,j)).symm)
  have hz := (variation_zero_iff n f).mpr hc
  omega

end
end UnifiedTheory.Clay.YangMills.BlockReflectionVariation
