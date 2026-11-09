/- The actual site-reflection partition of forward links on period 2n.
Boundary links are spatial links on times 0 and n; each nonboundary link belongs
to exactly one half, and reflection pairs the halves with orientation reversal. -/
import UnifiedTheory.Clay.YangMills.PeriodicTimeReflection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PeriodicHalfGeometry
noncomputable section
open PeriodicLattice4 PeriodicTimeReflection

theorem val_neg_add_one (m : ℕ) [NeZero m] (t : ZMod m) :
    (-(t + 1)).val = m - 1 - t.val := by
  have ht := t.val_lt
  have hn : m - 1 - t.val + t.val + 1 = m := by omega
  have he : ((m - 1 - t.val : ℕ) : ZMod m) = -(t + 1) := by
    apply eq_neg_iff_add_eq_zero.mpr
    calc
      ((m - 1 - t.val : ℕ) : ZMod m) + (t + 1) =
          ((m - 1 - t.val : ℕ) : ZMod m) + ((t.val : ZMod m) + 1) := by
        rw [ZMod.natCast_zmod_val]
      _ =
          (((m - 1 - t.val + t.val + 1 : ℕ)) : ZMod m) := by push_cast; ring
      _ = 0 := by rw [hn]; simp
  rw [← he, ZMod.val_natCast_of_lt (by omega)]

variable (n : ℕ) [NeZero n]

abbrev Index := Vertex (2 * n) × Fin 4

def Boundary (p : Index n) : Prop := p.2 ≠ 0 ∧ ((p.1 0).val = 0 ∨ (p.1 0).val = n)
def Positive (p : Index n) : Prop :=
  if p.2 = 0 then (p.1 0).val < n else 0 < (p.1 0).val ∧ (p.1 0).val < n

theorem reflected_time_val (x : Vertex (2 * n)) :
    ((reflectIndex (2 * n) (x, 0)).1 0).val = 2 * n - 1 - (x 0).val := by
  simpa [reflectIndex, reflectVertex, step] using val_neg_add_one (2 * n) (x 0)

omit [NeZero n] in
theorem reflected_spatial_zero (x : Vertex (2 * n)) (μ : Fin 4) (hμ : μ ≠ 0)
    (ht : (x 0).val = 0) : ((reflectIndex (2 * n) (x, μ)).1 0).val = 0 := by
  have hx : x 0 = 0 := (ZMod.val_eq_zero _).mp ht
  simp [reflectIndex, reflectVertex, hμ, hx]

theorem reflected_spatial_val (x : Vertex (2 * n)) (μ : Fin 4) (hμ : μ ≠ 0)
    (ht : (x 0).val ≠ 0) :
    ((reflectIndex (2 * n) (x, μ)).1 0).val = 2 * n - (x 0).val := by
  haveI : NeZero (x 0) := ⟨(ZMod.val_ne_zero _).mp ht⟩
  simp [reflectIndex, reflectVertex, hμ, ZMod.val_neg_of_ne_zero]

omit [NeZero n] in
theorem boundary_fixed (p : Index n) (hp : Boundary n p) : reflectIndex (2 * n) p = p := by
  rcases p with ⟨x, μ⟩
  have hv := (reflectVertex_fixed_iff n x).mpr hp.2
  simp [reflectIndex, hp.1, hv]

omit [NeZero n] in
theorem positive_not_boundary (p : Index n) (hp : Positive n p) : ¬ Boundary n p := by
  by_cases hμ : p.2 = 0
  · simp [Boundary, hμ]
  · simp only [Positive, if_neg hμ] at hp
    simp only [Boundary]
    omega

theorem positive_reflection_disjoint (p : Index n) (hp : Positive n p) :
    ¬ Positive n (reflectIndex (2 * n) p) := by
  rcases p with ⟨x, μ⟩
  have hn := NeZero.pos n
  have ht := (x 0).val_lt
  by_cases hμ : μ = 0
  · subst μ
    simp only [Positive, reflectIndex_direction, ↓reduceIte, reflected_time_val] at hp ⊢
    omega
  · have hpos : 0 < (x 0).val := (show 0 < (x 0).val ∧ (x 0).val < n from by
      simpa [Positive, hμ] using hp).1
    have hz : (x 0).val ≠ 0 := ne_of_gt hpos
    simp only [Positive, reflectIndex_direction, if_neg hμ] at hp ⊢
    rw [reflected_spatial_val n x μ hμ hz]
    omega

theorem half_partition (p : Index n) :
    Boundary n p ∨ Positive n p ∨ Positive n (reflectIndex (2 * n) p) := by
  rcases p with ⟨x, μ⟩
  have hn := NeZero.pos n
  have ht := (x 0).val_lt
  by_cases hμ : μ = 0
  · subst μ
    right
    simp only [Positive, reflectIndex_direction, ↓reduceIte, reflected_time_val]
    omega
  · by_cases hz : (x 0).val = 0
    · exact Or.inl ⟨hμ, Or.inl hz⟩
    · by_cases hm : (x 0).val = n
      · exact Or.inl ⟨hμ, Or.inr hm⟩
      · right
        simp only [Positive, reflectIndex_direction, if_neg hμ]
        rw [reflected_spatial_val n x μ hμ hz]
        omega

theorem fixed_iff_boundary (p : Index n) : reflectIndex (2 * n) p = p ↔ Boundary n p := by
  refine ⟨?_, boundary_fixed n p⟩
  intro he
  rcases half_partition n p with hb | hp | hp
  · exact hb
  · have hnot := positive_reflection_disjoint n p hp
    exact False.elim (hnot (he.symm ▸ hp))
  · rw [he] at hp
    exact False.elim ((positive_reflection_disjoint n p hp) (he.symm ▸ hp))

theorem nonboundary_nonpositive_reflect_positive (p : Index n)
    (hb : ¬ Boundary n p) (hp : ¬ Positive n p) : Positive n (reflectIndex (2 * n) p) := by
  rcases half_partition n p with h | h | h
  · exact False.elim (hb h)
  · exact False.elim (hp h)
  · exact h

end
end UnifiedTheory.Clay.YangMills.PeriodicHalfGeometry
