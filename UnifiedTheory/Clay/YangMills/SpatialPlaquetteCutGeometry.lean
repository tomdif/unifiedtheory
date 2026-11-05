/- Classification and exact action reflection for the link-plane spatial cut.
Both periodic seams are included. Interior plaquettes have all four vertices
on one side; a plaquette changing side is a normal crossing fixed by reflection. -/
import UnifiedTheory.Clay.YangMills.SpatialPlaquetteHalfPaths

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SpatialPlaquetteCutGeometry
noncomputable section
open WilsonTimeSlab SpatialHalfEdgeGeometry SpatialHalfEdgeSplit RegulatedGauge

variable (n : ℕ) [NeZero n]

def VertexPositive (x : SpatialVertex (2 * n)) : Prop := (x 0).val < n

omit [NeZero n] in
theorem tangent_side (x : SpatialVertex (2 * n)) (j : Fin 3) (hj : j ≠ 0) :
    VertexPositive n (spatialStep (2 * n) x j) ↔ VertexPositive n x := by
  simp [VertexPositive, spatialStep, hj]

theorem normal_partition (x : SpatialVertex (2 * n)) :
    (VertexPositive n x ↔ VertexPositive n (spatialStep (2 * n) x 0)) ∨
      reflectVertex (2 * n) x = spatialStep (2 * n) x 0 := by
  have hn := NeZero.pos n
  have ht := (x 0).val_lt
  have hs : (spatialStep (2 * n) x 0 0).val = ((x 0).val + 1) % (2 * n) := by
    simp [spatialStep, ZMod.val_add, ZMod.val_one'' (show 2 * n ≠ 1 by omega)]
  have hr : (reflectVertex (2 * n) x 0).val = 2 * n - 1 - (x 0).val := by
    exact PeriodicHalfGeometry.val_neg_add_one (2 * n) (x 0)
  by_cases hw : (x 0).val + 1 < 2 * n
  · rw [Nat.mod_eq_of_lt hw] at hs
    by_cases hm : (x 0).val + 1 = n
    · right
      funext j
      by_cases hj : j = 0
      · subst j
        apply ZMod.val_injective
        rw [hr, hs]
        omega
      · simp [reflectVertex, spatialStep, hj]
    · left
      unfold VertexPositive
      rw [hs]
      omega
  · have hm : (x 0).val + 1 = 2 * n := by omega
    rw [hm, Nat.mod_self] at hs
    right
    funext j
    by_cases hj : j = 0
    · subst j
      apply ZMod.val_injective
      rw [hr, hs]
      omega
    · simp [reflectVertex, spatialStep, hj]

abbrev Plaquette := SpatialVertex (2 * n) × SpatialPlane

def reflectPlaquette (p : Plaquette n) : Plaquette n :=
  ((reflectLink (2 * n) (p.1,p.2.val.1)).1,p.2)

omit [NeZero n] in
theorem reflectPlaquette_involutive : Function.Involutive (reflectPlaquette n) := by
  rintro ⟨x,p⟩
  have h := congrArg Prod.fst (reflectLink_involutive (2 * n) (x,p.val.1))
  exact Prod.ext h rfl

def plaquetteEquiv : Plaquette n ≃ Plaquette n :=
  (reflectPlaquette_involutive n).toPerm

variable (G : Type*) [Group G]

omit [NeZero n] in
theorem reflected_tangent (u : SpatialLinks (2 * n) G) (x : SpatialVertex (2 * n))
    (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) :
    spatialHolonomy (reflection n G u) x i j =
      spatialHolonomy u (reflectVertex (2 * n) x) i j := by
  simp [spatialHolonomy, reflection, reflectLink, hi, hj,
    reflectVertex_step_tangent (2 * n) x i hi,
    reflectVertex_step_tangent (2 * n) x j hj]

omit [NeZero n] in
theorem reflected_normal (u : SpatialLinks (2 * n) G) (x : SpatialVertex (2 * n))
    (j : Fin 3) (hj : j ≠ 0) :
    spatialHolonomy (reflection n G u) x 0 j =
      (u (reflectVertex (2 * n) (spatialStep (2 * n) x 0),0))⁻¹ *
      (spatialHolonomy u (reflectVertex (2 * n) (spatialStep (2 * n) x 0)) 0 j)⁻¹ *
      u (reflectVertex (2 * n) (spatialStep (2 * n) x 0),0) := by
  have hc : reflectVertex (2 * n) (spatialStep (2 * n) (spatialStep (2 * n) x j) 0) =
      spatialStep (2 * n) (reflectVertex (2 * n) (spatialStep (2 * n) x 0)) j := by
    rw [WilsonSlabGauge.spatialStep_comm, reflectVertex_step_tangent (2 * n) _ j hj]
  simp only [spatialHolonomy, reflection, reflectLink, ↓reduceIte, if_neg hj,
    hc, reflectVertex_step_normal]
  group

omit [NeZero n] in
theorem character_reflection (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ q, (χ q⁻¹).re = (χ q).re) (u : SpatialLinks (2 * n) G) (p : Plaquette n) :
    (χ (spatialHolonomy (reflection n G u) p.1 p.2.val.1 p.2.val.2)).re =
      (χ (spatialHolonomy u (reflectPlaquette n p).1 p.2.val.1 p.2.val.2)).re := by
  rcases p with ⟨x,⟨⟨i,j⟩,hij⟩⟩
  have hj : j ≠ 0 := by intro h; subst j; exact (not_lt_of_ge (Fin.zero_le i)) hij
  by_cases hi : i = 0
  · subst i
    simp only [reflectPlaquette, reflectLink, ↓reduceIte]
    rw [reflected_normal n G u x j hj]
    have hc := hχ (u (reflectVertex (2 * n) (spatialStep (2 * n) x 0),0))⁻¹
      (spatialHolonomy u (reflectVertex (2 * n) (spatialStep (2 * n) x 0)) 0 j)⁻¹
    simp only [inv_inv] at hc
    rw [hc, hinv]
  · simp only [reflectPlaquette, reflectLink, if_neg hi]
    rw [reflected_tangent n G u x i j hi hj]

theorem potential_reflection (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ q, (χ q⁻¹).re = (χ q).re) (c : ℝ) (u : SpatialLinks (2 * n) G) :
    potential χ c (reflection n G u) = potential χ c u := by
  calc
    _ = ∑ p : Plaquette n,
        (c - (χ (spatialHolonomy (reflection n G u) p.1 p.2.val.1 p.2.val.2)).re) := by
      simp only [Fintype.sum_prod_type, potential]
    _ = ∑ p : Plaquette n,
        (c - (χ (spatialHolonomy u (reflectPlaquette n p).1 p.2.val.1 p.2.val.2)).re) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [character_reflection n G χ hχ hinv u p]
    _ = _ := (Equiv.sum_comp (plaquetteEquiv n)
      (fun p => c - (χ (spatialHolonomy u p.1 p.2.val.1 p.2.val.2)).re)).trans (by
        simp only [Fintype.sum_prod_type, potential])

end
end UnifiedTheory.Clay.YangMills.SpatialPlaquetteCutGeometry
