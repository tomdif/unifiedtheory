/- Locality of the actual coarsened links and plaquettes in the independent
half-edge coordinates. These are exact identities, without a decay estimate. -/
import UnifiedTheory.Clay.YangMills.SpatialPlaquetteCutGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialHalfEdgeLocality
noncomputable section
open WilsonTimeSlab SpatialHalfEdgeGeometry SpatialHalfEdgeSplit
open SpatialPlaquetteCutGeometry SpatialPlaquetteHalfPaths

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]

def sideHalf (a b : Half n G) (x : SpatialVertex (2 * n)) : Half n G := by
  classical
  exact if VertexPositive n x then a else b

omit [Group G] in
theorem join_on_side (a b : Half n G) (x : SpatialVertex (2 * n))
    (e : HalfEdge (2 * n)) (he : Positive n e ↔ VertexPositive n x) :
    join n G (a,b) e = join n G (sideHalf n G a b x,sideHalf n G a b x) e := by
  classical
  by_cases hx : VertexPositive n x
  · have hp := he.mpr hx
    simp only [sideHalf, if_pos hx]
    exact (join_positive n G (a,b) ⟨e,hp⟩).trans
      (join_positive n G (a,a) ⟨e,hp⟩).symm
  · have hp : Positive n (reflectHalf (2 * n) e) :=
      (positive_reflected_iff n e).mpr (mt he.mp hx)
    have h1 := join_negative n G (a,b) ⟨reflectHalf (2 * n) e,hp⟩
    have h2 := join_negative n G (b,b) ⟨reflectHalf (2 * n) e,hp⟩
    simp only [reflectHalf_involutive (2 * n) e] at h1 h2
    simpa only [sideHalf, if_neg hx] using h1.trans h2.symm

theorem link_on_side (a b : Half n G) (x y : SpatialVertex (2 * n)) (k : Fin 3)
    (hy : VertexPositive n y ↔ VertexPositive n x)
    (hk : VertexPositive n (spatialStep (2 * n) y k) ↔ VertexPositive n x) :
    assemble n G (a,b) (y,k) =
      assemble n G (sideHalf n G a b x,sideHalf n G a b x) (y,k) := by
  unfold assemble HaarHalfEdges.coarsen
  rw [join_on_side n G a b x (Sum.inl (y,k)) hy,
    join_on_side n G a b x (Sum.inr (y,k)) hk]

theorem holonomy_on_side (a b : Half n G) (x : SpatialVertex (2 * n))
    (i j : Fin 3) (hj : j ≠ 0)
    (hi : VertexPositive n (spatialStep (2 * n) x i) ↔ VertexPositive n x) :
    spatialHolonomy (assemble n G (a,b)) x i j =
      spatialHolonomy (assemble n G (sideHalf n G a b x,sideHalf n G a b x)) x i j := by
  have hji := (tangent_side n (spatialStep (2 * n) x i) j hj).trans hi
  have hij : VertexPositive n (spatialStep (2 * n) (spatialStep (2 * n) x j) i) ↔
      VertexPositive n x := by
    rw [WilsonSlabGauge.spatialStep_comm]
    exact hji
  unfold spatialHolonomy
  rw [link_on_side n G a b x x i Iff.rfl hi,
    link_on_side n G a b x (spatialStep (2 * n) x i) j hi hji,
    link_on_side n G a b x (spatialStep (2 * n) x j) i (tangent_side n x j hj) hij,
    link_on_side n G a b x x j Iff.rfl (tangent_side n x j hj)]

theorem startPath_on_side (a b : Half n G) (x : SpatialVertex (2 * n))
    (j : Fin 3) (hj : j ≠ 0) :
    startPath (2 * n) G (join n G (a,b)) x j =
      halfPath G n x j (sideHalf n G a b x) := by
  unfold startPath halfPath HaarHalfEdges.coarsen
  rw [join_on_side n G a b x (Sum.inl (x,0)) Iff.rfl,
    join_on_side n G a b x (Sum.inl (x,j)) Iff.rfl,
    join_on_side n G a b x (Sum.inr (x,j)) (tangent_side n x j hj),
    join_on_side n G a b x (Sum.inl (spatialStep (2 * n) x j,0)) (tangent_side n x j hj)]
  rfl

theorem endPath_on_side (a b : Half n G) (x : SpatialVertex (2 * n))
    (j : Fin 3) (hj : j ≠ 0)
    (hc : reflectVertex (2 * n) x = spatialStep (2 * n) x 0) :
    endPath (2 * n) G (join n G (a,b)) x j =
      halfPath G n x j (sideHalf n G b a x) := by
  rw [← startPath_reflection (2 * n) G _ x j hj hc]
  have he : (fun e => join n G (a,b) (reflectHalf (2 * n) e)) = join n G (b,a) :=
    (funext (join_swap n G (a,b))).symm
  rw [he, startPath_on_side n G b a x j hj]

end
end UnifiedTheory.Clay.YangMills.SpatialHalfEdgeLocality
