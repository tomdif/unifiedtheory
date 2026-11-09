/- Exact midpoint path factorization of the actual spatial Wilson plaquette.
The boundary hypothesis is geometric and includes either periodic seam.
No gauge fixing or positivity of a modified ground state is assumed. -/
import UnifiedTheory.Clay.YangMills.SpatialHalfEdgeSplit
import UnifiedTheory.Clay.YangMills.SU2CrossingHaarFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SpatialPlaquetteHalfPaths
noncomputable section
open WilsonTimeSlab SpatialHalfEdgeGeometry SpatialHalfEdgeSplit RegulatedGauge

variable (N : ℕ) (G : Type*) [Group G]

def startPath (U : HalfEdge N → G) (x : SpatialVertex N) (j : Fin 3) : G :=
  (U (Sum.inl (x,0)))⁻¹ * HaarHalfEdges.coarsen G U (x,j) *
    U (Sum.inl (spatialStep N x j,0))

def endPath (U : HalfEdge N → G) (x : SpatialVertex N) (j : Fin 3) : G :=
  (U (Sum.inr (x,0)))⁻¹ * HaarHalfEdges.coarsen G U (spatialStep N x 0,j) *
    U (Sum.inr (spatialStep N x j,0))

theorem path_conjugacy (U : HalfEdge N → G) (x : SpatialVertex N) (j : Fin 3) :
    (startPath N G U x j)⁻¹ * endPath N G U x j =
      ((U (Sum.inl (spatialStep N x j,0)))⁻¹ *
          (HaarHalfEdges.coarsen G U (x,j))⁻¹) *
        spatialHolonomy (HaarHalfEdges.coarsen G U) x 0 j *
      ((U (Sum.inl (spatialStep N x j,0)))⁻¹ *
          (HaarHalfEdges.coarsen G U (x,j))⁻¹)⁻¹ := by
  unfold startPath endPath spatialHolonomy HaarHalfEdges.coarsen
  group

theorem path_character (χ : G → ℂ) (hχ : ClassFunction G χ)
    (U : HalfEdge N → G) (x : SpatialVertex N) (j : Fin 3) :
    χ ((startPath N G U x j)⁻¹ * endPath N G U x j) =
      χ (spatialHolonomy (HaarHalfEdges.coarsen G U) x 0 j) := by
  rw [path_conjugacy]
  exact hχ _ _

theorem boundary_link_fixed (x : SpatialVertex N)
    (hx : reflectVertex N x = spatialStep N x 0) : reflectLink N (x,0) = (x,0) := by
  have h := congrArg (reflectVertex N) hx
  rw [reflectVertex_involutive] at h
  simp [reflectLink, h.symm]

theorem boundary_tangent (x : SpatialVertex N) (j : Fin 3) (hj : j ≠ 0)
    (hx : reflectVertex N x = spatialStep N x 0) :
    reflectVertex N (spatialStep N x j) = spatialStep N (spatialStep N x j) 0 := by
  rw [reflectVertex_step_tangent N x j hj, hx, WilsonSlabGauge.spatialStep_comm]

theorem startPath_reflection (U : HalfEdge N → G) (x : SpatialVertex N)
    (j : Fin 3) (hj : j ≠ 0) (hx : reflectVertex N x = spatialStep N x 0) :
    startPath N G (fun e => U (reflectHalf N e)) x j = endPath N G U x j := by
  have he := boundary_link_fixed N x hx
  have he' := boundary_link_fixed N (spatialStep N x j) (boundary_tangent N x j hj hx)
  simp only [startPath, endPath, HaarHalfEdges.coarsen, reflectHalf,
    if_neg hj, he, he']
  simp [reflectLink, hj, hx]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem startPath_continuous (x : SpatialVertex N) (j : Fin 3) :
    Continuous (fun U : HalfEdge N → G => startPath N G U x j) := by
  unfold startPath HaarHalfEdges.coarsen
  fun_prop

variable (n : ℕ) [NeZero n]

def halfPath (x : SpatialVertex (2 * n)) (j : Fin 3) (a : Half n G) : G :=
  startPath (2 * n) G (join n G (a,a)) x j

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem startPath_join (a b : Half n G) (x : SpatialVertex (2 * n)) (j : Fin 3)
    (hj : j ≠ 0) (hx : (x 0).val < n) :
    startPath (2 * n) G (join n G (a,b)) x j = halfPath G n x j a := by
  have h : ∀ e, Positive n e → join n G (a,b) e = join n G (a,a) e := by
    intro e he
    exact (join_positive n G (a,b) ⟨e,he⟩).trans
      (join_positive n G (a,a) ⟨e,he⟩).symm
  unfold halfPath startPath HaarHalfEdges.coarsen
  rw [h (Sum.inl (x,0)) (by simpa [Positive, endpoint] using hx),
    h (Sum.inl (x,j)) (by simpa [Positive, endpoint] using hx),
    h (Sum.inr (x,j)) (by simpa [Positive, endpoint, spatialStep, hj] using hx),
    h (Sum.inl (spatialStep (2 * n) x j,0))
      (by simpa [Positive, endpoint, spatialStep, hj] using hx)]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem endPath_join (a b : Half n G) (x : SpatialVertex (2 * n)) (j : Fin 3)
    (hj : j ≠ 0) (hx : (x 0).val < n)
    (hc : reflectVertex (2 * n) x = spatialStep (2 * n) x 0) :
    endPath (2 * n) G (join n G (a,b)) x j = halfPath G n x j b := by
  rw [← startPath_reflection (2 * n) G _ x j hj hc]
  have he : (fun e => join n G (a,b) (reflectHalf (2 * n) e)) = join n G (b,a) :=
    (funext (join_swap n G (a,b))).symm
  rw [he, startPath_join G n b a x j hj hx]

theorem halfPath_continuous (x : SpatialVertex (2 * n)) (j : Fin 3) :
    Continuous (halfPath G n x j) :=
  (startPath_continuous (2 * n) G x j).comp
    ((join_continuous n G).comp (continuous_id.prodMk continuous_id))

end
end UnifiedTheory.Clay.YangMills.SpatialPlaquetteHalfPaths
