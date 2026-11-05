/- Translation and coordinate permutation of block labels preserve their
actual nearest-neighbor variation. Every disagreeing edge can be moved to
the canonical reflection seam. -/
import UnifiedTheory.Clay.YangMills.BlockReflectionVariation
import UnifiedTheory.Clay.YangMills.WilsonSpatialRotations

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.BlockLabelSymmetry
noncomputable section
open WilsonTimeSlab SpatialHalfEdgeGeometry WilsonSpatialRotations BlockReflectionVariation

variable (n : ℕ) [NeZero n] {A : Type*} [DecidableEq A]

def vertexFrame (σ : Equiv.Perm (Fin 3)) (s : SpatialVertex (2 * n)) :
    SpatialVertex (2 * n) ≃ SpatialVertex (2 * n) :=
  (vertexEquiv (2 * n) σ).trans (Equiv.addRight s)

def edgeFrame (σ : Equiv.Perm (Fin 3)) (s : SpatialVertex (2 * n)) :
    Link (2 * n) ≃ Link (2 * n) := Equiv.prodCongr (vertexFrame n σ s) σ

def pull (σ : Equiv.Perm (Fin 3)) (s : SpatialVertex (2 * n))
    (f : SpatialVertex (2 * n) → A) (x : SpatialVertex (2 * n)) : A := f (vertexFrame n σ s x)

omit [NeZero n] in
theorem frame_step (σ : Equiv.Perm (Fin 3)) (s x : SpatialVertex (2 * n)) (j : Fin 3) :
    vertexFrame n σ s (spatialStep (2 * n) x j) =
      spatialStep (2 * n) (vertexFrame n σ s x) (σ j) := by
  change vertexEquiv (2 * n) σ (spatialStep (2 * n) x j) + s = _
  rw [vertex_step, WilsonGroundTranslation.step_add]
  rfl

omit [NeZero n] in
theorem cost_pull (σ : Equiv.Perm (Fin 3)) (s : SpatialVertex (2 * n))
    (f : SpatialVertex (2 * n) → A) (e : Link (2 * n)) :
    edgeCost n (pull n σ s f) e = edgeCost n f (edgeFrame n σ s e) := by
  simp only [edgeCost, pull, frame_step, edgeFrame, Equiv.prodCongr_apply]
  rfl

theorem variation_pull (σ : Equiv.Perm (Fin 3)) (s : SpatialVertex (2 * n))
    (f : SpatialVertex (2 * n) → A) : variation n (pull n σ s f) = variation n f := by
  simp only [variation, cost_pull]
  exact Equiv.sum_comp (edgeFrame n σ s) (edgeCost n f)

def seamVertex : SpatialVertex (2 * n) := Pi.single 0 (-1)

omit [NeZero n] in
theorem seam_crossing : CrossEdge n (seamVertex n,0) := by
  refine ⟨rfl,?_⟩
  funext j
  by_cases hj : j = 0
  · subst j
    simp [seamVertex, reflectVertex, spatialStep]
  · simp [seamVertex, reflectVertex, spatialStep, hj]

omit [NeZero n] [DecidableEq A] in
theorem move_disagreement (f : SpatialVertex (2 * n) → A) (e : Link (2 * n))
    (hd : f e.1 ≠ f (spatialStep (2 * n) e.1 e.2)) :
    ∃ (σ : Equiv.Perm (Fin 3)) (s : SpatialVertex (2 * n)),
      pull n σ s f (seamVertex n) ≠ pull n σ s f (spatialStep (2 * n) (seamVertex n) 0) := by
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 e.2
  let s := e.1 - vertexEquiv (2 * n) σ (seamVertex n)
  have hσ : σ 0 = e.2 := Equiv.swap_apply_left _ _
  have hv : vertexFrame n σ s (seamVertex n) = e.1 := by
    change vertexEquiv (2 * n) σ (seamVertex n) + (e.1 - vertexEquiv (2 * n) σ (seamVertex n)) = _
    abel
  refine ⟨σ,s,?_⟩
  simpa only [pull, frame_step, hv, hσ] using hd

end
end UnifiedTheory.Clay.YangMills.BlockLabelSymmetry
