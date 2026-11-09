/- The reflection-plane source estimate applies to every translated spatial
plaquette in all three orientations, by exact Haar-preserving symmetries.
The original full ground and normalization are retained. -/
import UnifiedTheory.Clay.YangMills.WilsonSpatialRotations

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPlaquetteRelocation
noncomputable section
open WilsonTimeSlab WilsonSlabOperator SpatialPlaquetteCutGeometry SpatialWilsonPlaquetteKernels
open WilsonSpatialRotations WilsonRawSymmetry WilsonPhysicalVariance WilsonHighFieldDecay
open WilsonSingleLinkStaples (character)

variable (n : ℕ)

def cutBase : SpatialVertex (2 * n) := -Pi.single 0 1

def canonical : Plaquette n := (cutBase n, ⟨(0,1),by decide⟩)

theorem canonical_crossing : Crossing n (canonical n) := by
  refine ⟨rfl, ?_⟩
  funext j
  by_cases hj : j = 0
  · subst j
    simp [canonical, cutBase, SpatialHalfEdgeGeometry.reflectVertex, spatialStep]
  · simp [canonical, cutBase, SpatialHalfEdgeGeometry.reflectVertex, spatialStep, hj]

def planePermutation (p : SpatialPlane) : Equiv.Perm (Fin 3) :=
  (Equiv.swap 0 p.val.1).trans (Equiv.swap ((Equiv.swap 0 p.val.1) 1) p.val.2)

theorem permutation_zero (p : SpatialPlane) : planePermutation p 0 = p.val.1 := by
  rcases p with ⟨⟨i,j⟩,h⟩
  change i < j at h
  fin_cases i <;> fin_cases j <;> norm_num [planePermutation, Equiv.swap_apply_def] at * <;>
    exact False.elim (lt_irrefl _ h)

theorem permutation_one (p : SpatialPlane) : planePermutation p 1 = p.val.2 := by
  rcases p with ⟨⟨i,j⟩,h⟩
  change i < j at h
  fin_cases i <;> fin_cases j <;> norm_num [planePermutation, Equiv.swap_apply_def] at *

variable [NeZero n]

def relocation (q : Plaquette n) : Symmetry (2 * n) :=
  composition (2 * n)
    (translation (2 * n) (q.1 - vertexEquiv (2 * n) (planePermutation q.2) (cutBase n)))
    (rotation (2 * n) (planePermutation q.2))

theorem defect_relocation (q : Plaquette n) (u : Slice (2 * n)) :
    defect n (canonical n) ((relocation n q).map u) = defect n q u := by
  change (2 - (character (spatialHolonomy
    ((rotationEquiv (2 * n) (planePermutation q.2))
      (WilsonGroundTranslation.sliceEquiv (2 * n)
        (q.1 - vertexEquiv (2 * n) (planePermutation q.2) (cutBase n)) u))
    (cutBase n) 0 1)).re) = _
  rw [rotationEquiv_apply, WilsonGroundTranslation.sliceEquiv_apply,
    holonomy_rotate, WilsonGroundTranslation.spatialHolonomy_shift,
    permutation_zero, permutation_one]
  have he : vertexEquiv (2 * n) (planePermutation q.2) (cutBase n) +
      (q.1 - vertexEquiv (2 * n) (planePermutation q.2) (cutBase n)) = q.1 := by abel
  rw [he]
  rfl

/-- Supported decay at any spatial plaquette, with no orientation or seam premise. -/
theorem mass_decay (q : Plaquette n) (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ)
    (f : C(Slice (2 * n), ℝ)) (hs : ∀ u, defect n q u < R → f u = 0) :
    mass (2 * n) β (by linarith) (step (2 * n) β (by linarith) f) ≤
      WilsonPlaquetteColumnTail.rate β R * mass (2 * n) β (by linarith) f := by
  let S := relocation n q
  have hsupport (u : Slice (2 * n)) (hu : defect n (canonical n) u < R) :
      pull (2 * n) (inverse (2 * n) S) f u = 0 := by
    have he := defect_relocation n q (S.map.symm u)
    change defect n (canonical n) (S.map (S.map.symm u)) = _ at he
    rw [S.map.apply_symm_apply] at he
    exact hs (S.map.symm u) (he ▸ hu)
  have h := WilsonPlaquetteColumnDecay.mass_decay n (canonical n) (canonical_crossing n)
    β hβ R (pull (2 * n) (inverse (2 * n) S) f) hsupport
  simpa only [step_pull, mass_pull] using h

/-- Reversible output localization for arbitrary supported cutoffs at any plaquette. -/
theorem cutoff_output (q : Plaquette n) (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ)
    (χ f : C(Slice (2 * n), ℝ)) (hχ : ∀ u, χ u ∈ Set.Icc 0 1)
    (hs : ∀ u, defect n q u < R → χ u = 0) :
    mass (2 * n) β (by linarith) (χ * step (2 * n) β (by linarith) f) ≤
      WilsonPlaquetteColumnTail.rate β R * mass (2 * n) β (by linarith) f := by
  apply WilsonCutoffCover.cutoff_output (2 * n) β (by linarith) χ
    (WilsonPlaquetteColumnTail.rate β R) (WilsonPlaquetteColumnTail.rate_nonneg β R) hχ _ f
  intro g hg
  exact mass_decay n q β hβ R g (fun u hu => hg u (hs u hu))

end
end UnifiedTheory.Clay.YangMills.WilsonPlaquetteRelocation
