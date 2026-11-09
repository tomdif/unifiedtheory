/- Exact spatial frames for arbitrary plaquette profiles. The plaquette
permutation is carried together with the Haar-preserving field symmetry;
orientation reversal is handled by the actual SU(2) defect identity. -/
import UnifiedTheory.Clay.YangMills.WilsonSpatialRotations
import UnifiedTheory.Clay.YangMills.SpatialWilsonHalfCopies

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPlaquetteFrames
noncomputable section
open WilsonTimeSlab WilsonSlabOperator SpatialPlaquetteCutGeometry
open SpatialWilsonPlaquetteKernels WilsonSingleLinkStaples WilsonSpatialRotations

def planeMap (σ : Equiv.Perm (Fin 3)) (p : SpatialPlane) : SpatialPlane :=
  if h : σ p.val.1 < σ p.val.2 then ⟨(σ p.val.1,σ p.val.2),h⟩
  else ⟨(σ p.val.2,σ p.val.1),lt_of_le_of_ne (le_of_not_gt h)
    (σ.injective.ne (ne_of_lt p.property)).symm⟩

theorem planeMap_inverse : ∀ (σ : Equiv.Perm (Fin 3)) (p : SpatialPlane),
    planeMap σ.symm (planeMap σ p) = p := by decide

def planeEquiv (σ : Equiv.Perm (Fin 3)) : SpatialPlane ≃ SpatialPlane where
  toFun := planeMap σ
  invFun := planeMap σ.symm
  left_inv := planeMap_inverse σ
  right_inv := by simpa only [Equiv.symm_symm] using planeMap_inverse σ.symm

theorem plane_defect (N : ℕ) (σ : Equiv.Perm (Fin 3)) (u : Slice N)
    (x : SpatialVertex N) (p : SpatialPlane) :
    orientedDefect N u x (σ p.val.1) (σ p.val.2) =
      orientedDefect N u x (planeEquiv σ p).val.1 (planeEquiv σ p).val.2 := by
  change _ = orientedDefect N u x (planeMap σ p).val.1 (planeMap σ p).val.2
  unfold planeMap
  split_ifs
  · rfl
  · exact defect_swap N u x (σ p.val.2) (σ p.val.1)

variable (n : ℕ) [NeZero n]

structure Frame where
  symmetry : WilsonRawSymmetry.Symmetry (2 * n)
  plaquettes : Plaquette n ≃ Plaquette n
  defect_map : ∀ (p : Plaquette n) (u : Slice (2 * n)),
    defect n p (symmetry.map u) = defect n (plaquettes p) u
  kinetic_map : ∀ (β : ℝ) (u v : Slice (2 * n)),
    kineticWeight character β 2 (symmetry.map u) (symmetry.map v) =
      kineticWeight character β 2 u v

def inverse (F : Frame n) : Frame n where
  symmetry := WilsonRawSymmetry.inverse (2 * n) F.symmetry
  plaquettes := F.plaquettes.symm
  defect_map p u := by
    have h := F.defect_map (F.plaquettes.symm p) (F.symmetry.map.symm u)
    simpa only [MeasurableEquiv.apply_symm_apply, Equiv.apply_symm_apply] using h.symm
  kinetic_map β u v := by
    have h := F.kinetic_map β (F.symmetry.map.symm u) (F.symmetry.map.symm v)
    simpa only [MeasurableEquiv.apply_symm_apply] using h.symm

def composition (F G : Frame n) : Frame n where
  symmetry := WilsonRawSymmetry.composition (2 * n) F.symmetry G.symmetry
  plaquettes := G.plaquettes.trans F.plaquettes
  defect_map p u := (G.defect_map p (F.symmetry.map u)).trans (F.defect_map (G.plaquettes p) u)
  kinetic_map β u v := (G.kinetic_map β (F.symmetry.map u) (F.symmetry.map v)).trans
    (F.kinetic_map β u v)

def rotation (σ : Equiv.Perm (Fin 3)) : Frame n where
  symmetry := WilsonSpatialRotations.rotation (2 * n) σ
  plaquettes := Equiv.prodCongr (vertexEquiv (2 * n) σ) (planeEquiv σ)
  defect_map p u := by
    change defect n p (rotationEquiv (2 * n) σ u) = _
    rw [rotationEquiv_apply]
    unfold defect
    rw [holonomy_rotate]
    exact plane_defect (2 * n) σ u (vertexEquiv (2 * n) σ p.1) p.2
  kinetic_map β u v := by
    change kineticWeight character β 2 (rotationEquiv (2 * n) σ u)
      (rotationEquiv (2 * n) σ v) = _
    simp only [rotationEquiv_apply, kineticWeight, kinetic_rotate]

def translation (s : SpatialVertex (2 * n)) : Frame n where
  symmetry := WilsonSpatialRotations.translation (2 * n) s
  plaquettes := Equiv.prodCongr (Equiv.addRight s) (Equiv.refl SpatialPlane)
  defect_map p u := by
    change defect n p (WilsonGroundTranslation.sliceEquiv (2 * n) s u) = _
    rw [WilsonGroundTranslation.sliceEquiv_apply]
    unfold defect
    rw [WilsonGroundTranslation.spatialHolonomy_shift]
    rfl
  kinetic_map β u v := by
    change kineticWeight character β 2 (WilsonGroundTranslation.sliceEquiv (2 * n) s u)
      (WilsonGroundTranslation.sliceEquiv (2 * n) s v) = _
    simp only [WilsonGroundTranslation.sliceEquiv_apply, kineticWeight, kinetic_shift]

def affine (σ : Equiv.Perm (Fin 3)) (s : SpatialVertex (2 * n)) : Frame n :=
  composition n (translation n s) (rotation n σ)

theorem affine_plaquette (σ : Equiv.Perm (Fin 3)) (s : SpatialVertex (2 * n)) (p : Plaquette n) :
    (affine n σ s).plaquettes p = (vertexEquiv (2 * n) σ p.1 + s,planeEquiv σ p.2) := rfl

end
end UnifiedTheory.Clay.YangMills.WilsonPlaquetteFrames
