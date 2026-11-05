/- Coordinate permutations and translations are exact symmetries of the
actual spatial Wilson potential and raw temporal kernel. Reversed plaquette
orientations are accounted for by the SU(2) inverse-character identity. -/
import UnifiedTheory.Clay.YangMills.WilsonRawSymmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSpatialRotations
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonRawSymmetry WilsonTemporalGauge
open WilsonSingleLinkStaples (character character_inverse_re)

variable (n : ℕ)

def vertexEquiv (σ : Equiv.Perm (Fin 3)) : SpatialVertex n ≃ SpatialVertex n :=
  { toFun := fun x j => x (σ.symm j)
    invFun := fun x j => x (σ j)
    left_inv := fun x => by funext j; simp
    right_inv := fun x => by funext j; simp }

def linkEquiv (σ : Equiv.Perm (Fin 3)) :
    (SpatialVertex n × Fin 3) ≃ (SpatialVertex n × Fin 3) :=
  Equiv.prodCongr (vertexEquiv n σ) σ

def rotate (σ : Equiv.Perm (Fin 3)) (u : Slice n) : Slice n := fun e => u (linkEquiv n σ e)

def rotationEquiv (σ : Equiv.Perm (Fin 3)) : Slice n ≃ᵐ Slice n :=
  MeasurableEquiv.piCongrLeft (fun _ : SpatialVertex n × Fin 3 => Q) (linkEquiv n σ).symm

theorem rotationEquiv_apply (σ : Equiv.Perm (Fin 3)) (u : Slice n) :
    rotationEquiv n σ u = rotate n σ u := by
  funext e
  simp [rotationEquiv, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rfl

theorem rotate_continuous (σ : Equiv.Perm (Fin 3)) : Continuous (rotate n σ) :=
  continuous_pi (fun _ => continuous_apply _)

theorem rotationEquiv_inv_continuous (σ : Equiv.Perm (Fin 3)) :
    Continuous (rotationEquiv n σ).symm :=
  continuous_pi (fun _ => continuous_apply _)

theorem vertex_step (σ : Equiv.Perm (Fin 3)) (x : SpatialVertex n) (i : Fin 3) :
    vertexEquiv n σ (spatialStep n x i) = spatialStep n (vertexEquiv n σ x) (σ i) := by
  funext j
  simp only [vertexEquiv, Equiv.coe_fn_mk, spatialStep, Pi.add_apply]
  congr 1
  simp only [Pi.single_apply]
  have h : σ.symm j = i ↔ j = σ i := by
    constructor
    · intro h
      simpa using congrArg σ h
    · intro h
      simp [h]
  simp only [h]

theorem holonomy_rotate (σ : Equiv.Perm (Fin 3)) (u : Slice n)
    (x : SpatialVertex n) (i j : Fin 3) :
    spatialHolonomy (rotate n σ u) x i j =
      spatialHolonomy u (vertexEquiv n σ x) (σ i) (σ j) := by
  simp only [spatialHolonomy, rotate, linkEquiv, Equiv.prodCongr_apply,
    Prod.map_apply, vertex_step]

def orientedDefect (u : Slice n) (x : SpatialVertex n) (i j : Fin 3) : ℝ :=
  2 - (character (spatialHolonomy u x i j)).re

theorem defect_diagonal (u : Slice n) (x : SpatialVertex n) (i : Fin 3) :
    orientedDefect n u x i i = 0 := by
  have he : spatialHolonomy u x i i = 1 := by unfold spatialHolonomy; group
  unfold orientedDefect
  rw [he, QuaternionDefectCurvature.character_chord]
  simp

theorem defect_swap (u : Slice n) (x : SpatialVertex n) (i j : Fin 3) :
    orientedDefect n u x j i = orientedDefect n u x i j := by
  have he : spatialHolonomy u x j i = (spatialHolonomy u x i j)⁻¹ := by
    unfold spatialHolonomy
    group
  simp only [orientedDefect, he, character_inverse_re]

theorem plane_sum (u : Slice n) (x : SpatialVertex n) :
    2 * (∑ p : SpatialPlane, orientedDefect n u x p.val.1 p.val.2) =
      ∑ i : Fin 3, ∑ j : Fin 3, orientedDefect n u x i j := by
  have hp : (Finset.univ : Finset SpatialPlane) =
      {⟨(0,1),by decide⟩, ⟨(0,2),by decide⟩, ⟨(1,2),by decide⟩} := by decide
  rw [hp]
  repeat rw [Finset.sum_insert (by decide)]
  simp only [Finset.sum_singleton, Fin.sum_univ_three, defect_diagonal]
  rw [defect_swap n u x 0 1, defect_swap n u x 0 2, defect_swap n u x 1 2]
  ring

variable [NeZero n]

theorem potential_ordered (u : Slice n) :
    2 * potential character 2 u =
      ∑ x : SpatialVertex n, ∑ i : Fin 3, ∑ j : Fin 3, orientedDefect n u x i j := by
  unfold potential
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => plane_sum n u x)

theorem potential_rotate (σ : Equiv.Perm (Fin 3)) (u : Slice n) :
    potential character 2 (rotate n σ u) = potential character 2 u := by
  apply mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)
  rw [potential_ordered, potential_ordered]
  simp only [orientedDefect, holonomy_rotate]
  have hs (x : SpatialVertex n) :
      (∑ i : Fin 3, ∑ j : Fin 3, orientedDefect n u x (σ i) (σ j)) =
        ∑ i : Fin 3, ∑ j : Fin 3, orientedDefect n u x i j := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3, orientedDefect n u x (σ i) j :=
        Finset.sum_congr rfl (fun i _ => Equiv.sum_comp σ (orientedDefect n u x (σ i)))
      _ = _ := Equiv.sum_comp σ (fun i => ∑ j : Fin 3, orientedDefect n u x i j)
  change (∑ x : SpatialVertex n, ∑ i : Fin 3, ∑ j : Fin 3,
    orientedDefect n u (vertexEquiv n σ x) (σ i) (σ j)) = _
  simp_rw [hs]
  exact Equiv.sum_comp (vertexEquiv n σ)
    (fun x => ∑ i : Fin 3, ∑ j : Fin 3, orientedDefect n u x i j)

theorem kinetic_rotate (σ : Equiv.Perm (Fin 3)) (u v : Slice n) :
    kineticAction character 2 (rotate n σ u) (rotate n σ v) = kineticAction character 2 u v :=
  Equiv.sum_comp (linkEquiv n σ) (fun e => 2 - (character ((u e)⁻¹ * v e)).re)

theorem raw_rotate (σ : Equiv.Perm (Fin 3)) (β : ℝ) (u v : Slice n) :
    rawKernel character β 2 (rotate n σ u) (rotate n σ v) = rawKernel character β 2 u v := by
  simp only [rawKernel, spatialWeight, kineticWeight, potential_rotate, kinetic_rotate]

def rotation (σ : Equiv.Perm (Fin 3)) : Symmetry n where
  map := rotationEquiv n σ
  continuous_map := by
    change Continuous (fun u => rotationEquiv n σ u)
    simp_rw [rotationEquiv_apply]
    exact rotate_continuous n σ
  continuous_inv := rotationEquiv_inv_continuous n σ
  preserving := measurePreserving_piCongrLeft
    (fun _ : SpatialVertex n × Fin 3 => RegulatedGauge.compactHaar Q) (linkEquiv n σ).symm
  invariant β u v := by simpa only [rotationEquiv_apply] using raw_rotate n σ β u v

theorem kinetic_shift (s : SpatialVertex n) (u v : Slice n) :
    kineticAction character 2 (WilsonGroundTranslation.shiftSlice n s u)
      (WilsonGroundTranslation.shiftSlice n s v) = kineticAction character 2 u v :=
  Equiv.sum_comp (Equiv.prodCongr (Equiv.addRight s) (Equiv.refl (Fin 3)))
    (fun e => 2 - (character ((u e)⁻¹ * v e)).re)

def translation (s : SpatialVertex n) : Symmetry n where
  map := WilsonGroundTranslation.sliceEquiv n s
  continuous_map := by
    change Continuous (fun u => WilsonGroundTranslation.sliceEquiv n s u)
    simp_rw [WilsonGroundTranslation.sliceEquiv_apply]
    exact WilsonGroundTranslation.shiftSlice_continuous n s
  continuous_inv := continuous_pi (fun _ => continuous_apply _)
  preserving := WilsonGroundTranslation.slice_preserving n s
  invariant β u v := by
    simp only [WilsonGroundTranslation.sliceEquiv_apply, rawKernel, spatialWeight,
      kineticWeight, WilsonGroundTranslation.potential_shift, kinetic_shift]

end
end UnifiedTheory.Clay.YangMills.WilsonSpatialRotations
