/- The canonical phase-space lift of the actual mixed-coordinate charge rotation.
The mixed base (antisymmetric momenta, symmetric positions) agrees exactly with
NormalizedChargeFlow after the documented frequency-to-momentum scaling. This
is a finite-dimensional classical identification, not an Egorov theorem for
the ordered quantum Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates
import UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
import UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClassicalChargePhase
noncomputable section
open UnifiedTheory.Audit.KFCausalPairedRotation (Space)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale backward scale_square)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse velocity)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)

abbrev Phase := Space × Space

def rotate (θ : ℝ) (z : Phase) : Phase :=
  (WithLp.toLp 2 (fun
    | .inl i => Real.cos θ*z.1 (.inl i)+Real.sin θ*z.2 (.inr i.castSucc.succ)
    | .inr i => ![z.1 (.inr 0),
        Real.cos θ*z.1 (.inr 1)+Real.sin θ*z.2 (.inl 0),
        Real.cos θ*z.1 (.inr 2)+Real.sin θ*z.2 (.inl 1),z.1 (.inr 3)] i),
   WithLp.toLp 2 (fun
    | .inl i => Real.cos θ*z.2 (.inl i)-Real.sin θ*z.1 (.inr i.castSucc.succ)
    | .inr i => ![z.2 (.inr 0),
        Real.cos θ*z.2 (.inr 1)-Real.sin θ*z.1 (.inl 0),
        Real.cos θ*z.2 (.inr 2)-Real.sin θ*z.1 (.inl 1),z.2 (.inr 3)] i))

def mixedBase (c : ℝ) (z : Phase) : Space := WithLp.toLp 2 fun
  | .inl i => z.2 (.inl i)/c
  | .inr i => z.1 (.inr i)

theorem mixedBase_rotate (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (z : Phase) :
    mixedBase c (rotate θ z) =
      KFCausalNormalizedChargeFlow.flowEquiv c hc θ (mixedBase c z) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [mixedBase, rotate, KFCausalNormalizedChargeFlow.flow_apply,
      KFCausalNormalizedChargeFlow.dilate, KFCausalPairedRotation.rotate]
  all_goals field_simp <;> ring

theorem rotate_zero (z : Phase) : rotate 0 z = z := by
  ext i <;> rcases i with i | i <;> fin_cases i <;> simp [rotate]

theorem rotate_compose (θ φ : ℝ) (z : Phase) :
    rotate θ (rotate φ z) = rotate (θ+φ) z := by
  ext i <;> rcases i with i | i <;> fin_cases i <;>
    simp [rotate, Real.sin_add, Real.cos_add] <;> ring

theorem rotate_smul (θ a : ℝ) (z : Phase) : rotate θ (a • z) = a • rotate θ z := by
  ext i <;> rcases i with i | i <;> fin_cases i <;> simp [rotate] <;> ring

def symplectic (z w : Phase) : ℝ := inner ℝ z.1 w.2-inner ℝ z.2 w.1

theorem rotate_symplectic (θ : ℝ) (z w : Phase) :
    symplectic (rotate θ z) (rotate θ w) = symplectic z w := by
  let S := z.1 (.inr 0)*w.2 (.inr 0)-z.2 (.inr 0)*w.1 (.inr 0)+
    z.1 (.inr 3)*w.2 (.inr 3)-z.2 (.inr 3)*w.1 (.inr 3)
  calc
    _ = (Real.sin θ^2+Real.cos θ^2)*(symplectic z w-S)+S := by
      simp [symplectic, PiLp.inner_apply, Fintype.sum_sum_type, Fin.sum_univ_succ,
        rotate, RCLike.inner_apply, S, -Real.sin_sq_add_cos_sq]
      ring
    _ = symplectic z w := by rw [Real.sin_sq_add_cos_sq]; ring

def physicalTail (q : Space) : Transverse := fun i => backward q i.succ

def shear (z : Phase) : ℝ :=
  ∑ i, velocity (physicalTail z.1) i * physicalTail z.2 i

def diagonalPairing (z : Phase) : ℝ :=
  z.1 (.inl 0)*z.2 (.inl 0)+z.1 (.inr 1)*z.2 (.inr 1)+
  z.1 (.inl 1)*z.2 (.inl 1)+z.1 (.inr 2)*z.2 (.inr 2)

def crossPairing (z : Phase) : ℝ :=
  z.2 (.inl 0)*z.2 (.inr 1)-z.1 (.inl 0)*z.1 (.inr 1)+
  z.2 (.inl 1)*z.2 (.inr 2)-z.1 (.inl 1)*z.1 (.inr 2)

theorem shear_eq (z : Phase) :
    shear z = diagonalPairing z/2+2*scale*z.1 (.inr 2)*z.2 (.inr 3) := by
  simp [shear, physicalTail, velocity, backward, diagonalPairing, Fin.sum_univ_succ]
  ring_nf
  rw [scale_square]
  ring

theorem shear_rotate (θ : ℝ) (z : Phase) :
    shear (rotate θ z) =
      (Real.cos θ^2-Real.sin θ^2)*(diagonalPairing z/2)+
      (Real.sin θ*Real.cos θ)*crossPairing z+
      Real.sin θ*(2*scale*z.2 (.inl 1)*z.2 (.inr 3))+
      Real.cos θ*(2*scale*z.1 (.inr 2)*z.2 (.inr 3)) := by
  rw [shear_eq]
  simp [diagonalPairing, crossPairing, rotate]
  ring

theorem shear_smul (a : ℝ) (z : Phase) : shear (a • z) = a^2*shear z := by
  simp [shear_eq, diagonalPairing]
  ring

def kinetic (t : ℝ) (z : Phase) : ℝ :=
  ((∑ i, modelDirections 0 i*physicalTail z.2 i)^2+
   (∑ i, modelDirections 1 i*physicalTail z.2 i)^2)/2+
  Real.exp (2*t)*((∑ i, modelDirections 2 i*physicalTail z.2 i)^2+
   (∑ i, modelDirections 3 i*physicalTail z.2 i)^2)/2

theorem kinetic_eq (t : ℝ) (z : Phase) :
    kinetic t z = z.2 (.inr 1)^2+(2*scale*z.2 (.inr 2)+z.2 (.inr 3))^2/2+
      Real.exp (2*t)*(z.2 (.inl 0)^2+z.2 (.inl 1)^2) := by
  simp [kinetic, modelDirections, physicalTail, backward, Fin.sum_univ_succ]
  ring_nf
  rw [scale_square]
  ring

theorem kinetic_nonnegative (t : ℝ) (z : Phase) : 0 ≤ kinetic t z := by
  unfold kinetic
  positivity

theorem kinetic_smul (t a : ℝ) (z : Phase) : kinetic t (a • z) = a^2*kinetic t z := by
  simp [kinetic_eq]
  ring

#print axioms mixedBase_rotate
#print axioms rotate_zero
#print axioms rotate_compose
#print axioms rotate_smul
#print axioms rotate_symplectic
#print axioms shear_eq
#print axioms shear_rotate
#print axioms shear_smul
#print axioms kinetic_eq
#print axioms kinetic_nonnegative
#print axioms kinetic_smul

end
end UnifiedTheory.Audit.KFCausalClassicalChargePhase
