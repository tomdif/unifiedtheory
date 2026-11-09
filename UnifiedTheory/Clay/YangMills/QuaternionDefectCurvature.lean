/- Defect-sensitive finite second differences of the SU(2) Wilson action.
The negative part vanishes with the base holonomy defect. These are
pointwise action identities and estimates, not a Poincare theorem. -/
import UnifiedTheory.Clay.YangMills.SU2GaussianMass

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.QuaternionDefectCurvature
noncomputable section
open WilsonSlabOperator QuaternionSymmetricChange
open WilsonSingleLinkStaples (character)
open scoped Quaternion RealInnerProductSpace

theorem character_chord (a : Q) : 2-(character a).re = ‖(a : ℍ)-1‖^2 := by
  rw [SU2GaussianMass.chord_square, WilsonSingleLinkStaples.character_re]
  ring

/-- The nonnegative holonomy increments are kept separately from the
remainder proportional to the base plaquette defect. -/
theorem defect_second_identity (a ap am : Q) :
    (2-(character ap).re)+(2-(character am).re)-2*(2-(character a).re) =
      ‖(ap : ℍ)-(a : ℍ)‖^2+‖(am : ℍ)-(a : ℍ)‖^2+
        2*⟪(a : ℍ)-1, (ap : ℍ)+(am : ℍ)-(a : ℍ)-(a : ℍ)⟫ := by
  simp only [character_chord, norm_sub_sq_real, inner_sub_left, inner_sub_right,
    inner_add_right, real_inner_self_eq_norm_sq, real_inner_comm]
  ring

theorem defect_second_lower (a ap am : Q) (d k δ : ℝ)
    (h : Variation a ap am d k) (ha : ‖(a : ℍ) - 1‖ ≤ δ) :
    -2*δ*k^2*d^2 ≤
      (2-(character ap).re)+(2-(character am).re)-2*(2-(character a).re) := by
  have hi := abs_real_inner_le_norm ((a : ℍ)-1)
    ((ap : ℍ)+(am : ℍ)-(a : ℍ)-(a : ℍ))
  have hm := mul_le_mul ha h.2.2 (norm_nonneg _) ((norm_nonneg _).trans ha)
  have hl := (abs_le.mp hi).1
  rw [defect_second_identity]
  nlinarith [sq_nonneg ‖(ap : ℍ)-(a : ℍ)‖, sq_nonneg ‖(am : ℍ)-(a : ℍ)‖]

theorem relative_character (u v : Q) :
    (character (u⁻¹*v)).re = 2-‖(u : ℍ)-(v : ℍ)‖^2 := by
  rw [WilsonRowGeometry.character_pair, norm_sub_sq_real, unit_norm, unit_norm]
  ring

/-- The temporal quadratic coefficient is the actual relative character. -/
theorem kinetic_second_exact (q u v : Q) :
    (2-(character ((q*u)⁻¹*v)).re)+(2-(character ((q⁻¹*u)⁻¹*v)).re)-
      2*(2-(character (u⁻¹*v)).re) =
        ‖(q : ℍ)-1‖^2*(2-‖(u : ℍ)-(v : ℍ)‖^2) := by
  have hs : ((q*u : Q) : ℍ)+((q⁻¹*u : Q) : ℍ) =
      (2*(q : ℍ).re) • (u : ℍ) := by
    change (q : ℍ)*(u : ℍ)+star (q : ℍ)*(u : ℍ) = _
    rw [← add_mul, Quaternion.self_add_star']
    exact (Algebra.smul_def (2*(q : ℍ).re) (u : ℍ)).symm
  have hi := congrArg (fun x : ℍ => ⟪x, (v : ℍ)⟫) hs
  simp only [inner_add_left, real_inner_smul_left] at hi
  rw [← relative_character u v]
  simp only [WilsonRowGeometry.character_pair, SU2GaussianMass.chord_square]
  nlinarith [hi]

end
end UnifiedTheory.Clay.YangMills.QuaternionDefectCurvature
