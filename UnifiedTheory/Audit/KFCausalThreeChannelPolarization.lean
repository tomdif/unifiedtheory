/- Recover the full sesquilinear pairing from a three-channel energy identity. -/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalThreeChannelPolarization
noncomputable section
variable {V X Y Z W : Type*} [AddCommGroup V] [Module ℂ V]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem inner_split (A : V →ₗ[ℂ] X) (B : V →ₗ[ℂ] Y)
    (C : V →ₗ[ℂ] Z) (D : V →ₗ[ℂ] W) (r : ℝ)
    (hn : ∀ u, ‖A u‖^2 = ‖B u‖^2+r^2*(‖C u‖^2+‖D u‖^2)) (u v : V) :
    inner ℂ (A u) (A v) = inner ℂ (B u) (B v)+
      (r^2:ℂ)*(inner ℂ (C u) (C v)+inner ℂ (D u) (D v)) := by
  let L : V →ₗ[ℂ] WithLp 2 (Y × WithLp 2 (Z × W)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ Y (WithLp 2 (Z × W))).symm.toLinearMap.comp
      (B.prod ((WithLp.prodContinuousLinearEquiv 2 ℂ Z W).symm.toLinearMap.comp
        (((r:ℂ) • C).prod ((r:ℂ) • D))))
  have hL (x : V) : ‖A x‖ = ‖L x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hn,WithLp.prod_norm_sq_eq_of_L2]
    change ‖B x‖^2+r^2*(‖C x‖^2+‖D x‖^2) =
      ‖B x‖^2+‖WithLp.toLp 2 ((r:ℂ) • C x,(r:ℂ) • D x)‖^2
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖B x‖^2+r^2*(‖C x‖^2+‖D x‖^2) =
      ‖B x‖^2+(‖(r:ℂ) • C x‖^2+‖(r:ℂ) • D x‖^2)
    simp only [norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    ring
  have he : inner ℂ (A u) (A v) = inner ℂ (L u) (L v) := by
    rw [inner_eq_sum_norm_sq_div_four,inner_eq_sum_norm_sq_div_four]
    simp only [← map_add,← map_sub,← map_smul,hL]
  rw [he]
  change inner ℂ (B u) (B v)+
      (inner ℂ ((r:ℂ) • C u) ((r:ℂ) • C v)+inner ℂ ((r:ℂ) • D u) ((r:ℂ) • D v)) = _
  rw [inner_smul_left,inner_smul_right,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  ring

#print axioms inner_split
end
end UnifiedTheory.Audit.KFCausalThreeChannelPolarization
