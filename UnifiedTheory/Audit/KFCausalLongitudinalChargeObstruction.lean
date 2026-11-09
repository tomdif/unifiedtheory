/- A classical obstruction to silently treating the longitudinal shear as
charge invariant. Its positive exponential has no uniform pointwise bound
under a fixed quarter-turn. This is not a quantum commutator theorem or a
counterexample along the prescribed evolving quantum states. -/
import UnifiedTheory.Audit.KFCausalClassicalChargePhase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalLongitudinalChargeObstruction
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase

def witness (a : ℝ) : Phase :=
  (WithLp.toLp 2 (Pi.single (.inl 0) a),WithLp.toLp 2 (Pi.single (.inl 0) (-a)))

theorem witness_shear (a : ℝ) : shear (witness a) = -a^2/2 := by
  simp [shear_eq,diagonalPairing,witness]
  ring

theorem witness_rotated_shear (a : ℝ) : shear (rotate (Real.pi/2) (witness a)) = a^2/2 := by
  simp [shear_eq,diagonalPairing,witness,rotate]
  ring

theorem shear_not_charge_invariant : ¬∀ θ z, shear (rotate θ z) = shear z := by
  intro h
  have he := h (Real.pi/2) (witness 1)
  rw [witness_rotated_shear,witness_shear] at he
  norm_num at he

theorem no_uniform_exponential_comparison (C : ℝ) (hC : 0 < C) (B : ℝ) :
    ∃ z : Phase, B*Real.exp (shear z/C) < Real.exp (shear (rotate (Real.pi/2) z)/C) := by
  let a := Real.sqrt (C*(|B|+1))
  have ha : a^2 = C*(|B|+1) := Real.sq_sqrt (by positivity)
  have hr : a^2/C = |B|+1 := by rw [ha]; field_simp
  have he : B < Real.exp (a^2/C) := by
    rw [hr]
    linarith [Real.add_one_le_exp (|B|+1),le_abs_self B]
  refine ⟨witness a,?_⟩
  rw [witness_shear,witness_rotated_shear]
  have hid : Real.exp (a^2/2/C) = Real.exp (a^2/C)*Real.exp ((-a^2/2)/C) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hid]
  exact mul_lt_mul_of_pos_right he (Real.exp_pos _)

#print axioms witness_shear
#print axioms witness_rotated_shear
#print axioms shear_not_charge_invariant
#print axioms no_uniform_exponential_comparison

end
end UnifiedTheory.Audit.KFCausalLongitudinalChargeObstruction
