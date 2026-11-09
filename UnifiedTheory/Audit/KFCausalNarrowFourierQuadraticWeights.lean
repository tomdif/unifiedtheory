/- Quadratic frequency and broad-position weights satisfy the growth
condition required by the proved charged derivative L2 envelopes. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierModelDirections

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalNarrowFourierQuadraticWeights
noncomputable section
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalNarrowFourierPackets (chargedRadius chargedRadius_nonnegative)
open KFCausalNarrowFourierModelDirections (left_square_le right_square_le)

theorem square_growth (a x t : ℝ) (ha : 0 < a) (hx : a*x^2 ≤ t) :
    ‖(x:ℂ)^2‖ ≤ (1/a)*(1+t) := by
  simp only [norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have h1 : x^2 ≤ t/a := (le_div_iff₀ ha).mpr (by nlinarith only [hx])
  have h2 : 0 ≤ 1/a := by positivity
  rw [div_eq_mul_one_div] at h1
  nlinarith

theorem left_square_bound (α : ℝ) (hα : 0 < α) (z : Block 2 × Block 4) (i : Fin 2) :
    ‖(z.1 i:ℂ)^2‖ ≤ (1/(Real.pi^2/α))*(1+chargedRadius α z) :=
  square_growth (Real.pi^2/α) (z.1 i) (chargedRadius α z) (by positivity) (left_square_le α hα z i)

theorem right_square_bound (α : ℝ) (hα : 0 < α) (z : Block 2 × Block 4) (i : Fin 2) :
    ‖(z.2 i.castSucc.succ:ℂ)^2‖ ≤ (1/α)*(1+chargedRadius α z) :=
  square_growth α (z.2 i.castSucc.succ) (chargedRadius α z) hα (right_square_le α hα z i)

theorem one_bound (α : ℝ) (hα : 0 < α) (z : Block 2 × Block 4) :
    ‖(1:ℂ)‖ ≤ 1*(1+chargedRadius α z) := by
  have hz := chargedRadius_nonnegative α hα z
  simp only [norm_one,one_mul]
  linarith

#print axioms square_growth
#print axioms left_square_bound
#print axioms right_square_bound
#print axioms one_bound
end
end UnifiedTheory.Audit.KFCausalNarrowFourierQuadraticWeights
