/- Quantitative limits of the field-domination argument. These facts
concern this comparison estimate, not a counterexample to a Hamiltonian
response bound, whose cancellations and energy denominator are different. -/
import UnifiedTheory.Audit.KFCausalMixedFieldClockBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalMixedFieldEstimateScope
noncomputable section
open KFCausalShiftedNeutralCoercivity
open KFCausalMixedFieldClockBounds
open KFCausalRelativeGaussianDifferential (position)
open KFCausalTransverseDilationFlow (Transverse)

theorem scaleBound_one_le (ε y : ℝ) (hε : 0 < ε) : 1 ≤ scaleBound ε y := by
  unfold scaleBound
  exact Real.one_le_exp (by positivity)

theorem inverseBound_lower (ε y s : ℝ) (hε : 0 < ε) :
    ε*Real.pi/|y| ≤ inverseBound ε y s := by
  have hr := scaleBound_one_le ε y hε
  have hp := mul_pos hε Real.pi_pos
  unfold inverseBound
  apply div_le_div_of_nonneg_right _ (abs_nonneg y)
  nlinarith [mul_nonneg (scaleBound_positive ε y).le (Real.exp_pos s).le]

theorem fieldBound_lower (ε y z s : ℝ) (hε : 0 < ε) (hy : y ≠ 0) :
    ε*Real.pi/|y| ≤ fieldBound ε y z s := by
  have hi := inverseBound_positive ε y s hε hy
  have hr := scaleBound_one_le ε y hε
  have hs := scaleBound_one_le ε z hε
  have hm := mul_le_mul_of_nonneg_right (show 1 ≤ 3*scaleBound ε z+2*scaleBound ε y by linarith) hi.le
  have hl := inverseBound_lower ε y s hε
  unfold fieldBound
  nlinarith only [hm,hl]

theorem no_real_scale_domination :
    ¬ ∃ C : ℝ, ∀ q : Transverse, ‖field 1 q‖ ≤ C*‖position 1 q 4‖ := by
  rintro ⟨C,hC⟩
  have h := hC (fun i => if i = 2 then 1 else 0)
  have h42 : (4:Fin 5) ≠ 2 := by decide
  have h32 : (3:Fin 5) ≠ 2 := by decide
  norm_num [field,position,h42,h32] at h

#print axioms scaleBound_one_le
#print axioms inverseBound_lower
#print axioms fieldBound_lower
#print axioms no_real_scale_domination
end
end UnifiedTheory.Audit.KFCausalMixedFieldEstimateScope
