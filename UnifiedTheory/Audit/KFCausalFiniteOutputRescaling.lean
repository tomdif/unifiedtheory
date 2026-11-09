/- Bounded diagonal changes of finite Hilbert output coordinates and
orthogonal splitting into static and growing components. -/
import UnifiedTheory.Audit.KFCausalFiniteJointGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFiniteOutputRescaling
noncomputable section
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]

def diagonal (d : ι → ℂ) : Output ι H →L[ℂ] Output ι H where
  toFun y := WithLp.toLp 2 (fun i => d i • y i)
  map_add' := by
    intro x y
    apply PiLp.ext
    intro i
    simp only [PiLp.add_apply,smul_add]
  map_smul' := by
    intro a y
    apply PiLp.ext
    intro i
    simp only [PiLp.smul_apply,smul_smul,mul_comm,RingHom.id_apply]
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => continuous_const.smul (PiLp.continuous_apply 2 _ i)))

theorem diagonal_apply (d : ι → ℂ) (y : Output ι H) (i : ι) : diagonal d y i=d i • y i := rfl

theorem diagonal_norm_sq (d : ι → ℂ) (y : Output ι H) :
    ‖diagonal d y‖^2=∑ i, ‖d i‖^2*‖y i‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [diagonal_apply,norm_smul,mul_pow]

variable (p : ι → Prop) [DecidablePred p]

def selected : Output ι H →L[ℂ] Output ι H := diagonal (fun i => if p i then 1 else 0)

theorem selected_apply (y : Output ι H) (i : ι) : selected p y i=if p i then y i else 0 := by
  by_cases h : p i <;> simp [selected,diagonal_apply,h]

theorem split_norm (y : Output ι H) :
    ‖y‖^2=‖selected p y‖^2+‖selected (fun i => ¬ p i) y‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i <;> simp [selected_apply,h]

theorem selected_norm_le (y : Output ι H) : ‖selected p y‖ ≤ ‖y‖ := by
  have hs := split_norm p y
  nlinarith [sq_nonneg ‖selected (fun i => ¬ p i) y‖,norm_nonneg y,norm_nonneg (selected p y)]

def splitScaled (a : ℝ) : Output ι H →L[ℂ] Output ι H :=
  diagonal (fun i => if p i then 1 else (a:ℂ))

theorem splitScaled_apply (a : ℝ) (y : Output ι H) (i : ι) :
    splitScaled p a y i=if p i then y i else (a:ℂ) • y i := by
  by_cases h : p i <;> simp [splitScaled,diagonal_apply,h]

theorem splitScaled_norm_sq (a : ℝ) (y : Output ι H) :
    ‖splitScaled p a y‖^2=‖selected p y‖^2+a^2*‖selected (fun i => ¬ p i) y‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i <;>
    simp [splitScaled_apply,selected_apply,h,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

theorem splitScaled_inner (a : ℝ) (x y : Output ι H) :
    inner ℂ (splitScaled p a x) (splitScaled p a y)=
      inner ℂ (selected p x) (selected p y)+
        (a^2:ℂ)*inner ℂ (selected (fun i => ¬ p i) x) (selected (fun i => ¬ p i) y) := by
  rw [PiLp.inner_apply,PiLp.inner_apply,PiLp.inner_apply,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i <;>
    simp only [splitScaled_apply,selected_apply,h,not_false_eq_true,not_true_eq_false,
      if_true,if_false,inner_zero_right,zero_add,mul_zero,add_zero,
      inner_smul_left,inner_smul_right,Complex.conj_ofReal,pow_two,mul_assoc]

#print axioms diagonal_apply
#print axioms diagonal_norm_sq
#print axioms selected_apply
#print axioms split_norm
#print axioms selected_norm_le
#print axioms splitScaled_apply
#print axioms splitScaled_norm_sq
#print axioms splitScaled_inner

end
end UnifiedTheory.Audit.KFCausalFiniteOutputRescaling
