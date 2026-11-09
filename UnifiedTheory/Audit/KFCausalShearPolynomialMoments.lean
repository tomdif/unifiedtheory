/- Linear and mixed coordinate moments follow from the pure quadratic
moments of a physical state. Bounded continuous clock coefficients preserve
these L2 estimates. No generator membership is assumed. -/
import UnifiedTheory.Audit.KFCausalShearMaximalDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalShearPolynomialMoments
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

theorem linear_memLp (f : Configuration → ℂ) (hf : MemLp f 2 volume)
    (hq : ∀ i : Fin 5, MemLp (fun x => (x.2 i:ℂ)^2*f x) 2 volume) (i : Fin 5) :
    MemLp (fun x => (x.2 i:ℂ)*f x) 2 volume := by
  have hc : Continuous (fun x : Configuration => (x.2 i:ℂ)) := by fun_prop
  apply (hf.add (hq i)).of_le (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(x.2 i:ℂ)*f x‖ ≤ ‖f x+(x.2 i:ℂ)^2*f x‖
  rw [← one_add_mul]
  have he : 1+(x.2 i:ℂ)^2 = ((1+(x.2 i)^2:ℝ):ℂ) := by push_cast; rfl
  rw [he]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ 1+(x.2 i)^2 by positivity)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  nlinarith [sq_nonneg (|x.2 i|-1),sq_abs (x.2 i)]

theorem mixed_memLp (f : Configuration → ℂ) (hf : MemLp f 2 volume)
    (hq : ∀ i : Fin 5, MemLp (fun x => (x.2 i:ℂ)^2*f x) 2 volume) (i j : Fin 5) :
    MemLp (fun x => (x.2 i:ℂ)*(x.2 j:ℂ)*f x) 2 volume := by
  have hc : Continuous (fun x : Configuration => (x.2 i:ℂ)*(x.2 j:ℂ)) := by fun_prop
  apply ((hq i).add (hq j)).of_le (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(x.2 i:ℂ)*(x.2 j:ℂ)*f x‖ ≤ ‖(x.2 i:ℂ)^2*f x+(x.2 j:ℂ)^2*f x‖
  rw [← add_mul]
  have he : (x.2 i:ℂ)^2+(x.2 j:ℂ)^2 = (((x.2 i)^2+(x.2 j)^2:ℝ):ℂ) := by push_cast; rfl
  rw [he]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ (x.2 i)^2+(x.2 j)^2 by positivity)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  nlinarith [sq_nonneg (|x.2 i|-|x.2 j|),sq_abs (x.2 i),sq_abs (x.2 j)]

theorem clock_mul_memLp (c : ℝ → ℂ) (hc : Continuous c) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ s, ‖c s‖ ≤ M) (f : Configuration → ℂ) (hf : MemLp f 2 volume) :
    MemLp (fun x => c x.1*f x) 2 volume := by
  simpa only [one_smul] using KFCausalShearMaximalDifferential.scaled_memLp
    (fun x : Configuration => c x.1) (hc.comp continuous_fst) M hM (fun x => hb x.1) f hf 1

#print axioms linear_memLp
#print axioms mixed_memLp
#print axioms clock_mul_memLp
end
end UnifiedTheory.Audit.KFCausalShearPolynomialMoments
