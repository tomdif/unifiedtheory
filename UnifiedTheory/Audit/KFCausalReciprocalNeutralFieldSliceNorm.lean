/- The same positive physical Gram integral controls the vacuum,
linear-field and squared-field wavefunctions, retaining all cross terms. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPhysicalSliceNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralFieldSliceNorm
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalReciprocalNeutralPhysicalSliceNorm (wave weighted weighted_integrable weighted_integral_joint)
open KFCausalReciprocalNeutralSliceIntegrability (factor factor_memLp)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalQuarticPlaneDomination (potential)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalReciprocalNeutralLaplace (jointMeasure)

theorem fieldPower_bound (k : Fin 3) (x : ℝ) : (|x|^k.val)^2 ≤ 4*potential x := by
  fin_cases k <;> norm_num [potential,sq_abs] <;>
    nlinarith [sq_nonneg x,sq_nonneg (x^2)]

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c b : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

theorem fieldWave_sum (k : ℕ) (q : Transverse) :
    (pointField q:ℂ)^k*wave n α β w r c b P q =
      ∑ i, c i*factor α β (w i) r (b i) (P i) k q := by
  unfold wave
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [KFCausalReciprocalNeutralSliceIntegrability.factor,pow_zero,one_mul]
  ring

variable (ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i)

include hα hβ hwidth hε hy hw in
theorem fieldWave_memLp (k : ℕ) :
    MemLp (fun q => (pointField q:ℂ)^k*wave n α β w (scale ε y s) c b P q) 2 volume := by
  have hm := memLp_finset_sum Finset.univ (fun i _ =>
    (factor_memLp α β ε y s (w i) hα hβ hwidth hε hy (hw i) (b i) (P i) k).const_mul (c i))
  exact hm.ae_eq (Filter.Eventually.of_forall (fun q => (fieldWave_sum n α β w (scale ε y s) c b P k q).symm))

include hα hβ hwidth hε hy hw in
theorem fieldWave_integral_le_joint (k : Fin 3) :
    (∫ q, ‖(pointField q:ℂ)^k.val*wave n α β w (scale ε y s) c b P q‖^2) ≤
      4*(Real.pi/4*∫ q, positiveDensity n α β w (scale ε y s) c
        (fun i => exponentialProfile (b i) 1 (P i)) q ∂jointMeasure) := by
  rw [← weighted_integral_joint n α β w c b P ε y s hα hβ hwidth hε hy hw,← integral_const_mul]
  have hm := fieldWave_memLp n α β w c b P ε y s hα hβ hwidth hε hy hw k.val
  apply integral_mono ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm)
    ((weighted_integrable n α β w c b P ε y s hα hβ hwidth hε hy hw).const_mul 4)
  intro q
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,mul_pow,weighted]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (fieldPower_bound k (pointField q))
    (sq_nonneg ‖wave n α β w (scale ε y s) c b P q‖)

#print axioms fieldPower_bound
#print axioms fieldWave_sum
#print axioms fieldWave_memLp
#print axioms fieldWave_integral_le_joint
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralFieldSliceNorm
