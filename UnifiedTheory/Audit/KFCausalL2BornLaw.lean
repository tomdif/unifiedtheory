/- The positive measure of an arbitrary L2 representative has its actual
squared norm as mass. Its integrals agree with multiplier expectations. -/
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalL2BornLaw
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def law (f : Lp ℂ 2 μ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (‖f x‖^2))

theorem law_apply (f : Lp ℂ 2 μ) (A : Set X) (hA : MeasurableSet A) :
    law μ f A = ENNReal.ofReal (∫ x in A, ‖f x‖^2 ∂μ) := by
  rw [law,withDensity_apply _ hA]
  exact (ofReal_integral_eq_lintegral_ofReal
    (((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)).integrableOn)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm

theorem law_total (f : Lp ℂ 2 μ) : law μ f Set.univ = ENNReal.ofReal (‖f‖^2) := by
  rw [law_apply μ f Set.univ MeasurableSet.univ,setIntegral_univ,← l2_norm_square]

theorem law_probability (f : Lp ℂ 2 μ) (hf : ‖f‖ = 1) : IsProbabilityMeasure (law μ f) where
  measure_univ := by rw [law_total,hf,one_pow,ENNReal.ofReal_one]

theorem integral_eq_inner (f q : Lp ℂ 2 μ) (w : X → ℂ)
    (hq : q =ᵐ[μ] fun x => w x*f x) :
    (∫ x, w x ∂law μ f) = inner ℂ f q := by
  have hm : AEMeasurable (fun x => ENNReal.ofReal (‖f x‖^2)) μ :=
    (Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const 2 |>.ennreal_ofReal
  rw [law,integral_withDensity_eq_integral_toReal_smul₀ hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) w,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hq] with x hx
  rw [hx,ENNReal.toReal_ofReal (sq_nonneg _)]
  change (‖f x‖^2 : ℝ) • w x = inner ℂ (f x) (w x • f x)
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  simp only [Complex.real_smul,Complex.ofReal_pow,mul_comm]
  norm_cast

#print axioms law_apply
#print axioms law_total
#print axioms law_probability
#print axioms integral_eq_inner

end
end UnifiedTheory.Audit.KFCausalL2BornLaw
