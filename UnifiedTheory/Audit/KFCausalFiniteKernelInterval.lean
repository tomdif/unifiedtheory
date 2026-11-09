/- Integrating a measurable finite-measure kernel over a compact time
interval. Its finite mass and Bochner test identities are derived from
continuity of the actual kernel mass, not a uniform-kernel hypothesis. -/
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalFiniteKernelInterval
noncomputable section
open MeasureTheory ProbabilityTheory BoundedContinuousFunction

def integrated (κ : Kernel ℝ ℝ) (b c : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Icc b c)).bind κ

variable (κ : Kernel ℝ ℝ) [∀ t, IsFiniteMeasure (κ t)]
  (hm : Continuous (fun t => (κ t).real Set.univ)) (b c : ℝ)
include hm

theorem integrated_mass :
    integrated κ b c Set.univ = ENNReal.ofReal (∫ t in Set.Icc b c, (κ t).real Set.univ) := by
  rw [integrated,Measure.bind_apply MeasurableSet.univ κ.aemeasurable]
  have he (t : ℝ) : κ t Set.univ = ENNReal.ofReal ((κ t).real Set.univ) :=
    (ENNReal.ofReal_toReal (measure_ne_top (κ t) Set.univ)).symm
  simp_rw [he]
  exact (ofReal_integral_eq_lintegral_ofReal hm.integrableOn_Icc
    (Filter.Eventually.of_forall (fun _ => measureReal_nonneg))).symm

theorem integrated_finite : IsFiniteMeasure (integrated κ b c) where
  measure_univ_lt_top := by rw [integrated_mass κ hm]; exact ENNReal.ofReal_lt_top

theorem integrated_real_mass :
    (integrated κ b c).real Set.univ = ∫ t in Set.Icc b c, (κ t).real Set.univ := by
  rw [Measure.real,integrated_mass κ hm,ENNReal.toReal_ofReal]
  exact integral_nonneg (fun _ => measureReal_nonneg)

theorem integrated_mass_bound (hbc : b ≤ c) (C : ℝ)
    (hb : ∀ t ∈ Set.Icc b c, (κ t).real Set.univ ≤ C) :
    (integrated κ b c).real Set.univ ≤ (c-b)*C := by
  rw [integrated_real_mass κ hm]
  calc
    _ ≤ ∫ _t in Set.Icc b c, C := by
      apply integral_mono_ae hm.integrableOn_Icc (integrable_const C)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hb t ht
    _ = _ := by rw [setIntegral_const,Real.volume_real_Icc_of_le hbc,smul_eq_mul]

theorem integrated_test (q : ℝ →ᵇ ℂ) :
    (∫ x, q x ∂integrated κ b c) = ∫ t in Set.Icc b c, ∫ x, q x ∂κ t := by
  letI := integrated_finite κ hm b c
  have he : integrated κ b c = (κ ∘ₖ Kernel.const Unit (volume.restrict (Set.Icc b c))) () := rfl
  rw [he]
  exact ProbabilityTheory.Kernel.integral_comp (q.integrable (integrated κ b c))

theorem integrated_test_integrable (q : ℝ →ᵇ ℂ) :
    IntegrableOn (fun t => ∫ x, q x ∂κ t) (Set.Icc b c) volume := by
  letI := integrated_finite κ hm b c
  have hq : Integrable q ((κ ∘ₖ Kernel.const Unit (volume.restrict (Set.Icc b c))) ()) :=
    q.integrable (integrated κ b c)
  exact hq.integral_comp

theorem integrated_characteristic (v : ℝ) :
    charFun (integrated κ b c) v = ∫ t in Set.Icc b c, charFun (κ t) v := by
  simpa only [charFun_eq_integral_innerProbChar] using
    integrated_test κ hm b c (innerProbChar v)

theorem characteristic_integrable (v : ℝ) :
    IntegrableOn (fun t => charFun (κ t) v) (Set.Icc b c) volume := by
  simpa only [charFun_eq_integral_innerProbChar] using
    integrated_test_integrable κ hm b c (innerProbChar v)

#print axioms integrated_mass
#print axioms integrated_finite
#print axioms integrated_real_mass
#print axioms integrated_mass_bound
#print axioms integrated_test
#print axioms integrated_test_integrable
#print axioms integrated_characteristic
#print axioms characteristic_integrable
end
end UnifiedTheory.Audit.KFCausalFiniteKernelInterval
