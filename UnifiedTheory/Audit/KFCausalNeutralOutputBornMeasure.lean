/- Positive neutral-momentum measures of all eight actual energy-output
channels, and of an L2 family of such outputs. The averaged measure is
constructed as a measurable kernel integral and has exactly squared L2 mass. -/
import UnifiedTheory.Audit.KFCausalL2BornMeasurability
import UnifiedTheory.Audit.KFCausalNeutralMomentumProbability
import UnifiedTheory.Audit.KFCausalNeutralOutputPolarization
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralOutputBornMeasure
noncomputable section
open MeasureTheory ProbabilityTheory BoundedContinuousFunction
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit (dualPhysical)
open UnifiedTheory.Audit.KFCausalNeutralTranslationOutput
open UnifiedTheory.Audit.KFCausalNeutralMomentumProbability (law law_characteristic symbol_continuous)
open UnifiedTheory.Audit.KFCausalNeutralCanonicalForm (operator_action)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

local instance hilbertMeasurable : MeasurableSpace Hilbert := borel _
local instance hilbertBorel : BorelSpace Hilbert := ⟨rfl⟩
local instance outputMeasurable : MeasurableSpace Outputs := borel _
local instance outputBorel : BorelSpace Outputs := ⟨rfl⟩

theorem channel_mass (h : ℝ) (f : Hilbert) : law h f Set.univ = ENNReal.ofReal (‖f‖^2) := by
  rw [law,Measure.map_apply (symbol_continuous h).measurable MeasurableSet.univ,
    Set.preimage_univ,KFCausalL2BornLaw.law_total,dualPhysical.norm_map]

theorem channel_finite (h : ℝ) (f : Hilbert) : IsFiniteMeasure (law h f) where
  measure_univ_lt_top := by rw [channel_mass]; exact ENNReal.ofReal_lt_top

theorem channel_measurable (h : ℝ) : Measurable (law h) := by
  apply (Measure.measurable_map _ (symbol_continuous h).measurable).comp
  exact (KFCausalL2BornMeasurability.law_measurable volume).comp
    dualPhysical.continuous.borel_measurable

def outputLaw (h : ℝ) (y : Outputs) : Measure ℝ := ∑ i : Fin 8, law h (y i)

theorem outputLaw_mass (h : ℝ) (y : Outputs) :
    outputLaw h y Set.univ = ENNReal.ofReal (‖y‖^2) := by
  simp only [outputLaw,Measure.finset_sum_apply,channel_mass]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖y i‖),PiLp.norm_sq_eq_of_L2]

theorem outputLaw_finite (h : ℝ) (y : Outputs) : IsFiniteMeasure (outputLaw h y) where
  measure_univ_lt_top := by rw [outputLaw_mass]; exact ENNReal.ofReal_lt_top

theorem outputLaw_measurable (h : ℝ) : Measurable (outputLaw h) := by
  apply Finset.measurable_sum
  intro i _
  exact (channel_measurable h).comp (PiLp.continuous_apply 2 _ i).measurable

theorem outputLaw_characteristic (h v : ℝ) (y : Outputs) :
    charFun (outputLaw h y) v = inner ℂ y (translateOutput (h*v) y) := by
  letI (i : Fin 8) : IsFiniteMeasure (law h (y i)) := channel_finite h (y i)
  rw [charFun_eq_integral_innerProbChar,outputLaw,integral_finset_sum_measure
    (fun i _ => (innerProbChar v).integrable _)]
  simp only [← charFun_eq_integral_innerProbChar,law_characteristic,
    KFCausalCanonicalWeylAlgebra.characteristic,operator_action,PiLp.inner_apply]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

def outputKernel (h : ℝ) (y : Lp Outputs 2 μ) : Kernel Ω ℝ :=
  ⟨fun x => outputLaw h (y x), (outputLaw_measurable h).comp (Lp.stronglyMeasurable y).measurable⟩

def averagedLaw (h : ℝ) (y : Lp Outputs 2 μ) : Measure ℝ :=
  μ.bind (outputKernel μ h y)

theorem averagedLaw_mass (h : ℝ) (y : Lp Outputs 2 μ) :
    averagedLaw μ h y Set.univ = ENNReal.ofReal (‖y‖^2) := by
  rw [averagedLaw,Measure.bind_apply MeasurableSet.univ (outputKernel μ h y).aemeasurable]
  change (∫⁻ x, outputLaw h (y x) Set.univ ∂μ) = _
  simp_rw [outputLaw_mass]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable y)).mp (Lp.memLp y))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),← l2_norm_square]

theorem averagedLaw_finite (h : ℝ) (y : Lp Outputs 2 μ) : IsFiniteMeasure (averagedLaw μ h y) where
  measure_univ_lt_top := by rw [averagedLaw_mass]; exact ENNReal.ofReal_lt_top

theorem averagedLaw_characteristic (h v : ℝ) (y : Lp Outputs 2 μ) :
    charFun (averagedLaw μ h y) v = KFCausalNeutralOutputPolarization.expectation μ (h*v) y := by
  letI := averagedLaw_finite μ h y
  have he : averagedLaw μ h y = ((outputKernel μ h y) ∘ₖ (Kernel.const Unit μ)) () := rfl
  rw [charFun_eq_integral_innerProbChar,he]
  rw [ProbabilityTheory.Kernel.integral_comp]
  · change (∫ x, ∫ z, innerProbChar v z ∂outputLaw h (y x) ∂μ) = _
    simp_rw [← charFun_eq_integral_innerProbChar,outputLaw_characteristic]
    rw [KFCausalNeutralOutputPolarization.expectation,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(translateOutput (h*v)).coeFn_compLp y] with x hx
    rw [hx]
  · exact (innerProbChar v).integrable (averagedLaw μ h y)

#print axioms channel_mass
#print axioms channel_finite
#print axioms channel_measurable
#print axioms outputLaw_mass
#print axioms outputLaw_finite
#print axioms outputLaw_measurable
#print axioms outputLaw_characteristic
#print axioms averagedLaw_mass
#print axioms averagedLaw_finite
#print axioms averagedLaw_characteristic
end
end UnifiedTheory.Audit.KFCausalNeutralOutputBornMeasure
