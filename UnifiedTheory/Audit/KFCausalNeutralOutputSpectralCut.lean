/- Every measurable-set evaluation of the actual averaged output law is
a continuous squared norm. This yields measurability in the L2 output
state without any jointly selected pointwise representatives. -/
import UnifiedTheory.Audit.KFCausalNeutralOutputBornMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralOutputSpectralCut
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (JointHilbert)
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit (dualPhysical)
open UnifiedTheory.Audit.KFCausalComplementaryMomentumTests (momentumSymbol)
open UnifiedTheory.Audit.KFCausalNeutralMomentumProbability (law symbol_continuous)
open UnifiedTheory.Audit.KFCausalNeutralTranslationOutput (Outputs)
open UnifiedTheory.Audit.KFCausalNeutralOutputBornMeasure
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

abbrev DualOutputs := PiLp 2 (fun _ : Fin 8 => JointHilbert 5 1)

def channelCut (h : ℝ) (A : Set ℝ) (hA : MeasurableSet A) : Hilbert →L[ℂ] JointHilbert 5 1 :=
  (KFCausalL2BornMeasurability.cut volume (momentumSymbol h 2 ⁻¹' A)
    ((symbol_continuous h).measurable hA)).comp
      (dualPhysical : Hilbert →L[ℂ] JointHilbert 5 1)

theorem channel_cut (h : ℝ) (A : Set ℝ) (hA : MeasurableSet A) (f : Hilbert) :
    law h f A = ENNReal.ofReal (‖channelCut h A hA f‖^2) := by
  rw [law,Measure.map_apply (symbol_continuous h).measurable hA,
    KFCausalL2BornMeasurability.law_cut volume _ ((symbol_continuous h).measurable hA)]
  rfl

def outputCut (h : ℝ) (A : Set ℝ) (hA : MeasurableSet A) : Outputs →L[ℂ] DualOutputs where
  toFun y := WithLp.toLp 2 (fun i => channelCut h A hA (y i))
  map_add' x y := by ext i; simp [map_add]
  map_smul' z y := by ext i; simp [map_smul]
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => (channelCut h A hA).continuous.comp (PiLp.continuous_apply 2 _ i)))

theorem output_cut (h : ℝ) (A : Set ℝ) (hA : MeasurableSet A) (y : Outputs) :
    outputLaw h y A = ENNReal.ofReal (‖outputCut h A hA y‖^2) := by
  simp only [outputLaw,Measure.finset_sum_apply,channel_cut h A hA]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖channelCut h A hA (y i)‖),
    PiLp.norm_sq_eq_of_L2]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

theorem averaged_cut (h : ℝ) (A : Set ℝ) (hA : MeasurableSet A) (y : Lp Outputs 2 μ) :
    averagedLaw μ h y A = ENNReal.ofReal (‖(outputCut h A hA).compLp y‖^2) := by
  rw [averagedLaw,Measure.bind_apply hA (outputKernel μ h y).aemeasurable]
  change (∫⁻ x, outputLaw h (y x) A ∂μ) = _
  simp_rw [output_cut h A hA]
  have he : (fun x => ENNReal.ofReal (‖outputCut h A hA (y x)‖^2)) =ᵐ[μ]
      (fun x => ENNReal.ofReal (‖(outputCut h A hA).compLp y x‖^2)) := by
    filter_upwards [(outputCut h A hA).coeFn_compLp y] with x hx
    rw [hx]
  rw [lintegral_congr_ae he]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ((outputCut h A hA).compLp y))).mp
      (Lp.memLp ((outputCut h A hA).compLp y)))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),← l2_norm_square]

theorem averaged_eval_continuous (h : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    Continuous (fun y : Lp Outputs 2 μ => averagedLaw μ h y A) := by
  simp_rw [averaged_cut μ h A hA]
  exact ENNReal.continuous_ofReal.comp ((((outputCut h A hA).compLpL 2 μ).continuous.norm).pow 2)

theorem averaged_measurable (h : ℝ) :
    @Measurable (Lp Outputs 2 μ) (Measure ℝ) (borel _) _ (averagedLaw μ h) := by
  letI : MeasurableSpace (Lp Outputs 2 μ) := borel _
  letI : BorelSpace (Lp Outputs 2 μ) := ⟨rfl⟩
  exact Measure.measurable_of_measurable_coe _
    (fun A hA => (averaged_eval_continuous μ h A hA).measurable)

#print axioms channel_cut
#print axioms output_cut
#print axioms averaged_cut
#print axioms averaged_eval_continuous
#print axioms averaged_measurable
end
end UnifiedTheory.Audit.KFCausalNeutralOutputSpectralCut
