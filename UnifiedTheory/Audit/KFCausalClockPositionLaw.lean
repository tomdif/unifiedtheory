/- The actual Born configuration measure and its log-clock marginal for any
physical L2 vector. Normalization and interval tails follow from the L2 norm,
without assuming an evolved classical measure. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockPositionMass

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockPositionLaw
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorClockPositionMass (outsideMass)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

def configurationLaw (f : Hilbert) : Measure Configuration :=
  volume.withDensity (fun x => ENNReal.ofReal (‖f x‖^2))

def clockPositionLaw (f : Hilbert) : Measure ℝ := (configurationLaw f).map Prod.fst

theorem configurationLaw_apply (f : Hilbert) (A : Set Configuration) (hA : MeasurableSet A) :
    configurationLaw f A = ENNReal.ofReal (∫ x in A, ‖f x‖^2) := by
  rw [configurationLaw,withDensity_apply _ hA]
  exact (ofReal_integral_eq_lintegral_ofReal
    (((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)).integrableOn)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm

theorem configurationLaw_total (f : Hilbert) : configurationLaw f Set.univ = ENNReal.ofReal (‖f‖^2) := by
  rw [configurationLaw_apply f Set.univ MeasurableSet.univ,setIntegral_univ,← l2_norm_square]

theorem clockPositionLaw_apply (f : Hilbert) (A : Set ℝ) (hA : MeasurableSet A) :
    clockPositionLaw f A = ENNReal.ofReal (∫ x : Configuration in {x | x.1 ∈ A}, ‖f x‖^2) := by
  rw [clockPositionLaw,Measure.map_apply measurable_fst hA,
    configurationLaw_apply f _ (hA.preimage measurable_fst)]
  rfl

theorem clockPositionLaw_total (f : Hilbert) : clockPositionLaw f Set.univ = ENNReal.ofReal (‖f‖^2) := by
  rw [clockPositionLaw,Measure.map_apply measurable_fst MeasurableSet.univ,Set.preimage_univ,
    configurationLaw_total]

theorem clockPositionLaw_probability (f : Hilbert) (hf : ‖f‖ = 1) :
    IsProbabilityMeasure (clockPositionLaw f) where
  measure_univ := by rw [clockPositionLaw_total,hf,one_pow,ENNReal.ofReal_one]

theorem clockPositionLaw_outside (S R : ℝ) (f : Hilbert) :
    clockPositionLaw f (Set.Icc S R)ᶜ = ENNReal.ofReal (outsideMass S R f) :=
  clockPositionLaw_apply f _ measurableSet_Icc.compl

#print axioms configurationLaw_apply
#print axioms configurationLaw_total
#print axioms clockPositionLaw_apply
#print axioms clockPositionLaw_total
#print axioms clockPositionLaw_probability
#print axioms clockPositionLaw_outside

end
end UnifiedTheory.Audit.KFCausalClockPositionLaw
