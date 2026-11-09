/- The actual exponential and ordered field drift pairings admit
integrable recentered densities, with semiclassical dominated convergence. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftIntegral
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldEnergyLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftDensity
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDriftCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftIntegral
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldIntegral
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyIntegral (boostedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldDensity
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredOutputLimit
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredMajorant
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization (gaussianMass)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)

theorem output_drift_integrable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hs : |h| ≤ ε/2) (h1 : |h| ≤ 1) (p : Configuration) (θ : ℝ) :
    Integrable (fun z => realDrift ε hε z.1*outputDensity ε a hε h p θ z) :=
  drift_mul_integrable volume ε hε Prod.fst measurable_fst _
    (outputDensity_integrable ε a h hε ha hh hb hs h1 p θ)

theorem field_drift_integrable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hs : |h| ≤ ε/2) (h1 : |h| ≤ 1)
    (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    Integrable (fun z => realDrift ε hε z.1*fieldDensity ε a hε h p θ l j z) :=
  drift_mul_integrable volume ε hε Prod.fst measurable_fst _
    (fieldDensity_integrable ε a h hε ha hh hb hs h1 p θ l j)

theorem boostedOutput_drift_integral (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hs : |h| ≤ ε/2) (h1 : |h| ≤ 1) (p : Configuration) (θ : ℝ) :
    driftPair ε hε (boostedOutput ε a h hε ha hh hb p θ) =
      (∫ z, realDrift ε hε z.1*outputDensity ε a hε h p θ z) /
        (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) := by
  have hi := output_drift_integrable ε a h hε ha hh hb hs h1 p θ
  rw [Measure.volume_eq_prod ℝ Transverse] at hi
  rw [boostedOutput_pairing,Measure.volume_eq_prod ℝ Transverse,integral_prod _ hi]
  simp only [outputDensity,← mul_assoc,integral_const_mul]

theorem boostedFieldOutput_drift_integral (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hs : |h| ≤ ε/2) (h1 : |h| ≤ 1)
    (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    driftPair ε hε (boostedFieldOutput ε a h hε ha hh hb p θ l j) =
      (∫ z, realDrift ε hε z.1*fieldDensity ε a hε h p θ l j z) /
        (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) := by
  have hi := field_drift_integrable ε a h hε ha hh hb hs h1 p θ l j
  rw [Measure.volume_eq_prod ℝ Transverse] at hi
  rw [boostedFieldOutput_pairing,Measure.volume_eq_prod ℝ Transverse,integral_prod _ hi]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  unfold fieldDensity outputDensity
  ring

theorem output_drift_integral_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (θ : ℝ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, realDrift ε hε z.1*outputDensity ε a hε (h n) p θ z) atTop
      (𝓝 (∫ z, realDrift ε hε z.1*limitDensity ε a hε p θ z)) := by
  obtain ⟨B,hB⟩ := outputDensity_uniform_bound ε a hε ha.le p
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z : ℝ × Transverse => (1/ε)*(B*clockWeight ε a hε z.1*gaussianEnvelope (1/4) z.2))
  · exact Eventually.of_forall (fun n => (((realDrift_continuous ε hε).comp continuous_fst).mul
      (outputDensity_continuous ε a (h n) hε (hb n) p θ)).aestronglyMeasurable)
  · filter_upwards [eventually_small ε hε h hz] with n hn
    filter_upwards [] with z
    rw [norm_mul,Real.norm_eq_abs (realDrift ε hε z.1)]
    exact mul_le_mul (realDrift_bound ε hε z.1)
      (hB θ (h n) (hh n) (hb n) hn.1 hn.2 z) (norm_nonneg _) (by positivity)
  · exact (productEnvelope_integrable ε a B hε ha).const_mul (1/ε)
  · exact Eventually.of_forall (fun z => (outputDensity_tendsto ε a hε p θ h hh hz z).const_mul _)

theorem field_drift_integral_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, realDrift ε hε z.1*fieldDensity ε a hε (h n) p θ l j z) atTop
      (𝓝 (∫ z, realDrift ε hε z.1*fieldLimitDensity ε a hε p θ l j z)) := by
  obtain ⟨B,hB⟩ := fieldDensity_uniform_bound ε a hε ha.le p l
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z : ℝ × Transverse => (1/ε)*(B*clockWeight ε a hε z.1*gaussianEnvelope (1/8) z.2))
  · exact Eventually.of_forall (fun n => (((realDrift_continuous ε hε).comp continuous_fst).mul
      (fieldDensity_continuous ε a (h n) hε (hb n) p θ l j)).aestronglyMeasurable)
  · filter_upwards [eventually_small ε hε h hz] with n hn
    filter_upwards [] with z
    rw [norm_mul,Real.norm_eq_abs (realDrift ε hε z.1)]
    exact mul_le_mul (realDrift_bound ε hε z.1)
      (hB θ (h n) (hh n) (hb n) hn.1 hn.2 j z) (norm_nonneg _) (by positivity)
  · exact (fieldEnvelope_integrable ε a B hε ha).const_mul (1/ε)
  · exact Eventually.of_forall (fun z => (fieldDensity_tendsto ε a hε p θ l j h hh hz z).const_mul _)

#print axioms output_drift_integrable
#print axioms field_drift_integrable
#print axioms boostedOutput_drift_integral
#print axioms boostedFieldOutput_drift_integral
#print axioms output_drift_integral_tendsto
#print axioms field_drift_integral_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftDensity
