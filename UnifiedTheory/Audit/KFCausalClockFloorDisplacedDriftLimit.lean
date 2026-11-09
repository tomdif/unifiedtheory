/- Semiclassical limits of the actual ordered-output drift pairings.
The limiting clock-law integrals retain the shear and both displaced
field powers. No positive-time propagation limit is used. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorDriftCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftIntegral
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftDensity
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldIntegral
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldDensity (fieldLimitDensity)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyIntegral (boostedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyLimit
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredOutputLimit (limitDensity eventually_small)
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredMajorant
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredFields (fieldPower orbitCentre)
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect (realClock realDefect)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
open UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyIdentification (dampedClock_square)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy (dampedClockFunction)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization (gaussianMass gaussianMass_positive)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chartIso)
open UnifiedTheory.Audit.KFCausalCoupledTestPullback (clock_change_integral)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (shear rotate)
open UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase (toPaired)

def driftLimit (ε a : ℝ) (p : Configuration) (θ : ℝ) : ℝ :=
  ∫ s : ℝ, drift ε (defect ε s)*
    (Real.exp ((p.1+shear (rotate (-θ) (0,toPaired p)))/clock ε s)/clock ε s) ∂clockLaw ε a

def fieldDriftLimit (ε a : ℝ) (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) : ℝ :=
  (fieldPower j l (orbitCentre p θ))^2*driftLimit ε a p θ

theorem drift_clockExponential_law (ε a r : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    (∫ u, realDrift ε hε u*clockExponential ε a hε r u)/clockMass ε a =
      ∫ s : ℝ, drift ε (defect ε s)*(Real.exp (r/clock ε s)/clock ε s) ∂clockLaw ε a := by
  have he : (∫ u, realDrift ε hε u*clockExponential ε a hε r u) =
      ∫ s, drift ε (defect ε s)*Real.exp (r/clock ε s)*‖dampedClockFunction ε a s‖^2 := by
    rw [← clock_change_integral ε hε]
    apply integral_congr_ae
    filter_upwards [] with s
    have hc : (chartIso ε hε).symm (chart ε s) = s := (chartIso ε hε).symm_apply_apply s
    rw [realDrift,realDefect,hc,clockExponential]
    calc
      _ = (drift ε (defect ε s)*Real.exp (r/realClock ε hε (chart ε s)))*
          ((Real.exp s+ε)*clockWeight ε a hε (chart ε s)) := by ring
      _ = _ := by rw [clockWeight_chart ε a s hε,realClock,hc]
  rw [he,clockLaw,integral_withDensity_eq_integral_toReal_smul
    (clockDensity_continuous ε a).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),← integral_div]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s),smul_eq_mul,dampedClock_square ε a s hε]
  unfold clockDensity
  ring

theorem drift_limitDensity_normalized (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) (θ : ℝ) :
    (∫ z, realDrift ε hε z.1*limitDensity ε a hε p θ z)/
      (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) = driftLimit ε a p θ := by
  have he : (∫ z, realDrift ε hε z.1*limitDensity ε a hε p θ z) =
      (∫ u, realDrift ε hε u*clockExponential ε a hε (p.1+shear (rotate (-θ) (0,toPaired p))) u)*
        gaussianMass (groundWidth 1) (neutralWidth 1) := by
    calc
      _ = ∫ z : ℝ × Transverse,
          (realDrift ε hε z.1*clockExponential ε a hε (p.1+shear (rotate (-θ) (0,toPaired p))) z.1)*
            gaussianEnvelope 2 z.2 := by
        apply integral_congr_ae
        filter_upwards [] with z
        unfold limitDensity clockExponential
        ring
      _ = _ := by
        rw [Measure.volume_eq_prod ℝ Transverse,
          integral_prod_mul (fun u => realDrift ε hε u*clockExponential ε a hε
            (p.1+shear (rotate (-θ) (0,toPaired p))) u) (gaussianEnvelope 2),gaussianEnvelope_mass]
  rw [he,mul_div_mul_right _ _ (gaussianMass_positive _ _ (groundWidth_positive 1 one_ne_zero)
    (neutralWidth_positive 1 one_ne_zero)).ne']
  exact drift_clockExponential_law ε a _ hε ha

theorem drift_fieldLimitDensity_normalized (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    (∫ z, realDrift ε hε z.1*fieldLimitDensity ε a hε p θ l j z)/
      (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) = fieldDriftLimit ε a p θ l j := by
  simp only [fieldLimitDensity,mul_left_comm (realDrift ε hε _) ((fieldPower j l (orbitCentre p θ))^2),
    integral_const_mul,mul_div_assoc]
  rw [drift_limitDensity_normalized ε a hε ha p θ]
  rfl

theorem boostedOutput_drift_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) (θ : ℝ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => driftPair ε hε (boostedOutput ε a (h n) hε ha (hh n) (hb n) p θ)) atTop
      (𝓝 (driftLimit ε a p θ)) := by
  rw [← drift_limitDensity_normalized ε a hε ha p θ]
  apply ((output_drift_integral_tendsto ε a hε ha p θ h hh hb hz).div_const
    (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1))).congr'
  filter_upwards [eventually_small ε hε h hz] with n hn
  exact (boostedOutput_drift_integral ε a (h n) hε ha (hh n) (hb n) hn.1 hn.2 p θ).symm

theorem boostedFieldOutput_drift_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => driftPair ε hε (boostedFieldOutput ε a (h n) hε ha (hh n) (hb n) p θ l j)) atTop
      (𝓝 (fieldDriftLimit ε a p θ l j)) := by
  rw [← drift_fieldLimitDensity_normalized ε a hε ha p θ l j]
  apply ((field_drift_integral_tendsto ε a hε ha p θ l j h hh hb hz).div_const
    (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1))).congr'
  filter_upwards [eventually_small ε hε h hz] with n hn
  exact (boostedFieldOutput_drift_integral ε a (h n) hε ha (hh n) (hb n) hn.1 hn.2 p θ l j).symm

#print axioms drift_clockExponential_law
#print axioms drift_limitDensity_normalized
#print axioms drift_fieldLimitDensity_normalized
#print axioms boostedOutput_drift_tendsto
#print axioms boostedFieldOutput_drift_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftLimit
