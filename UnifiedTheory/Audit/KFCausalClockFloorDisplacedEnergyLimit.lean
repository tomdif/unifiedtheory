/- The normalized ordered longitudinal energy on each actual boosted
charge orbit converges to the physical clock-law average of the classical
clock-plus-shear exponential. This is an initial-energy theorem, not a
quantum propagation theorem or a complete matter-energy limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorRecenteredOutputLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredOutputLimit
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredMajorant
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredJacobian
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyIntegral
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect (realClock realClock_positive)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedEnergyIdentification (exponential_clock_bound)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor)
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

def clockExponential (ε a : ℝ) (hε : 0 < ε) (r u : ℝ) : ℝ :=
  clockWeight ε a hε u*Real.exp (r/realClock ε hε u)

theorem clockExponential_integrable (ε a r : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (clockExponential ε a hε r) := by
  have hc : Continuous (realClock ε hε) :=
    (Real.continuous_exp.comp (chartIso ε hε).symm.toHomeomorph.continuous).add continuous_const
  have hw : Continuous (clockWeight ε a hε) := by
    apply (clockJacobian_continuous ε hε).mul
    unfold clockFactor
    fun_prop
  have he : Continuous (fun u => Real.exp (r/realClock ε hε u)) :=
    Real.continuous_exp.comp (continuous_const.div hc (fun u => (realClock_positive ε hε u).ne'))
  apply ((clockWeight_integrable ε a hε ha).const_mul (Real.exp (|r|/ε))).mono'
    (hw.mul he).aestronglyMeasurable
  filter_upwards [] with u
  have hp : 0 ≤ clockWeight ε a hε u :=
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  change ‖clockWeight ε a hε u*Real.exp (r/realClock ε hε u)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp (Real.exp_pos _).le)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (exponential_clock_bound ε r u hε) hp

theorem limitDensity_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) (θ : ℝ) :
    Integrable (limitDensity ε a hε p θ) := by
  rw [Measure.volume_eq_prod ℝ Transverse]
  apply ((clockExponential_integrable ε a
    (p.1+KFCausalClassicalChargePhase.shear
      (KFCausalClassicalChargePhase.rotate (-θ) (0,KFCausalClassicalPhysicalPhase.toPaired p))) hε ha).mul_prod
        (gaussianEnvelope_integrable 2 (by norm_num))).congr
  filter_upwards [] with z
  dsimp only [clockExponential,limitDensity]
  ring

theorem limitDensity_mass (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) (θ : ℝ) :
    (∫ z, limitDensity ε a hε p θ z) =
      (∫ u, clockExponential ε a hε
        (p.1+KFCausalClassicalChargePhase.shear
          (KFCausalClassicalChargePhase.rotate (-θ) (0,KFCausalClassicalPhysicalPhase.toPaired p))) u)*
        gaussianMass (groundWidth 1) (neutralWidth 1) := by
  have hi := limitDensity_integrable ε a hε ha p θ
  rw [Measure.volume_eq_prod ℝ Transverse] at hi ⊢
  rw [integral_prod _ hi]
  simp only [limitDensity,integral_mul_const,integral_const_mul,gaussianEnvelope_mass]
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with u
  unfold clockExponential
  ring

theorem clockExponential_law (ε a r : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    (∫ u, clockExponential ε a hε r u)/clockMass ε a =
      ∫ s : ℝ, Real.exp (r/clock ε s)/clock ε s ∂clockLaw ε a := by
  have he : (∫ u, clockExponential ε a hε r u) =
      ∫ s, Real.exp (r/clock ε s)*‖dampedClockFunction ε a s‖^2 := by
    rw [← clock_change_integral ε hε]
    apply integral_congr_ae
    filter_upwards [] with s
    have hc : (chartIso ε hε).symm (chart ε s) = s := (chartIso ε hε).symm_apply_apply s
    rw [clockExponential,← mul_assoc,clockWeight_chart ε a s hε,realClock,hc]
    ring
  rw [he,clockLaw,integral_withDensity_eq_integral_toReal_smul
    (clockDensity_continuous ε a).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),← integral_div]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s),smul_eq_mul,dampedClock_square ε a s hε]
  unfold clockDensity
  ring

theorem limitDensity_normalized (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) (θ : ℝ) :
    (∫ z, limitDensity ε a hε p θ z)/(clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) =
      ∫ s : ℝ, Real.exp ((p.1+KFCausalClassicalChargePhase.shear
        (KFCausalClassicalChargePhase.rotate (-θ) (0,KFCausalClassicalPhysicalPhase.toPaired p)))/clock ε s)/
          clock ε s ∂clockLaw ε a := by
  rw [limitDensity_mass ε a hε ha p θ,
    mul_div_mul_right _ _ (gaussianMass_positive _ _ (groundWidth_positive 1 one_ne_zero)
      (neutralWidth_positive 1 one_ne_zero)).ne']
  exact clockExponential_law ε a _ hε ha

theorem boostedOutput_energy_clockLaw (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) (θ : ℝ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ‖boostedOutput ε a (h n) hε ha (hh n) (hb n) p θ‖^2) atTop
      (𝓝 (∫ s : ℝ, Real.exp ((p.1+KFCausalClassicalChargePhase.shear
        (KFCausalClassicalChargePhase.rotate (-θ) (0,KFCausalClassicalPhysicalPhase.toPaired p)))/clock ε s)/
          clock ε s ∂clockLaw ε a)) := by
  rw [← limitDensity_normalized ε a hε ha p θ]
  apply ((outputDensity_integral_tendsto ε a hε ha p θ h hh hb hz).div_const
    (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1))).congr'
  filter_upwards [eventually_small ε hε h hz] with n hn
  exact (boostedOutput_integral ε a (h n) hε ha (hh n) (hb n) hn.1 hn.2 p θ).symm

theorem boostedOutput_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (θ : ℝ) :
    (KFCausalPhysicalCircleAction.action h hh θ
      (KFCausalClockFloorBoostedKineticLimit.boostedState ε a h hε ha hh
        (KFCausalClockFloorEvolvedCharacteristics.positionFrequency p.1 p.2)),
      boostedOutput ε a h hε ha hh hb p θ) ∈
        (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph := by
  rw [KFCausalClockFloorDisplacedBoostOrbit.action_boostedState]
  exact KFCausalClockFloorDisplacedCommonDomain.factorOutput_graph ε a h hε ha hh hb _ _
    (KFCausalClockFloorDisplacedBoostOrbit.boost_orbit_clock_displacement h p θ) _ _ 7

#print axioms clockExponential_integrable
#print axioms limitDensity_integrable
#print axioms limitDensity_mass
#print axioms clockExponential_law
#print axioms limitDensity_normalized
#print axioms boostedOutput_energy_clockLaw
#print axioms boostedOutput_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyLimit
