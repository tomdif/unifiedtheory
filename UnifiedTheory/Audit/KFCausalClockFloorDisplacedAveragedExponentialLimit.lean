/- Charge averaging commutes with the proved initial longitudinal-energy
limit. The hbar-independent bound follows from the integrable recentered
majorant, not from the fixed-hbar complex source estimates. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyLimit
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedFormOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedAveragedExponentialLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyIntegral
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyLimit
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredOutputLimit
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredMajorant
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass clockMass_positive)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization (gaussianMass gaussianMass_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw (clockLaw)

theorem boostedOutput_orbit_continuous (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) :
    Continuous (boostedOutput ε a h hε ha hh hb p) :=
  KFCausalClockFloorDisplacedFormOrbit.factorOutput_orbit_continuous ε a h hε ha hh hb _ _ _ _ 7

theorem boostedOutput_uniform_bound (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) :
    ∃ K : ℝ, ∀ (θ h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3),
      |h| ≤ ε/2 → |h| ≤ 1 → ‖boostedOutput ε a h hε ha hh hb p θ‖^2 ≤ K := by
  obtain ⟨B,hB⟩ := outputDensity_uniform_bound ε a hε ha.le p
  refine ⟨(∫ z : ℝ × Transverse, B*clockWeight ε a hε z.1*gaussianEnvelope (1/4) z.2)/
    (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)),?_⟩
  intro θ h hh hb hs h1
  rw [boostedOutput_integral ε a h hε ha hh hb hs h1 p θ]
  apply div_le_div_of_nonneg_right _ (mul_pos (clockMass_positive ε a hε ha)
    (gaussianMass_positive _ _ (groundWidth_positive 1 one_ne_zero)
      (neutralWidth_positive 1 one_ne_zero))).le
  apply integral_mono (outputDensity_integrable ε a h hε ha hh hb hs h1 p θ)
    (productEnvelope_integrable ε a B hε ha)
  intro z
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB θ h hh hb hs h1 z)

def averagedEnergy (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) : ℝ :=
  ∫ θ, ‖boostedOutput ε a h hε ha hh hb p (2*Real.pi*θ)‖^2 ∂angleMeasure

def averagedLimit (ε a : ℝ) (p : Configuration) : ℝ :=
  ∫ θ, (∫ s : ℝ, Real.exp ((p.1+KFCausalClassicalChargePhase.shear
    (KFCausalClassicalChargePhase.rotate (-(2*Real.pi*θ)) (0,KFCausalClassicalPhysicalPhase.toPaired p)))/clock ε s)/
      clock ε s ∂clockLaw ε a) ∂angleMeasure

theorem averagedEnergy_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => averagedEnergy ε a (h n) hε ha (hh n) (hb n) p) atTop
      (𝓝 (averagedLimit ε a p)) := by
  obtain ⟨K,hK⟩ := boostedOutput_uniform_bound ε a hε ha p
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => K)
  · exact Eventually.of_forall (fun n =>
      (((boostedOutput_orbit_continuous ε a (h n) hε ha (hh n) (hb n) p).norm.pow 2).comp
        (continuous_const.mul continuous_id)).aestronglyMeasurable)
  · filter_upwards [eventually_small ε hε h hz] with n hn
    filter_upwards [] with θ
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hK (2*Real.pi*θ) (h n) (hh n) (hb n) hn.1 hn.2
  · exact integrable_const K
  · exact Eventually.of_forall (fun θ => boostedOutput_energy_clockLaw ε a hε ha p (2*Real.pi*θ) h hh hb hz)

#print axioms boostedOutput_orbit_continuous
#print axioms boostedOutput_uniform_bound
#print axioms averagedEnergy_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedAveragedExponentialLimit
