/- Initial energy limits for both actual ordered field factors, including
their circle averages. The limiting centre-field factors need not vanish. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldEnergyLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldIntegral
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldDensity
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredFields
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredOutputLimit (eventually_small outputDensity)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass clockMass_positive)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization (gaussianMass gaussianMass_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw (clockLaw)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (rotate shear)
open UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase (toPaired)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def fieldEnergyLimit (ε a : ℝ) (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) : ℝ :=
  (fieldPower j l (orbitCentre p θ))^2*
    ∫ s : ℝ, Real.exp ((p.1+shear (rotate (-θ) (0,toPaired p)))/clock ε s)/clock ε s ∂clockLaw ε a

theorem fieldLimitDensity_normalized (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    (∫ z, fieldLimitDensity ε a hε p θ l j z)/(clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) =
      fieldEnergyLimit ε a p θ l j := by
  unfold fieldLimitDensity
  rw [integral_const_mul,mul_div_assoc,
    KFCausalClockFloorDisplacedEnergyLimit.limitDensity_normalized ε a hε ha p θ]
  rfl

theorem boostedFieldOutput_integral (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hs : |h| ≤ ε/2) (h1 : |h| ≤ 1)
    (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    ‖boostedFieldOutput ε a h hε ha hh hb p θ l j‖^2 =
      (∫ z, fieldDensity ε a hε h p θ l j z)/(clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)) := by
  have hi := fieldDensity_integrable ε a h hε ha hh hb hs h1 p θ l j
  rw [Measure.volume_eq_prod ℝ Transverse] at hi
  rw [boostedFieldOutput_mass,Measure.volume_eq_prod ℝ Transverse,integral_prod _ hi]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  unfold fieldDensity outputDensity
  ring

theorem boostedFieldOutput_energy_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ‖boostedFieldOutput ε a (h n) hε ha (hh n) (hb n) p θ l j‖^2) atTop
      (𝓝 (fieldEnergyLimit ε a p θ l j)) := by
  rw [← fieldLimitDensity_normalized ε a hε ha p θ l j]
  apply ((fieldDensity_integral_tendsto ε a hε ha p θ l j h hh hb hz).div_const
    (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1))).congr'
  filter_upwards [eventually_small ε hε h hz] with n hn
  exact (boostedFieldOutput_integral ε a (h n) hε ha (hh n) (hb n) hn.1 hn.2 p θ l j).symm

theorem boostedFieldOutput_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (θ : ℝ) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    (KFCausalPhysicalCircleAction.action h hh θ
      (KFCausalClockFloorBoostedKineticLimit.boostedState ε a h hε ha hh
        (KFCausalClockFloorEvolvedCharacteristics.positionFrequency p.1 p.2)),
      boostedFieldOutput ε a h hε ha hh hb p θ l j) ∈
        (KFCausalClockFloorCommonDomain.energyFactor ε hε h KFCausalPhysicalEnergyFactors.modelDirections l (fieldIndex j)).graph := by
  rw [KFCausalClockFloorDisplacedBoostOrbit.action_boostedState]
  exact KFCausalClockFloorDisplacedCommonDomain.factorOutput_graph ε a h hε ha hh hb _ _
    (KFCausalClockFloorDisplacedBoostOrbit.boost_orbit_clock_displacement h p θ) _ _ _

theorem boostedFieldOutput_orbit_continuous (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    Continuous (fun θ => boostedFieldOutput ε a h hε ha hh hb p θ l j) :=
  KFCausalClockFloorDisplacedFormOrbit.factorOutput_orbit_continuous ε a h hε ha hh hb _ _ _ _ _

theorem boostedFieldOutput_uniform_bound (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    ∃ K : ℝ, ∀ (θ h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3),
      |h| ≤ ε/2 → |h| ≤ 1 → ∀ j : Fin 2, ‖boostedFieldOutput ε a h hε ha hh hb p θ l j‖^2 ≤ K := by
  obtain ⟨B,hB⟩ := fieldDensity_uniform_bound ε a hε ha.le p l
  refine ⟨(∫ z : ℝ × Transverse, B*KFCausalClockFloorRecenteredMajorant.clockWeight ε a hε z.1*
    KFCausalClockFloorRecenteredMajorant.gaussianEnvelope (1/8) z.2)/
      (clockMass ε a*gaussianMass (groundWidth 1) (neutralWidth 1)),?_⟩
  intro θ h hh hb hs h1 j
  rw [boostedFieldOutput_integral ε a h hε ha hh hb hs h1 p θ l j]
  apply div_le_div_of_nonneg_right _ (mul_pos (clockMass_positive ε a hε ha)
    (gaussianMass_positive _ _ (groundWidth_positive 1 one_ne_zero) (neutralWidth_positive 1 one_ne_zero))).le
  apply integral_mono (fieldDensity_integrable ε a h hε ha hh hb hs h1 p θ l j)
    (fieldEnvelope_integrable ε a B hε ha)
  intro z
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB θ h hh hb hs h1 j z)

def averagedFieldEnergy (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) : ℝ :=
  ∫ θ, ‖boostedFieldOutput ε a h hε ha hh hb p (2*Real.pi*θ) l j‖^2 ∂angleMeasure

def averagedFieldLimit (ε a : ℝ) (p : Configuration) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) : ℝ :=
  ∫ θ, fieldEnergyLimit ε a p (2*Real.pi*θ) l j ∂angleMeasure

theorem averagedFieldEnergy_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (l : Transverse →L[ℝ] ℝ) (j : Fin 2)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => averagedFieldEnergy ε a (h n) hε ha (hh n) (hb n) p l j) atTop
      (𝓝 (averagedFieldLimit ε a p l j)) := by
  obtain ⟨K,hK⟩ := boostedFieldOutput_uniform_bound ε a hε ha p l
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => K)
  · exact Eventually.of_forall (fun n =>
      (((boostedFieldOutput_orbit_continuous ε a (h n) hε ha (hh n) (hb n) p l j).norm.pow 2).comp
        (continuous_const.mul continuous_id)).aestronglyMeasurable)
  · filter_upwards [eventually_small ε hε h hz] with n hn
    filter_upwards [] with θ
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hK (2*Real.pi*θ) (h n) (hh n) (hb n) hn.1 hn.2 j
  · exact integrable_const K
  · exact Eventually.of_forall (fun θ => boostedFieldOutput_energy_tendsto ε a hε ha p (2*Real.pi*θ) l j h hh hb hz)

#print axioms fieldLimitDensity_normalized
#print axioms boostedFieldOutput_integral
#print axioms boostedFieldOutput_energy_tendsto
#print axioms boostedFieldOutput_graph
#print axioms boostedFieldOutput_orbit_continuous
#print axioms boostedFieldOutput_uniform_bound
#print axioms averagedFieldEnergy_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldEnergyLimit
