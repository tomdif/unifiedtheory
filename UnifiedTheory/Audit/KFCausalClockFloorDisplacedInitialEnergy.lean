/- The full averaged energy of the actual normalized boosted initial
state converges to the classical matter Hamiltonian expectation.
The form parameter t is fixed; no positive-time quantum propagation is
asserted and no Hamiltonian operator-domain membership is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyAssembly
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedAveragedDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedInitialEnergy
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedAveragedDomain (averagedVector averagedVector_energy)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy (energyOutput)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedCommonDomain (factorOutput)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFormOrbit (factorValue_eq)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy (seedEnergy)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyAssembly
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFactorLimits
open UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy (energyPolynomial)
open UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyLimit (energyPolynomial_tendsto)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw (clockLaw)
open UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase (toPaired)
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalDisplacedBoostParameters (boostQ boostK)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def boostedEnergy (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ t : ℝ) (p : Configuration) : ℝ :=
  ‖energyOutput ε hε h (hamiltonian_bound ε h hb) hh m g κ t
    (averagedVector ε a h hε ha hh hb m g κ t (boostQ h (h⁻¹ • p)) (boostK (h⁻¹ • p)) rfl)‖^2

theorem boostedEnergy_eq (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ t : ℝ) (p : Configuration)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) :
    boostedEnergy ε a h hε ha hh hb m g κ t p =
      energyPolynomial m g κ t (factorEnergy ε a h hε ha hh hb p) := by
  unfold boostedEnergy
  rw [averagedVector_energy ε a h hε ha hh hb m g κ t _ _ _ hm hg hκ]
  calc
    _ = ∫ θ, energyPolynomial m g κ t (fun i => ‖factorOutput ε a h hε ha hh hb
        (parameter (2*Real.pi*θ) (boostQ h (h⁻¹ • p)))
        (parameter (2*Real.pi*θ) (boostK (h⁻¹ • p))) modelDirections pointField i‖^2) ∂angleMeasure := by
      apply integral_congr_ae
      filter_upwards [] with θ
      have hq : parameter (2*Real.pi*θ) (boostQ h (h⁻¹ • p)) (.inr 0) = 0 :=
        (KFCausalClockFloorDisplacedBoostOrbit.parameter_clock (2*Real.pi*θ) _).trans rfl
      simp only [seedEnergy,energyPolynomial,factorValue_eq ε a h hε ha hh hb _ _ hq modelDirections pointField]
    _ = _ := energyPolynomial_integral _ _ _ _ _ _ (factor_energy_integrable ε a h hε ha hh hb p)

theorem boosted_initial_energy_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ t : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => boostedEnergy ε a (h n) hε ha (hh n) (hb n) m g κ t p) atTop
      (𝓝 (∫ s, hamiltonian ε m g κ t (0,toPaired p) s p.1 ∂clockLaw ε a)) := by
  simp_rw [boostedEnergy_eq ε a _ hε ha _ _ m g κ t p hm hg hκ]
  rw [hamiltonian_integral ε a m g κ t hε ha p]
  exact energyPolynomial_tendsto m g κ t _ _ (factorEnergy_tendsto ε a hε ha p h hh hb hz)

#print axioms boostedEnergy_eq
#print axioms boosted_initial_energy_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedInitialEnergy
