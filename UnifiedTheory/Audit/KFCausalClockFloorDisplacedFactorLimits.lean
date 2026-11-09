/- All eight initial averaged factor limits, on the actual displaced
boost orbit, and integrability of their classical charge averages. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedKineticSymbols

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedFactorLimits
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedCommonDomain (factorOutput)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFormOrbit (factorOutput_orbit_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedKineticSymbols
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockLaw (clock_integrable)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw (clockLaw clockLaw_probability)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (rotate)
open UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase (toPaired)
open UnifiedTheory.Audit.KFCausalClassicalChargeMean (mean mean_eq_angle mean_const)
open UnifiedTheory.Audit.KFCausalDisplacedClassicalAverage (mean_neg rotate_period)
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols (squaredSymbols)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalDisplacedBoostParameters (boostQ boostK)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)

def factorEnergy (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (i : Fin 8) : ℝ :=
  ∫ θ, ‖factorOutput ε a h hε ha hh hb (parameter (2*Real.pi*θ) (boostQ h (h⁻¹ • p)))
    (parameter (2*Real.pi*θ) (boostK (h⁻¹ • p))) modelDirections pointField i‖^2 ∂angleMeasure

def symbolMean (ε : ℝ) (p : Configuration) (s : ℝ) (i : Fin 8) : ℝ :=
  mean (fun θ => squaredSymbols (clock ε s) p.1 (rotate θ (0,toPaired p)) i)

def classicalFactor (ε a : ℝ) (p : Configuration) (i : Fin 8) : ℝ :=
  ∫ s, symbolMean ε p s i ∂clockLaw ε a

theorem factor_energy_integrable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (i : Fin 8) :
    Integrable (fun θ => ‖factorOutput ε a h hε ha hh hb
      (parameter (2*Real.pi*θ) (boostQ h (h⁻¹ • p)))
      (parameter (2*Real.pi*θ) (boostK (h⁻¹ • p))) modelDirections pointField i‖^2) angleMeasure := by
  have hc := (factorOutput_orbit_continuous ε a h hε ha hh hb
    (boostQ h (h⁻¹ • p)) (boostK (h⁻¹ • p)) modelDirections pointField i).comp
      (f := fun θ : ℝ => 2*Real.pi*θ) (continuous_const.mul continuous_id)
  have hm := continuous_angle_memLp _ hc
  exact (memLp_two_iff_integrable_sq_norm hm.1).mp hm

theorem symbolMean_reverse (ε : ℝ) (p : Configuration) (s : ℝ) (i : Fin 8) :
    mean (fun θ => squaredSymbols (clock ε s) p.1 (rotate (-θ) (0,toPaired p)) i) = symbolMean ε p s i :=
  mean_neg (fun θ => squaredSymbols (clock ε s) p.1 (rotate θ (0,toPaired p)) i)
    (fun θ => by dsimp only; rw [rotate_period])

theorem fieldSymbol_mean (ε : ℝ) (p : Configuration) (s : ℝ) (j : Fin 2) :
    (∫ θ, KFCausalClockFloorDisplacedFieldSymbols.fieldSymbol ε p pointField j θ s ∂angleMeasure) =
      symbolMean ε p s (KFCausalClockFloorDisplacedFieldIntegral.fieldIndex j) := by
  simp_rw [KFCausalClockFloorDisplacedFieldSymbols.fieldSymbol_eq]
  rw [← mean_eq_angle (fun θ => squaredSymbols (clock ε s) p.1 (rotate (-θ) (0,toPaired p))
    (KFCausalClockFloorDisplacedFieldIntegral.fieldIndex j))]
  exact symbolMean_reverse ε p s _

theorem exponentialSymbol_mean (ε : ℝ) (p : Configuration) (s : ℝ) :
    (∫ θ, KFCausalClockFloorDisplacedExponentialSymbol.symbol ε p θ s ∂angleMeasure) = symbolMean ε p s 7 := by
  change (∫ θ, (fun φ => squaredSymbols (clock ε s) p.1 (rotate (-φ) (0,toPaired p)) 7)
    (2*Real.pi*θ) ∂angleMeasure) = _
  rw [← mean_eq_angle (fun θ => squaredSymbols (clock ε s) p.1 (rotate (-θ) (0,toPaired p)) 7)]
  exact symbolMean_reverse ε p s 7

theorem symbolMean_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) (i : Fin 8) :
    Integrable (fun s => symbolMean ε p s i) (clockLaw ε a) := by
  letI := clockLaw_probability ε a hε ha
  have hf (j : Fin 2) : Integrable (fun s => symbolMean ε p s (KFCausalClockFloorDisplacedFieldIntegral.fieldIndex j))
      (clockLaw ε a) := by
    simpa only [fieldSymbol_mean] using
      (KFCausalClockFloorDisplacedFieldSymbols.fieldSymbol_integrable ε a hε ha p pointField j).integral_prod_right
  fin_cases i
  · change Integrable (fun s => mean (fun _ : ℝ => clock ε s)) (clockLaw ε a)
    simpa only [mean_const] using clock_integrable ε a hε ha
  · exact kineticSymbol_integrable ε a hε ha p 0
  · exact kineticSymbol_integrable ε a hε ha p 1
  · exact kineticSymbol_integrable ε a hε ha p 2
  · exact kineticSymbol_integrable ε a hε ha p 3
  · exact hf 0
  · exact hf 1
  · simpa only [exponentialSymbol_mean] using
      (KFCausalClockFloorDisplacedExponentialSymbol.symbol_integrable ε a hε ha p).integral_prod_right

theorem factorEnergy_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (i : Fin 8) :
    Tendsto (fun n => factorEnergy ε a (h n) hε ha (hh n) (hb n) p i) atTop
      (𝓝 (classicalFactor ε a p i)) := by
  fin_cases i
  · change Tendsto (fun n => averagedClockEnergy ε a (h n) hε ha (hh n) p) _ _
    simp_rw [averagedClockEnergy_classicalSymbol]
    exact tendsto_const_nhds
  · exact averagedKineticEnergy_classicalSymbol_tendsto ε a hε ha p 0 h hh hz
  · exact averagedKineticEnergy_classicalSymbol_tendsto ε a hε ha p 1 h hh hz
  · exact averagedKineticEnergy_classicalSymbol_tendsto ε a hε ha p 2 h hh hz
  · exact averagedKineticEnergy_classicalSymbol_tendsto ε a hε ha p 3 h hh hz
  · exact KFCausalClockFloorDisplacedFieldSymbols.averagedFieldEnergy_classicalSymbol_tendsto ε a hε ha p 0 h hh hb hz
  · exact KFCausalClockFloorDisplacedFieldSymbols.averagedFieldEnergy_classicalSymbol_tendsto ε a hε ha p 1 h hh hb hz
  · exact KFCausalClockFloorDisplacedExponentialSymbol.averagedEnergy_classicalSymbol_tendsto ε a hε ha p h hh hb hz

#print axioms factor_energy_integrable
#print axioms symbolMean_reverse
#print axioms fieldSymbol_mean
#print axioms exponentialSymbol_mean
#print axioms symbolMean_integrable
#print axioms factorEnergy_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedFactorLimits
