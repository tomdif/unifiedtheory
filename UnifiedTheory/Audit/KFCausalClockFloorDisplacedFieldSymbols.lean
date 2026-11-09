/- Identification of both averaged ordered field-energy limits with the
existing classical squared symbols at indices 5 and 6. Clock/angle Fubini
and the reversal of orbit orientation are justified, not assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldEnergyLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldSymbols
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldIntegral (fieldIndex)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldEnergyLimit
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredFields
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedExponentialSymbol (symbol symbol_continuous symbol_bound)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw (clockLaw clockLaw_probability)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (rotate physicalTail)
open UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase (toPaired)
open UnifiedTheory.Audit.KFCausalClassicalChargeMean (mean mean_eq_angle)
open UnifiedTheory.Audit.KFCausalDisplacedClassicalAverage (mean_neg rotate_period)
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols (squaredSymbols fieldValue)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

theorem orbitCentre_continuous (p : Configuration) : Continuous (orbitCentre p) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [orbitCentre,physicalTail,KFCausalPairedModeCoordinates.backward,rotate] <;> fun_prop

theorem centrePower_bound (l : Transverse →L[ℝ] ℝ) (j : Fin 2) (Q : Transverse) :
    (fieldPower j l Q)^2 ≤ (fieldBound l Q)^2 := by
  have h := fieldPower_square_bound j 0 (by norm_num) Q 0 l
  have he : KFCausalClockFloorDisplacedPhaseLimit.rescaledPosition 0 Q 0 = Q := by
    ext i
    simp [KFCausalClockFloorDisplacedPhaseLimit.rescaledPosition]
  simpa only [he,KFCausalClockFloorCenteredEstimates.energy_eq,Pi.zero_apply,zero_pow (by decide : 2 ≠ 0),
    zero_add,zero_div,add_zero,one_pow,mul_one] using h

def fieldSymbol (ε : ℝ) (p : Configuration) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) (θ s : ℝ) : ℝ :=
  (fieldPower j l (orbitCentre p (2*Real.pi*θ)))^2*symbol ε p θ s

theorem fieldSymbol_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    Integrable (fun x : ℝ × ℝ => fieldSymbol ε p l j x.1 x.2) (angleMeasure.prod (clockLaw ε a)) := by
  letI := clockLaw_probability ε a hε ha
  obtain ⟨D,hD⟩ := fieldBound_orbit l p
  have hc : Continuous (fun x : ℝ × ℝ => fieldSymbol ε p l j x.1 x.2) := by
    have hQ := (orbitCentre_continuous p).comp
      (f := fun x : ℝ × ℝ => 2*Real.pi*x.1) (by fun_prop)
    exact (((l.continuous.comp hQ).pow (j.val+1)).pow 2).mul (symbol_continuous ε hε p)
  apply (integrable_const (|D| *(Real.exp ((|p.1|+2*KFCausalClassicalVacuumEnergyBounds.phaseSize (0,toPaired p))/ε)/ε))).mono'
    hc.aestronglyMeasurable
  filter_upwards [] with x
  have hd : (fieldPower j l (orbitCentre p (2*Real.pi*x.1)))^2 ≤ |D| :=
    (centrePower_bound l j _).trans ((hD _).trans (le_abs_self D))
  rw [fieldSymbol,norm_mul,norm_pow,Real.norm_eq_abs,sq_abs]
  exact mul_le_mul hd (symbol_bound ε hε p x.1 x.2) (norm_nonneg _) (abs_nonneg D)

theorem fieldSymbol_eq (ε : ℝ) (p : Configuration) (j : Fin 2) (θ s : ℝ) :
    fieldSymbol ε p pointField j θ s =
      squaredSymbols (clock ε s) p.1 (rotate (-(2*Real.pi*θ)) (0,toPaired p)) (fieldIndex j) := by
  fin_cases j <;> simp [fieldSymbol,fieldPower,orbitCentre,symbol,squaredSymbols,fieldIndex,fieldValue] <;> ring

theorem averagedFieldLimit_classicalSymbol (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (j : Fin 2) :
    averagedFieldLimit ε a p pointField j =
      ∫ s, mean (fun θ => squaredSymbols (clock ε s) p.1 (rotate θ (0,toPaired p)) (fieldIndex j)) ∂clockLaw ε a := by
  letI := clockLaw_probability ε a hε ha
  have he : averagedFieldLimit ε a p pointField j =
      ∫ θ, (∫ s, fieldSymbol ε p pointField j θ s ∂clockLaw ε a) ∂angleMeasure := by
    simp only [averagedFieldLimit,fieldEnergyLimit,fieldSymbol,symbol,integral_const_mul]
  rw [he,integral_integral_swap (fieldSymbol_integrable ε a hε ha p pointField j)]
  apply integral_congr_ae
  filter_upwards [] with s
  simp_rw [fieldSymbol_eq]
  rw [← mean_eq_angle (fun φ => squaredSymbols (clock ε s) p.1 (rotate (-φ) (0,toPaired p)) (fieldIndex j))]
  exact mean_neg (fun θ => squaredSymbols (clock ε s) p.1 (rotate θ (0,toPaired p)) (fieldIndex j))
    (fun θ => by dsimp only; rw [rotate_period])

theorem averagedFieldEnergy_classicalSymbol_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (j : Fin 2) (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0)
    (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => averagedFieldEnergy ε a (h n) hε ha (hh n) (hb n) p pointField j) atTop
      (𝓝 (∫ s, mean (fun θ => squaredSymbols (clock ε s) p.1
        (rotate θ (0,toPaired p)) (fieldIndex j)) ∂clockLaw ε a)) := by
  rw [← averagedFieldLimit_classicalSymbol ε a hε ha p j]
  exact averagedFieldEnergy_tendsto ε a hε ha p pointField j h hh hb hz

#print axioms orbitCentre_continuous
#print axioms centrePower_bound
#print axioms fieldSymbol_integrable
#print axioms fieldSymbol_eq
#print axioms averagedFieldLimit_classicalSymbol
#print axioms averagedFieldEnergy_classicalSymbol_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldSymbols
