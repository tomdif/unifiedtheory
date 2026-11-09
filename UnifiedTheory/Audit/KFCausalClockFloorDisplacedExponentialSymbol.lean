/- Identification of the averaged longitudinal limit with the classical
squared symbol at index 7, averaged against the physical clock law. The
exchange of clock and charge integrals and the orbit orientation are proved. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedAveragedExponentialLimit
import UnifiedTheory.Audit.KFCausalClassicalVacuumShearBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedExponentialSymbol
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedAveragedExponentialLimit
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw (clockLaw clockLaw_probability)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock clock_above_floor)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (rotate shear)
open UnifiedTheory.Audit.KFCausalClassicalChargeMean (mean mean_eq_angle shear_continuous)
open UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase (toPaired)
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols (squaredSymbols)
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds (phaseSize)
open UnifiedTheory.Audit.KFCausalClassicalVacuumShearBounds
  (phaseSize_nonnegative phaseSize_rotate shear_abs_bound)
open UnifiedTheory.Audit.KFCausalDisplacedClassicalAverage (mean_neg rotate_period)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def symbol (ε : ℝ) (p : Configuration) (θ s : ℝ) : ℝ :=
  Real.exp ((p.1+shear (rotate (-(2*Real.pi*θ)) (0,toPaired p)))/clock ε s)/clock ε s

theorem symbol_continuous (ε : ℝ) (hε : 0 < ε) (p : Configuration) :
    Continuous (fun x : ℝ × ℝ => symbol ε p x.1 x.2) := by
  have hs := (shear_continuous (0,toPaired p)).comp
    (f := fun x : ℝ × ℝ => -(2*Real.pi*x.1)) (by fun_prop)
  have hc : Continuous (fun x : ℝ × ℝ => clock ε x.2) := by unfold clock; fun_prop
  exact (Real.continuous_exp.comp ((continuous_const.add hs).div hc
    (fun x => (clock_positive ε x.2 hε.le).ne'))).div hc
      (fun x => (clock_positive ε x.2 hε.le).ne')

theorem symbol_bound (ε : ℝ) (hε : 0 < ε) (p : Configuration) (θ s : ℝ) :
    ‖symbol ε p θ s‖ ≤ Real.exp ((|p.1|+2*phaseSize (0,toPaired p))/ε)/ε := by
  have hC := clock_positive ε s hε.le
  have hεC := (clock_above_floor ε s).le
  have hs := (le_abs_self (shear (rotate (-(2*Real.pi*θ)) (0,toPaired p)))).trans
    (shear_abs_bound (rotate (-(2*Real.pi*θ)) (0,toPaired p)))
  rw [phaseSize_rotate] at hs
  have hR : 0 ≤ |p.1|+2*phaseSize (0,toPaired p) := by
    have := phaseSize_nonnegative (0,toPaired p)
    positivity
  have hr : p.1+shear (rotate (-(2*Real.pi*θ)) (0,toPaired p)) ≤
      |p.1|+2*phaseSize (0,toPaired p) := add_le_add (le_abs_self p.1) hs
  have hd := (div_le_div_of_nonneg_right hr hC.le).trans
    (div_le_div_of_nonneg_left hR hε hεC)
  rw [symbol,Real.norm_eq_abs,abs_of_pos (div_pos (Real.exp_pos _) hC)]
  exact (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hd) hC.le).trans
    (div_le_div_of_nonneg_left (Real.exp_pos _).le hε hεC)

theorem symbol_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) :
    Integrable (fun x : ℝ × ℝ => symbol ε p x.1 x.2) (angleMeasure.prod (clockLaw ε a)) := by
  letI := clockLaw_probability ε a hε ha
  exact (integrable_const (Real.exp ((|p.1|+2*phaseSize (0,toPaired p))/ε)/ε)).mono'
    (symbol_continuous ε hε p).aestronglyMeasurable
    (Eventually.of_forall (fun x => symbol_bound ε hε p x.1 x.2))

theorem averagedLimit_classicalSymbol (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) :
    averagedLimit ε a p = ∫ s, mean (fun θ => squaredSymbols (clock ε s) p.1
      (rotate θ (0,toPaired p)) 7) ∂clockLaw ε a := by
  letI := clockLaw_probability ε a hε ha
  change (∫ θ, (∫ s, symbol ε p θ s ∂clockLaw ε a) ∂angleMeasure) = _
  rw [integral_integral_swap (symbol_integrable ε a hε ha p)]
  apply integral_congr_ae
  filter_upwards [] with s
  change (∫ θ, (fun φ => Real.exp ((p.1+shear (rotate (-φ) (0,toPaired p)))/clock ε s)/clock ε s)
    (2*Real.pi*θ) ∂angleMeasure) = _
  rw [← mean_eq_angle (fun φ => Real.exp ((p.1+shear (rotate (-φ) (0,toPaired p)))/clock ε s)/clock ε s)]
  exact mean_neg (fun θ => squaredSymbols (clock ε s) p.1 (rotate θ (0,toPaired p)) 7)
    (fun θ => by dsimp only; rw [rotate_period])

theorem averagedEnergy_classicalSymbol_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => averagedEnergy ε a (h n) hε ha (hh n) (hb n) p) atTop
      (𝓝 (∫ s, mean (fun θ => squaredSymbols (clock ε s) p.1
        (rotate θ (0,toPaired p)) 7) ∂clockLaw ε a)) := by
  rw [← averagedLimit_classicalSymbol ε a hε ha p]
  exact averagedEnergy_tendsto ε a hε ha p h hh hb hz

#print axioms symbol_continuous
#print axioms symbol_bound
#print axioms symbol_integrable
#print axioms averagedLimit_classicalSymbol
#print axioms averagedEnergy_classicalSymbol_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedExponentialSymbol
