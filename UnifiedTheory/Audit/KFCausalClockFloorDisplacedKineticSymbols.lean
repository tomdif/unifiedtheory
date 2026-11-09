/- Exact averaged kinetic energies and their classical squared-symbol
limits. Together with the clock expectation these cover indices 0--4. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedKineticSymbols
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedKineticEnergy
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentumDensity (pairing)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockLaw
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass halfMass dampedMass)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw (clockLaw)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (rotate physicalTail)
open UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase (toPaired)
open UnifiedTheory.Audit.KFCausalClassicalChargeMean (mean mean_eq_angle mean_const mean_add mean_mul_const)
open UnifiedTheory.Audit.KFCausalDisplacedClassicalAverage (mean_neg rotate_period)
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols (squaredSymbols)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

theorem orbitMomentum_continuous (p : Configuration) : Continuous (orbitMomentum p) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [orbitMomentum,physicalTail,KFCausalPairedModeCoordinates.backward,rotate] <;> fun_prop

theorem pairing_orbit_continuous (p : Configuration) (v : Transverse) :
    Continuous (fun θ => pairing v (orbitMomentum p θ)) := by
  unfold pairing
  exact continuous_finset_sum _ (fun i _ => continuous_const.mul ((continuous_apply i).comp (orbitMomentum_continuous p)))

def kineticMean (p : Configuration) (v : Transverse) : ℝ := mean (fun θ => (pairing v (orbitMomentum p θ))^2)

def averagedClockEnergy (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (p : Configuration) : ℝ :=
  ∫ θ, ‖boostedClockOutput ε a h hε ha hh p (2*Real.pi*θ)‖^2 ∂angleMeasure

def averagedKineticEnergy (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (p : Configuration) (v : Transverse) : ℝ :=
  ∫ θ, ‖boostedMomentumOutput ε a h hε ha hh p (2*Real.pi*θ) v‖^2 ∂angleMeasure

theorem averagedClockEnergy_eq (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (p : Configuration) :
    averagedClockEnergy ε a h hε ha hh p = halfMass ε a/clockMass ε a := by
  simp [averagedClockEnergy,boostedClockOutput_square]

theorem averagedKineticEnergy_eq (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (p : Configuration) (v : Transverse) :
    averagedKineticEnergy ε a h hε ha hh p v =
      (dampedMass ε a/clockMass ε a)*(kineticMean p v+|h| *kineticCorrection v) := by
  unfold averagedKineticEnergy
  simp_rw [boostedMomentumOutput_square,mul_comm (dampedMass ε a/clockMass ε a)]
  rw [← mean_eq_angle (fun θ => ((pairing v (orbitMomentum p θ))^2+|h| *kineticCorrection v)*
    (dampedMass ε a/clockMass ε a)),mean_mul_const,
    mean_add _ _ ((pairing_orbit_continuous p v).pow 2) continuous_const,mean_const]
  rfl

theorem kineticMean_forward (p : Configuration) (v : Transverse) :
    kineticMean p v = mean (fun θ => (pairing v (physicalTail (rotate θ (0,toPaired p)).2))^2) :=
  mean_neg (fun θ => (pairing v (physicalTail (rotate θ (0,toPaired p)).2))^2)
    (fun θ => by dsimp only; rw [rotate_period])

theorem squaredSymbol_kinetic (C r : ℝ) (p : Configuration) (θ : ℝ) (i : Fin 4) :
    squaredSymbols C r (rotate θ (0,toPaired p)) (kineticIndex i) =
      (pairing (modelDirections i) (physicalTail (rotate θ (0,toPaired p)).2))^2/C := by
  fin_cases i <;> rfl

theorem kineticSymbol_mean (C r : ℝ) (p : Configuration) (i : Fin 4) :
    mean (fun θ => squaredSymbols C r (rotate θ (0,toPaired p)) (kineticIndex i)) =
      kineticMean p (modelDirections i)/C := by
  simp_rw [squaredSymbol_kinetic,div_eq_mul_inv,mean_mul_const]
  rw [kineticMean_forward]

theorem kineticSymbol_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) (i : Fin 4) :
    Integrable (fun s => mean (fun θ => squaredSymbols (clock ε s) p.1
      (rotate θ (0,toPaired p)) (kineticIndex i))) (clockLaw ε a) := by
  simp_rw [kineticSymbol_mean,div_eq_mul_inv]
  exact (inverseClock_integrable ε a hε ha).const_mul _

theorem kineticSymbol_integral (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) (i : Fin 4) :
    (∫ s, mean (fun θ => squaredSymbols (clock ε s) p.1
      (rotate θ (0,toPaired p)) (kineticIndex i)) ∂clockLaw ε a) =
      (dampedMass ε a/clockMass ε a)*kineticMean p (modelDirections i) := by
  simp_rw [kineticSymbol_mean,div_eq_mul_inv]
  rw [integral_const_mul,inverseClock_integral ε a hε ha]
  exact mul_comm _ _

theorem averagedClockEnergy_classicalSymbol (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (p : Configuration) :
    averagedClockEnergy ε a h hε ha hh p =
      ∫ s, mean (fun θ => squaredSymbols (clock ε s) p.1 (rotate θ (0,toPaired p)) 0) ∂clockLaw ε a := by
  rw [averagedClockEnergy_eq]
  simp only [squaredSymbols,Matrix.cons_val_zero,mean_const]
  exact (clock_integral ε a hε ha).symm

theorem averagedKineticEnergy_classicalSymbol_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (i : Fin 4) (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => averagedKineticEnergy ε a (h n) hε ha (hh n) p (modelDirections i)) atTop
      (𝓝 (∫ s, mean (fun θ => squaredSymbols (clock ε s) p.1
        (rotate θ (0,toPaired p)) (kineticIndex i)) ∂clockLaw ε a)) := by
  simp_rw [averagedKineticEnergy_eq]
  rw [kineticSymbol_integral ε a hε ha]
  simpa only [abs_zero,zero_mul,add_zero] using
    ((hz.abs.mul_const (kineticCorrection (modelDirections i))).const_add (kineticMean p (modelDirections i))).const_mul
      (dampedMass ε a/clockMass ε a)

#print axioms orbitMomentum_continuous
#print axioms pairing_orbit_continuous
#print axioms averagedClockEnergy_eq
#print axioms averagedKineticEnergy_eq
#print axioms kineticMean_forward
#print axioms squaredSymbol_kinetic
#print axioms kineticSymbol_mean
#print axioms kineticSymbol_integrable
#print axioms kineticSymbol_integral
#print axioms averagedClockEnergy_classicalSymbol
#print axioms averagedKineticEnergy_classicalSymbol_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedKineticSymbols
