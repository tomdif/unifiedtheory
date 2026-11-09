/- Linear integration identities for the eight-factor energy polynomial,
and its identification with the full classical matter Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedFactorLimits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyAssembly
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy (energyPolynomial)
open UnifiedTheory.Audit.KFCausalClassicalChargeMean (mean mean_eq_angle shear_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFactorLimits (symbolMean classicalFactor symbolMean_integrable)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedKineticSymbols (pairing_orbit_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedKineticEnergy (orbitMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentumDensity (pairing)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw (clockLaw)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (rotate physicalTail)
open UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase (toPaired)
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols (squaredSymbols fieldValue fieldValue_rotate)
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian (hamiltonian hamiltonian_eq_factor_mean)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def energyCoefficient (m g κ t : ℝ) : Fin 8 → ℝ :=
  ![1/2,1/2,1/2,Real.exp (2*t)/2,Real.exp (2*t)/2,
    Real.exp (2*t)*(m/2),Real.exp (2*t)*(g/4),Real.exp (2*t)*κ]

theorem energyPolynomial_sum (m g κ t : ℝ) (F : Fin 8 → ℝ) :
    energyPolynomial m g κ t F = ∑ i, energyCoefficient m g κ t i*F i := by
  simp [energyPolynomial,energyCoefficient,Fin.sum_univ_succ]
  ring

theorem energyPolynomial_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (m g κ t : ℝ) (F : X → Fin 8 → ℝ) (hF : ∀ i, Integrable (fun x => F x i) μ) :
    Integrable (fun x => energyPolynomial m g κ t (F x)) μ := by
  simp_rw [energyPolynomial_sum]
  exact integrable_finset_sum _ (fun i _ => (hF i).const_mul _)

theorem energyPolynomial_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (m g κ t : ℝ) (F : X → Fin 8 → ℝ) (hF : ∀ i, Integrable (fun x => F x i) μ) :
    (∫ x, energyPolynomial m g κ t (F x) ∂μ) =
      energyPolynomial m g κ t (fun i => ∫ x, F x i ∂μ) := by
  simp_rw [energyPolynomial_sum]
  rw [integral_finset_sum _ (fun i _ => (hF i).const_mul _)]
  simp only [integral_const_mul]

theorem energyPolynomial_mean (m g κ t : ℝ) (F : ℝ → Fin 8 → ℝ)
    (hF : ∀ i, Continuous (fun θ => F θ i)) :
    mean (fun θ => energyPolynomial m g κ t (F θ)) =
      energyPolynomial m g κ t (fun i => mean (fun θ => F θ i)) := by
  simp_rw [mean_eq_angle]
  exact energyPolynomial_integral angleMeasure m g κ t _ (fun i =>
    (continuous_angle_memLp _ ((hF i).comp (continuous_const.mul continuous_id))).integrable (by norm_num))

theorem squaredSymbols_orbit_continuous (C r : ℝ) (p : Configuration) (i : Fin 8) :
    Continuous (fun θ => squaredSymbols C r (rotate θ (0,toPaired p)) i) := by
  have hk (v : Transverse) : Continuous (fun θ => pairing v (physicalTail (rotate θ (0,toPaired p)).2)) := by
    simpa only [Function.comp_def,orbitMomentum,neg_neg] using (pairing_orbit_continuous p v).comp continuous_neg
  have hf : Continuous (fun θ => fieldValue (rotate θ (0,toPaired p))) := by
    simp_rw [fieldValue_rotate]
    fun_prop
  have he := Real.continuous_exp.comp (((continuous_const (y := r)).add (shear_continuous (0,toPaired p))).div_const C)
  fin_cases i
  · exact continuous_const
  · exact ((hk _).pow 2).div_const C
  · exact ((hk _).pow 2).div_const C
  · exact ((hk _).pow 2).div_const C
  · exact ((hk _).pow 2).div_const C
  · exact ((hf.pow 2).mul he).div_const C
  · exact ((hf.pow 4).mul he).div_const C
  · exact he.div_const C

theorem hamiltonian_symbolMean (ε m g κ t : ℝ) (p : Configuration) (s : ℝ) :
    hamiltonian ε m g κ t (0,toPaired p) s p.1 = energyPolynomial m g κ t (symbolMean ε p s) := by
  rw [hamiltonian_eq_factor_mean,energyPolynomial_mean m g κ t _ (squaredSymbols_orbit_continuous _ _ p)]
  rfl

theorem hamiltonian_integrable (ε a m g κ t : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) :
    Integrable (fun s => hamiltonian ε m g κ t (0,toPaired p) s p.1) (clockLaw ε a) := by
  simp_rw [hamiltonian_symbolMean]
  exact energyPolynomial_integrable _ _ _ _ _ _ (symbolMean_integrable ε a hε ha p)

theorem hamiltonian_integral (ε a m g κ t : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) :
    (∫ s, hamiltonian ε m g κ t (0,toPaired p) s p.1 ∂clockLaw ε a) =
      energyPolynomial m g κ t (classicalFactor ε a p) := by
  simp_rw [hamiltonian_symbolMean]
  exact energyPolynomial_integral _ _ _ _ _ _ (symbolMean_integrable ε a hε ha p)

#print axioms energyPolynomial_sum
#print axioms energyPolynomial_integrable
#print axioms energyPolynomial_integral
#print axioms energyPolynomial_mean
#print axioms squaredSymbols_orbit_continuous
#print axioms hamiltonian_symbolMean
#print axioms hamiltonian_integrable
#print axioms hamiltonian_integral

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyAssembly
