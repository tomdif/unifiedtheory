/- The inverse state-orbit orientation gives the same normalized classical
charge average. This identifies the candidate factor symbols on the actual
displacement parameter orbit; convergence of the quantum energies is separate. -/
import UnifiedTheory.Audit.KFCausalDisplacedPhysicalPhase
import UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalDisplacedClassicalAverage
noncomputable section
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (Phase rotate)
open UnifiedTheory.Audit.KFCausalClassicalChargeMean (mean)
open UnifiedTheory.Audit.KFCausalDisplacedPhysicalPhase
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalDisplacedBoostParameters (boostQ boostK)
open UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase (toPaired)
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian (hamiltonian hamiltonian_eq_factor_mean)
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols (squaredSymbols)
open UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy (energyPolynomial)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)

theorem mean_neg (f : ℝ → ℝ) (hf : Function.Periodic f (2*Real.pi)) :
    mean (fun θ => f (-θ)) = mean f := by
  unfold mean
  rw [intervalIntegral.integral_comp_neg,neg_zero]
  congr 1
  simpa only [neg_add_cancel,zero_add] using hf.intervalIntegral_add_eq (-(2*Real.pi)) 0

theorem rotate_period (θ : ℝ) (z : Phase) : rotate (θ+2*Real.pi) z = rotate θ z := by
  ext i <;> rcases i with i | i <;> fin_cases i <;> simp [rotate]

theorem mean_phase_parameter (h : ℝ) (q k : Joint 2 4) (F : Phase → ℝ) :
    mean (fun θ => F (phase h (parameter θ q) (parameter θ k))) =
      mean (fun θ => F (rotate θ (phase h q k))) := by
  simp_rw [phase_parameter]
  exact mean_neg (fun θ => F (rotate θ (phase h q k)))
    (fun θ => congrArg F (rotate_period θ (phase h q k)))

theorem hamiltonian_eq_displaced_mean (ε m g κ t h s r : ℝ) (q k : Joint 2 4) :
    hamiltonian ε m g κ t (phase h q k) s r =
      mean (fun θ => energyPolynomial m g κ t
        (squaredSymbols (clock ε s) r (phase h (parameter θ q) (parameter θ k)))) := by
  rw [mean_phase_parameter h q k (fun z => energyPolynomial m g κ t (squaredSymbols (clock ε s) r z))]
  exact hamiltonian_eq_factor_mean ε m g κ t (phase h q k) s r

theorem boosted_candidate_mean (ε m g κ t h s : ℝ) (hh : h ≠ 0) (p : Configuration) :
    mean (fun θ => energyPolynomial m g κ t (squaredSymbols (clock ε s) p.1
      (phase h (parameter θ (boostQ h (h⁻¹ • p))) (parameter θ (boostK (h⁻¹ • p)))))) =
      hamiltonian ε m g κ t (0,toPaired p) s p.1 := by
  rw [← hamiltonian_eq_displaced_mean,phase_boost h hh]

#print axioms mean_neg
#print axioms rotate_period
#print axioms mean_phase_parameter
#print axioms hamiltonian_eq_displaced_mean
#print axioms boosted_candidate_mean

end
end UnifiedTheory.Audit.KFCausalDisplacedClassicalAverage
