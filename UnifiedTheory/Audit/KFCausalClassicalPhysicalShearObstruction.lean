/- The classical shear obstruction on the actual twelve-dimensional phase
space and the existing full matter Hamiltonian. Clock coordinates are inserted
into their physical slots. No fixed-hbar quantum counterexample is asserted. -/
import UnifiedTheory.Audit.KFCausalClassicalShearEnergyObstruction
import UnifiedTheory.Audit.KFCausalClassicalMatterSmooth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClassicalPhysicalShearObstruction
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClassicalShearEnergyObstruction
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterSmooth (fullHamiltonian)
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q p q_apply p_apply)
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum (kineticMean kineticMean_eq)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (response)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)

def physicalState (x : State) : Phase :=
  (WithLp.toLp 2 (fun i => if i = .inr 0 then x.2.1 else x.1.1 i),
   WithLp.toLp 2 (fun i => if i = .inr 0 then x.2.2 else x.1.2 i))

theorem physical_clock (x : State) :
    q (.inr 0) (physicalState x) = x.2.1 ∧ p (.inr 0) (physicalState x) = x.2.2 := by
  simp [q_apply,p_apply,physicalState]

theorem physical_shear (x : State) (θ : ℝ) :
    shear (rotate θ (physicalState x)) = shear (rotate θ x.1) := by
  simp [shear_rotate,diagonalPairing,crossPairing,physicalState]

theorem physical_field (x : State) (θ : ℝ) :
    fieldValue (rotate θ (physicalState x)) = fieldValue (rotate θ x.1) := by
  simp [fieldValue_rotate,physicalState]

theorem physical_kinetic (x : State) (t : ℝ) :
    kineticMean t (physicalState x) = kineticMean t x.1 := by
  simp [kineticMean_eq,physicalState]

theorem physical_weightedMean (m g κ C : ℝ) (x : State) :
    weightedMean m g κ C (physicalState x) = weightedMean m g κ C x.1 := by
  simp only [weightedMean,potential,physical_field,physical_shear]

theorem physical_weightedTilt (m g κ C : ℝ) (x : State) :
    weightedTilt m g κ C (physicalState x) = weightedTilt m g κ C x.1 := by
  simp only [weightedTilt,potential,physical_field,physical_shear]

theorem physical_energy (m g : ℝ) (x : State) :
    fullHamiltonian (1/2) m g 1 (0,physicalState x) = energy m g x := by
  unfold fullHamiltonian
  rw [(physical_clock x).1,(physical_clock x).2]
  simp only [energy,hamiltonian,physical_kinetic,physical_weightedMean]

def fullShear (m g : ℝ) (z : Phase) : ℝ :=
  response (1/2) (q (.inr 0) z)*amplitude (1/2) 0 (q (.inr 0) z) (p (.inr 0) z)*
    weightedTilt m g 1 (clock (1/2) (q (.inr 0) z)) z/(clock (1/2) (q (.inr 0) z))^2

theorem physical_signedShear (m g : ℝ) (x : State) :
    fullShear m g (physicalState x) = signedShear m g x := by
  unfold fullShear
  rw [(physical_clock x).1,(physical_clock x).2,physical_weightedTilt]
  rfl

def fullLaw (r : ℝ) : Measure Phase :=
  ENNReal.ofReal (mixingWeight r) • Measure.dirac (physicalState (sample r))+
    ENNReal.ofReal (1-mixingWeight r) • Measure.dirac (physicalState baseline)

instance fullLaw_probability (r : ℝ) : IsProbabilityMeasure (fullLaw r) where
  measure_univ := by
    simp only [fullLaw,Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    rw [← ENNReal.ofReal_add (mixingWeight_bounds r).1 (by linarith [(mixingWeight_bounds r).2])]
    norm_num

theorem fullLaw_integrable (r : ℝ) (F : Phase → ℝ) : Integrable F (fullLaw r) := by
  have h0 : Integrable F (Measure.dirac (physicalState (sample r))) := integrable_dirac (by finiteness)
  have h1 : Integrable F (Measure.dirac (physicalState baseline)) := integrable_dirac (by finiteness)
  exact (h0.smul_measure (by finiteness)).add_measure (h1.smul_measure (by finiteness))

theorem fullLaw_integral (r : ℝ) (F : Phase → ℝ) :
    (∫ z, F z ∂fullLaw r) = ∫ x, F (physicalState x) ∂law r := by
  have h0 : Integrable F (Measure.dirac (physicalState (sample r))) := integrable_dirac (by finiteness)
  have h1 : Integrable F (Measure.dirac (physicalState baseline)) := integrable_dirac (by finiteness)
  rw [fullLaw,integral_add_measure (h0.smul_measure (by finiteness)) (h1.smul_measure (by finiteness)),law_integral]
  simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (mixingWeight_bounds r).1,
    ENNReal.toReal_ofReal (show 0 ≤ 1-mixingWeight r by linarith [(mixingWeight_bounds r).2]),smul_eq_mul]

theorem fullLaw_energy (m g r : ℝ) (hr : r ≠ 0) :
    (∫ z, fullHamiltonian (1/2) m g 1 (0,z) ∂fullLaw r) = 7/2-3*mixingWeight r := by
  rw [fullLaw_integral]
  simp only [physical_energy]
  exact law_energy m g r hr

theorem fullLaw_energy_bounds (m g r : ℝ) (hr : r ≠ 0) :
    0 ≤ (∫ z, fullHamiltonian (1/2) m g 1 (0,z) ∂fullLaw r) ∧
    (∫ z, fullHamiltonian (1/2) m g 1 (0,z) ∂fullLaw r) ≤ 7/2 := by
  simp only [fullLaw_integral,physical_energy]
  exact law_energy_bounds m g r hr

theorem fullLaw_shear_lower (m g r : ℝ) (hr : 480 ≤ r^2) :
    r^2/32 ≤ ∫ z, fullShear m g z ∂fullLaw r := by
  simp only [fullLaw_integral,physical_signedShear]
  exact law_shear_lower m g r hr

theorem exists_bounded_energy_large_shear (m g M : ℝ) :
    ∃ r : ℝ, r ≠ 0 ∧ 0 ≤ (∫ z, fullHamiltonian (1/2) m g 1 (0,z) ∂fullLaw r) ∧
      (∫ z, fullHamiltonian (1/2) m g 1 (0,z) ∂fullLaw r) ≤ 7/2 ∧
      M < (∫ z, fullShear m g z ∂fullLaw r) := by
  simp only [fullLaw_integral,physical_energy,physical_signedShear]
  exact KFCausalClassicalShearEnergyObstruction.exists_bounded_energy_large_shear m g M

theorem no_affine_energy_bound (m g : ℝ) :
    ¬ ∃ A B : ℝ, ∀ z : Phase,
      fullShear m g z ≤ A*fullHamiltonian (1/2) m g 1 (0,z)+B := by
  rintro ⟨A,B,h⟩
  apply KFCausalClassicalShearEnergyObstruction.no_affine_energy_bound m g
  refine ⟨A,B,fun x => ?_⟩
  simpa only [physical_signedShear,physical_energy] using h (physicalState x)

#print axioms physical_clock
#print axioms physical_shear
#print axioms physical_field
#print axioms physical_kinetic
#print axioms physical_weightedMean
#print axioms physical_weightedTilt
#print axioms physical_energy
#print axioms physical_signedShear
#print axioms fullLaw_probability
#print axioms fullLaw_integrable
#print axioms fullLaw_integral
#print axioms fullLaw_energy
#print axioms fullLaw_energy_bounds
#print axioms fullLaw_shear_lower
#print axioms exists_bounded_energy_large_shear
#print axioms no_affine_energy_bound
end
end UnifiedTheory.Audit.KFCausalClassicalPhysicalShearObstruction
