/- The classical matter candidate keeps the actual field factors multiplying
 the ordered exponential. The eight squared symbols use the repository's
 energy polynomial. A controlled quantum symbol limit is not asserted. -/
import UnifiedTheory.Audit.KFCausalClassicalWeightedLaplace
import UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
import UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale backward)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum (kineticMean kinetic_continuous)
open UnifiedTheory.Audit.KFCausalClassicalWeightedLaplace

def fieldValue (z : Phase) : ℝ := KFCausalMatterOrderedDomain.pointField (physicalTail z.1)

theorem fieldValue_eq (z : Phase) : fieldValue z = 2*scale*z.1 (.inr 2)+z.1 (.inr 3) := by
  simp [fieldValue,KFCausalMatterOrderedDomain.pointField_apply,physicalTail,backward]
  ring

theorem fieldValue_rotate (θ : ℝ) (z : Phase) :
    fieldValue (rotate θ z) = 2*scale*(Real.cos θ*z.1 (.inr 2)+Real.sin θ*z.2 (.inl 1))+z.1 (.inr 3) := by
  simp [fieldValue_eq,rotate]

def potential (m g κ : ℝ) (z : Phase) : ℝ := κ+(m/2)*(fieldValue z)^2+(g/4)*(fieldValue z)^4

def squaredSymbols (C r : ℝ) (z : Phase) : Fin 8 → ℝ :=
  ![C,(∑ i,modelDirections 0 i*physicalTail z.2 i)^2/C,
    (∑ i,modelDirections 1 i*physicalTail z.2 i)^2/C,
    (∑ i,modelDirections 2 i*physicalTail z.2 i)^2/C,
    (∑ i,modelDirections 3 i*physicalTail z.2 i)^2/C,
    (fieldValue z)^2*Real.exp ((r+shear z)/C)/C,
    (fieldValue z)^4*Real.exp ((r+shear z)/C)/C,Real.exp ((r+shear z)/C)/C]

def rawHamiltonian (ε m g κ t s r : ℝ) (z : Phase) : ℝ :=
  clock ε s/2+(kinetic t z+potential m g κ z*Real.exp (2*t+(r+shear z)/clock ε s))/clock ε s

theorem rawHamiltonian_eq_energyPolynomial (ε m g κ t s r : ℝ) (z : Phase) :
    rawHamiltonian ε m g κ t s r z =
      KFCausalClockFloorTrialUniformEnergy.energyPolynomial m g κ t (squaredSymbols (clock ε s) r z) := by
  simp [rawHamiltonian,squaredSymbols,KFCausalClockFloorTrialUniformEnergy.energyPolynomial,
    potential,kinetic,Real.exp_add]
  ring

theorem potential_continuous (m g κ : ℝ) (z : Phase) :
    Continuous (fun θ => potential m g κ (rotate θ z)) := by
  simp_rw [potential,fieldValue_rotate]
  fun_prop

theorem potential_ge_vacuum (m g κ : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (z : Phase) :
    κ ≤ potential m g κ z := by
  unfold potential
  have h2 : 0 ≤ m/2*(fieldValue z)^2 := by positivity
  have h4 : 0 ≤ g/4*(fieldValue z)^4 := by positivity
  linarith

def weightedMean (m g κ C : ℝ) (z : Phase) : ℝ :=
  mean (fun θ => potential m g κ (rotate θ z)*Real.exp (shear (rotate θ z)/C))

def weightedTilt (m g κ C : ℝ) (z : Phase) : ℝ :=
  mean (fun θ => potential m g κ (rotate θ z)*(shear (rotate θ z)/C)*Real.exp (shear (rotate θ z)/C))

theorem weightedMean_vacuum (κ C : ℝ) (z : Phase) :
    weightedMean 0 0 κ C z = κ*exponentialMean C z := by
  simp only [weightedMean,potential,zero_div,zero_mul,add_zero]
  simp_rw [mul_comm κ]
  rw [mean_mul_const,exponentialMean,mul_comm]

theorem weightedMean_lower (m g κ C : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) (z : Phase) :
    κ ≤ weightedMean m g κ C z := by
  have h := mean_mono (fun θ => κ*Real.exp (shear (rotate θ z)/C))
    (fun θ => potential m g κ (rotate θ z)*Real.exp (shear (rotate θ z)/C))
    (by have hs := shear_continuous z; fun_prop)
    (by have hp := potential_continuous m g κ z; have hs := shear_continuous z; fun_prop)
    (fun θ => mul_le_mul_of_nonneg_right (potential_ge_vacuum m g κ hm hg _) (Real.exp_pos _).le)
  have hv : mean (fun θ => κ*Real.exp (shear (rotate θ z)/C)) = κ*exponentialMean C z := by
    simpa only [weightedMean,potential,zero_div,zero_mul,add_zero] using weightedMean_vacuum κ C z
  rw [hv] at h
  exact (le_mul_of_one_le_right hκ (exponentialMean_ge_one C z)).trans h

theorem weightedMean_derivative (m g κ C : ℝ) (hC : C ≠ 0) (z : Phase) :
    HasDerivAt (fun u => weightedMean m g κ u z) (-weightedTilt m g κ C z/C) C := by
  have h := (mean_weighted_exp_derivative (fun θ => potential m g κ (rotate θ z))
    (fun θ => shear (rotate θ z)) (potential_continuous m g κ z) (shear_continuous z) C⁻¹).comp C
    (hasDerivAt_inv hC)
  have he (u : ℝ) : mean (fun θ => potential m g κ (rotate θ z)*Real.exp (u⁻¹*shear (rotate θ z))) =
      weightedMean m g κ u z := by
    unfold weightedMean
    congr 1
    funext θ
    rw [div_eq_mul_inv,mul_comm u⁻¹]
  simp only [Function.comp_def,he] at h
  convert h using 1
  have ht : weightedTilt m g κ C z =
      mean (fun θ => potential m g κ (rotate θ z)*shear (rotate θ z)*Real.exp (C⁻¹*shear (rotate θ z)))*C⁻¹ := by
    rw [← mean_mul_const]
    unfold weightedTilt
    congr 1
    funext θ
    rw [mul_comm C⁻¹ (shear (rotate θ z))]
    ring
  rw [ht]
  field_simp

#print axioms fieldValue_eq
#print axioms fieldValue_rotate
#print axioms rawHamiltonian_eq_energyPolynomial
#print axioms potential_continuous
#print axioms potential_ge_vacuum
#print axioms weightedMean_vacuum
#print axioms weightedMean_lower
#print axioms weightedMean_derivative

end
end UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
