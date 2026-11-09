/- The weighted matter clock equations are consequences of the derived
full canonical field, using shifts in the actual clock phase coordinates. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterODE
import UnifiedTheory.Audit.KFCausalClassicalVacuumClockComponents

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterClock
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterSmooth
open UnifiedTheory.Audit.KFCausalClassicalMatterODE
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q p q_apply p_apply TimePhase)
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE (positionBasis momentumBasis)
open UnifiedTheory.Audit.KFCausalClassicalVacuumClockComponents (clockShift clockShift_clock shear_clockShift kineticMean_clockShift)

theorem fieldValue_clockShift (θ a b : ℝ) (z : Phase) :
    fieldValue (rotate θ (clockShift a b z)) = fieldValue (rotate θ z) := by
  simp [fieldValue_rotate,clockShift,positionBasis,momentumBasis,PiLp.basisFun_apply]

theorem potential_clockShift (m g κ θ a b : ℝ) (z : Phase) :
    potential m g κ (rotate θ (clockShift a b z)) = potential m g κ (rotate θ z) := by
  simp only [potential,fieldValue_clockShift]

theorem weightedMean_clockShift (m g κ C a b : ℝ) (z : Phase) :
    weightedMean m g κ C (clockShift a b z) = weightedMean m g κ C z := by
  simp only [weightedMean,potential_clockShift,shear_clockShift]

theorem hamiltonian_clockShift (ε m g κ t a b s r : ℝ) (z : Phase) :
    hamiltonian ε m g κ t (clockShift a b z) s r = hamiltonian ε m g κ t z s r := by
  simp only [hamiltonian, kineticMean_clockShift, weightedMean_clockShift]

theorem fullHamiltonian_clockShift (ε m g κ t a b : ℝ) (z : Phase) :
    fullHamiltonian ε m g κ (t,clockShift a b z) =
      hamiltonian ε m g κ t z (q (.inr 0) z+a) (p (.inr 0) z+b) := by
  simp only [fullHamiltonian, (clockShift_clock a b z).1, (clockShift_clock a b z).2,
    hamiltonian_clockShift]

theorem field_clock (ε m g κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    q (.inr 0) (field ε m g κ x).2 = clockRate ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) := by
  have hd : HasFDerivAt (fullHamiltonian ε m g κ) (fderiv ℝ (fullHamiltonian ε m g κ) x) x :=
    ((fullHamiltonian_contDiff ε m g κ hε 1).differentiable (by norm_num) x).hasFDerivAt
  have hl : HasDerivAt (fun u : ℝ => (x.1,clockShift 0 u x.2))
      (0,momentumBasis (.inr 0)) 0 := by
    convert (hasDerivAt_const (0:ℝ) x.1).prodMk
      ((hasDerivAt_const (0:ℝ) x.2).add ((hasDerivAt_id (0:ℝ)).smul_const (momentumBasis (.inr 0)))) using 1
    · funext u; simp [clockShift]
    · simp
  have hc := hd.comp_hasDerivAt_of_eq 0 hl (by simp [clockShift])
  have hp := (hamiltonian_momentum_derivative ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2)).comp_of_eq 0
    ((hasDerivAt_id (0:ℝ)).const_add (p (.inr 0) x.2)) (by simp)
  have hp' : HasDerivAt (fun u => fullHamiltonian ε m g κ (x.1,clockShift 0 u x.2))
      (clockRate ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2)) 0 := by
    simpa only [fullHamiltonian_clockShift, add_zero, Function.comp_def, id_eq, mul_one] using hp
  change fderiv ℝ (fullHamiltonian ε m g κ) x (0,momentumBasis (.inr 0)) = _
  exact hc.unique hp'

theorem field_clockMomentum (ε m g κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    p (.inr 0) (field ε m g κ x).2 = momentumRate ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) := by
  have hd : HasFDerivAt (fullHamiltonian ε m g κ) (fderiv ℝ (fullHamiltonian ε m g κ) x) x :=
    ((fullHamiltonian_contDiff ε m g κ hε 1).differentiable (by norm_num) x).hasFDerivAt
  have hl : HasDerivAt (fun u : ℝ => (x.1,clockShift u 0 x.2))
      (0,positionBasis (.inr 0)) 0 := by
    convert (hasDerivAt_const (0:ℝ) x.1).prodMk
      ((hasDerivAt_const (0:ℝ) x.2).add ((hasDerivAt_id (0:ℝ)).smul_const (positionBasis (.inr 0)))) using 1
    · funext u; simp [clockShift]
    · simp
  have hc := hd.comp_hasDerivAt_of_eq 0 hl (by simp [clockShift])
  have hp := (hamiltonian_clock_derivative ε m g κ x.1 hε x.2 (q (.inr 0) x.2) (p (.inr 0) x.2)).comp_of_eq 0
    ((hasDerivAt_id (0:ℝ)).const_add (q (.inr 0) x.2)) (by simp)
  have hp' : HasDerivAt (fun u => fullHamiltonian ε m g κ (x.1,clockShift u 0 x.2))
      (-momentumRate ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2)) 0 := by
    simpa only [fullHamiltonian_clockShift, add_zero, Function.comp_def, id_eq, mul_one] using hp
  change -fderiv ℝ (fullHamiltonian ε m g κ) x (0,positionBasis (.inr 0)) = _
  have h := hc.unique hp'
  linarith

#print axioms fieldValue_clockShift
#print axioms potential_clockShift
#print axioms weightedMean_clockShift
#print axioms hamiltonian_clockShift
#print axioms fullHamiltonian_clockShift
#print axioms field_clock
#print axioms field_clockMomentum

end
end UnifiedTheory.Audit.KFCausalClassicalMatterClock
