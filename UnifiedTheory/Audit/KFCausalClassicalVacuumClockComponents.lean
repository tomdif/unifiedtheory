/- Identification of the clock components of the full canonical vector field
with the previously calculated clock Hamilton equations. -/
import UnifiedTheory.Audit.KFCausalCanonicalPhaseODE
import UnifiedTheory.Audit.KFCausalClassicalAveragedVacuumDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumClockComponents
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE

def clockShift (a b : ℝ) (z : Phase) : Phase :=
  z+a • positionBasis (.inr 0)+b • momentumBasis (.inr 0)

theorem clockShift_clock (a b : ℝ) (z : Phase) :
    q (.inr 0) (clockShift a b z) = q (.inr 0) z+a ∧
    p (.inr 0) (clockShift a b z) = p (.inr 0) z+b := by
  simp [clockShift, q_apply, p_apply, positionBasis, momentumBasis, PiLp.basisFun_apply]

theorem shear_clockShift (θ a b : ℝ) (z : Phase) :
    shear (rotate θ (clockShift a b z)) = shear (rotate θ z) := by
  simp [shear_rotate, diagonalPairing, crossPairing, clockShift,
    positionBasis, momentumBasis, PiLp.basisFun_apply]

theorem kineticMean_clockShift (t a b : ℝ) (z : Phase) :
    kineticMean t (clockShift a b z) = kineticMean t z := by
  simp [kineticMean_eq, clockShift, positionBasis, momentumBasis, PiLp.basisFun_apply]

theorem exponentialMean_clockShift (C a b : ℝ) (z : Phase) :
    exponentialMean C (clockShift a b z) = exponentialMean C z := by
  simp only [exponentialMean, shear_clockShift]

theorem hamiltonian_clockShift (ε κ t a b s r : ℝ) (z : Phase) :
    hamiltonian ε κ t (clockShift a b z) s r = hamiltonian ε κ t z s r := by
  simp only [hamiltonian, kineticMean_clockShift, exponentialMean_clockShift]

theorem fullHamiltonian_clockShift (ε κ t a b : ℝ) (z : Phase) :
    fullHamiltonian ε κ (t,clockShift a b z) =
      hamiltonian ε κ t z (q (.inr 0) z+a) (p (.inr 0) z+b) := by
  simp only [fullHamiltonian, (clockShift_clock a b z).1, (clockShift_clock a b z).2,
    hamiltonian_clockShift]

theorem field_clock (ε κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    q (.inr 0) (field ε κ x).2 = clockRate ε κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) := by
  have hd : HasFDerivAt (fullHamiltonian ε κ) (fderiv ℝ (fullHamiltonian ε κ) x) x :=
    ((fullHamiltonian_contDiff ε κ hε 1).differentiable (by norm_num) x).hasFDerivAt
  have hl : HasDerivAt (fun u : ℝ => (x.1,clockShift 0 u x.2))
      (0,momentumBasis (.inr 0)) 0 := by
    convert (hasDerivAt_const (0:ℝ) x.1).prodMk
      ((hasDerivAt_const (0:ℝ) x.2).add ((hasDerivAt_id (0:ℝ)).smul_const (momentumBasis (.inr 0)))) using 1
    · funext u; simp [clockShift]
    · simp
  have hc := hd.comp_hasDerivAt_of_eq 0 hl (by simp [clockShift])
  have hp := (hamiltonian_momentum_derivative ε κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2)).comp_of_eq 0
    ((hasDerivAt_id (0:ℝ)).const_add (p (.inr 0) x.2)) (by simp)
  have hp' : HasDerivAt (fun u => fullHamiltonian ε κ (x.1,clockShift 0 u x.2))
      (clockRate ε κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2)) 0 := by
    simpa only [fullHamiltonian_clockShift, add_zero, Function.comp_def, id_eq, mul_one] using hp
  change fderiv ℝ (fullHamiltonian ε κ) x (0,momentumBasis (.inr 0)) = _
  exact hc.unique hp'

theorem field_clockMomentum (ε κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    p (.inr 0) (field ε κ x).2 = momentumRate ε κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) := by
  have hd : HasFDerivAt (fullHamiltonian ε κ) (fderiv ℝ (fullHamiltonian ε κ) x) x :=
    ((fullHamiltonian_contDiff ε κ hε 1).differentiable (by norm_num) x).hasFDerivAt
  have hl : HasDerivAt (fun u : ℝ => (x.1,clockShift u 0 x.2))
      (0,positionBasis (.inr 0)) 0 := by
    convert (hasDerivAt_const (0:ℝ) x.1).prodMk
      ((hasDerivAt_const (0:ℝ) x.2).add ((hasDerivAt_id (0:ℝ)).smul_const (positionBasis (.inr 0)))) using 1
    · funext u; simp [clockShift]
    · simp
  have hc := hd.comp_hasDerivAt_of_eq 0 hl (by simp [clockShift])
  have hp := (hamiltonian_clock_derivative ε κ x.1 hε x.2 (q (.inr 0) x.2) (p (.inr 0) x.2)).comp_of_eq 0
    ((hasDerivAt_id (0:ℝ)).const_add (q (.inr 0) x.2)) (by simp)
  have hp' : HasDerivAt (fun u => fullHamiltonian ε κ (x.1,clockShift u 0 x.2))
      (-momentumRate ε κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2)) 0 := by
    simpa only [fullHamiltonian_clockShift, add_zero, Function.comp_def, id_eq, mul_one] using hp
  change -fderiv ℝ (fullHamiltonian ε κ) x (0,positionBasis (.inr 0)) = _
  have h := hc.unique hp'
  linarith

#print axioms clockShift_clock
#print axioms shear_clockShift
#print axioms kineticMean_clockShift
#print axioms exponentialMean_clockShift
#print axioms hamiltonian_clockShift
#print axioms fullHamiltonian_clockShift
#print axioms field_clock
#print axioms field_clockMomentum

end
end UnifiedTheory.Audit.KFCausalClassicalVacuumClockComponents
