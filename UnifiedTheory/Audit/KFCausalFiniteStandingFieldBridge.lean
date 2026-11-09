/- Identify the finite model's actual gradient and matter-position fields
with standing-wave positions. Their exact charge derivatives include the
neutral matter contribution and retain arbitrary radial ladder weights. -/
import UnifiedTheory.Audit.KFCausalFiniteStandingCharge
import UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFiniteStandingFieldBridge
noncomputable section
open Matrix
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalGradedSpinSource
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity
open UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian
open UnifiedTheory.Audit.KFCausalFiniteStandingCharge

def neutralField (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  (Real.sqrt (hbar/2):ℂ) • (ladder r 5+(ladder r 5)ᴴ)

theorem fieldQx_standing (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    fieldQx R r hbar = sinePosition (Real.sqrt (hbar/2)) (ladder r 1) (ladder r 2) := by
  ext i j
  simp [fieldQx, gradientPair, skew, sinePosition, sineMode, Matrix.conjTranspose_apply]
  ring

theorem fieldPhix_standing (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    fieldPhix R r hbar = sinePosition (Real.sqrt (hbar/2)) (ladder r 3) (ladder r 4) := by
  ext i j
  simp [fieldPhix, gradientPair, skew, sinePosition, sineMode, Matrix.conjTranspose_apply]
  ring

theorem fieldPhi_standing (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    fieldPhi R r hbar = neutralField R r hbar+
      cosinePosition (Real.sqrt (hbar/2)) (ladder r 3) (ladder r 4) := by
  ext i j
  simp [fieldPhi, neutralField, cosinePosition, cosineMode, Matrix.conjTranspose_apply]
  ring

theorem neutralField_derivative (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    spatialDeriv charge (neutralField R r hbar) = 0 := by
  have hZ : HasCharge (charge (R := R)) 0 (ladder r 5) := by
    simpa [flavorCharge] using ladder_charge (R := R) r 5
  rw [neutralField, spatialDeriv_smul, spatialDeriv_add, spatialDeriv_adjoint,
    spatialDeriv_charged charge 0 (ladder r 5) hZ]
  simp

theorem fieldPhi_derivative (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    spatialDeriv charge (fieldPhi R r hbar) = fieldPhix R r hbar := by
  rw [fieldPhi_standing, spatialDeriv_add, neutralField_derivative,
    matter_cosine_derivative, zero_add, fieldPhix_standing]

theorem fieldPhix_derivative (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    spatialDeriv charge (fieldPhix R r hbar) = -(fieldPhi R r hbar-neutralField R r hbar) := by
  rw [fieldPhix_standing, matter_sine_derivative, fieldPhi_standing]
  simp

#print axioms fieldQx_standing
#print axioms fieldPhix_standing
#print axioms fieldPhi_standing
#print axioms neutralField_derivative
#print axioms fieldPhi_derivative
#print axioms fieldPhix_derivative

end
end UnifiedTheory.Audit.KFCausalFiniteStandingFieldBridge
