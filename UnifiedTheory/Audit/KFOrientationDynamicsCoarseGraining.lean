/-
  Audit/KFOrientationDynamicsCoarseGraining.lean

  HEISENBERG DYNAMICS VERSUS ORIENTATION COARSE-GRAINING

  Exact fixed-profile Heisenberg evolution preserves the spin-one trace Gram
  pairing.  The normalized diamond-to-chain blocking does something different:
  it generates the missing long-range skew edge and changes the quadratic
  orientation strength from 4 to 6.

  Consequently, this blocking step cannot be represented as any member of the
  exact fixed-Hamiltonian Rodrigues flow acting on the native coarse operator.
  This is a finite separation between reversible dynamics and coarse graining,
  not a continuum renormalization theorem.
-/

import UnifiedTheory.Audit.KFOrientationSpinOneEvolution
import UnifiedTheory.Audit.KFMultirankCoarseGraining

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationDynamicsCoarseGraining

noncomputable section

open scoped BigOperators Polynomial ComplexConjugate
open Matrix
open UnifiedTheory.Audit.KFMultirankCoarseGraining
open UnifiedTheory.Audit.KFOrientationQuantumConsequences
open UnifiedTheory.Audit.KFOrientationSpinOne
open UnifiedTheory.Audit.KFOrientationSpinOneRelational
open UnifiedTheory.Audit.KFOrientationSpinOneEvolution

/-! ## 1. Hermitian representatives of the coarse and blocked channels -/

def hermitianizedOrientation
    (M : Matrix (Fin 3) (Fin 3) ℚ) : SpinOneMatrix :=
  Complex.I • M.map (Rat.castHom ℂ)

def coarseNativeOrientationHamiltonian : SpinOneMatrix :=
  hermitianizedOrientation chainThreeOrientationRankTwo

def normalizedBlockedOrientationHamiltonian : SpinOneMatrix :=
  hermitianizedOrientation
    ((1 / 2 : ℚ) •
      pushForwardMatrix diamondRankTwoBlock diamondOrientationRankTwo)

theorem coarseNativeOrientationHamiltonian_eq :
    coarseNativeOrientationHamiltonian = skewHamiltonian 1 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coarseNativeOrientationHamiltonian, hermitianizedOrientation,
      chainThreeOrientationRankTwo, skewHamiltonian, Fin.ext_iff]

theorem normalizedBlockedOrientationHamiltonian_eq :
    normalizedBlockedOrientationHamiltonian = skewHamiltonian 1 1 1 := by
  unfold normalizedBlockedOrientationHamiltonian
  rw [diamond_orientation_normalized_pushforward]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hermitianizedOrientation, chainThreeOrientationRankTwo,
      generatedLongRangeOrientation, skewHamiltonian, Fin.ext_iff]

theorem coarseNativeOrientationHamiltonian_spinOne :
    coarseNativeOrientationHamiltonian =
      spinOneFieldHamiltonian spinOneSqrtTwo 0 0 := by
  rw [coarseNativeOrientationHamiltonian_eq]
  simpa [spinOneFieldHamiltonian] using
    skewHamiltonian_spinOne_decomposition 1 0 0

theorem normalizedBlockedOrientationHamiltonian_spinOne :
    normalizedBlockedOrientationHamiltonian =
      spinOneFieldHamiltonian spinOneSqrtTwo 1 0 := by
  rw [normalizedBlockedOrientationHamiltonian_eq]
  simpa [spinOneFieldHamiltonian] using
    skewHamiltonian_spinOne_decomposition 1 1 0

/-! ## 2. The exact strength jump under blocking -/

def orientationTraceStrength (H : SpinOneMatrix) : ℂ :=
  Matrix.trace (H * H)

theorem coarseNative_orientationTraceStrength :
    orientationTraceStrength coarseNativeOrientationHamiltonian = 4 := by
  rw [coarseNativeOrientationHamiltonian_spinOne]
  unfold orientationTraceStrength
  rw [spinOneField_trace_product]
  unfold fieldDot
  push_cast
  have hsqrt :
      (spinOneSqrtTwo : ℂ) * spinOneSqrtTwo = 2 := by
    rw [← pow_two, spinOneSqrtTwo_sq_complex]
  rw [hsqrt]
  norm_num

theorem normalizedBlocked_orientationTraceStrength :
    orientationTraceStrength normalizedBlockedOrientationHamiltonian = 6 := by
  rw [normalizedBlockedOrientationHamiltonian_spinOne]
  unfold orientationTraceStrength
  rw [spinOneField_trace_product]
  unfold fieldDot
  push_cast
  have hsqrt :
      (spinOneSqrtTwo : ℂ) * spinOneSqrtTwo = 2 := by
    rw [← pow_two, spinOneSqrtTwo_sq_complex]
  rw [hsqrt]
  norm_num

theorem blocking_changes_orientationTraceStrength :
    orientationTraceStrength normalizedBlockedOrientationHamiltonian ≠
      orientationTraceStrength coarseNativeOrientationHamiltonian := by
  rw [normalizedBlocked_orientationTraceStrength,
    coarseNative_orientationTraceStrength]
  norm_num

/-! ## 3. Blocking is not fixed-profile Heisenberg evolution -/

theorem normalized_blocking_not_heisenberg_evolution
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (t : ℝ) :
    orientationHeisenbergEvolution p q r t
        coarseNativeOrientationHamiltonian ≠
      normalizedBlockedOrientationHamiltonian := by
  intro heq
  have hpreserve := orientationHeisenbergEvolution_trace_product
    p q r hp hq hr t spinOneSqrtTwo 0 0 spinOneSqrtTwo 0 0
  rw [← coarseNativeOrientationHamiltonian_spinOne] at hpreserve
  rw [heq] at hpreserve
  change orientationTraceStrength normalizedBlockedOrientationHamiltonian =
      orientationTraceStrength coarseNativeOrientationHamiltonian at hpreserve
  exact blocking_changes_orientationTraceStrength hpreserve

/-- The exact synthesis: reversible fixed-profile evolution exists and
preserves trace geometry, while the certified blocking step lies outside every
such orbit because it generates an independent orientation component. -/
theorem reversible_dynamics_and_blocking_separate
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (t : ℝ) :
    orientationHeisenbergEvolution p q r (-t)
        (orientationHeisenbergEvolution p q r t
          coarseNativeOrientationHamiltonian) =
      coarseNativeOrientationHamiltonian
    ∧ orientationTraceStrength normalizedBlockedOrientationHamiltonian = 6
    ∧ orientationTraceStrength coarseNativeOrientationHamiltonian = 4
    ∧ orientationHeisenbergEvolution p q r t
        coarseNativeOrientationHamiltonian ≠
      normalizedBlockedOrientationHamiltonian := by
  have hinverse :
      orientationHeisenbergEvolution p q r (-t)
          (orientationHeisenbergEvolution p q r t
            coarseNativeOrientationHamiltonian) =
        coarseNativeOrientationHamiltonian := by
    rw [coarseNativeOrientationHamiltonian_spinOne]
    exact orientationHeisenbergEvolution_inverse p q r hp hq hr
      t spinOneSqrtTwo 0 0
  exact ⟨hinverse,
    normalizedBlocked_orientationTraceStrength,
    coarseNative_orientationTraceStrength,
    normalized_blocking_not_heisenberg_evolution p q r hp hq hr t⟩

#print axioms normalizedBlockedOrientationHamiltonian_eq
#print axioms blocking_changes_orientationTraceStrength
#print axioms normalized_blocking_not_heisenberg_evolution
#print axioms reversible_dynamics_and_blocking_separate

end

end UnifiedTheory.Audit.KFOrientationDynamicsCoarseGraining
