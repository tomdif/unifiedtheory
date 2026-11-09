/- The actual homogeneous trajectories inhabit the general weak-solution
class. Uniqueness now compares them with every solution in that class,
including sums and complex scalar multiples. -/
import UnifiedTheory.Audit.KFCausalWeakFormSolution
import UnifiedTheory.Audit.KFCausalRegularizedFormFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedWeakSolution
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
open UnifiedTheory.Audit.KFCausalRegularizedFormRegularity
open UnifiedTheory.Audit.KFCausalRegularizedFormWindowBound
open UnifiedTheory.Audit.KFCausalRegularizedWeakTrajectory
open UnifiedTheory.Audit.KFCausalRegularizedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalRegularizedMassEnergy
open UnifiedTheory.Audit.KFCausalMassEnergyIdentities
open UnifiedTheory.Audit.KFCausalShiftedForm
open UnifiedTheory.Audit.KFCausalWeakFormSolution
open UnifiedTheory.Audit.KFCausalRegularizedFormFlow

def formGenerator (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    FormSpace ε hε hbar coupling 0 →L[ℂ] FormSpace ε hε hbar coupling 0 :=
  (-Complex.I*((1/hbar:ℝ):ℂ)) • referenceFormOperator ε hε hbar coupling t

theorem formGenerator_diagonal_zero (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (x : FormSpace ε hε hbar coupling 0) :
    (inner ℂ (formGenerator ε hε hbar coupling t x) x).re = 0 := by
  have hs := formOperator_inner_symm (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (clockMap ε hε hbar coupling) (momentumMap ε hε hbar coupling) t
  have hh := schrodinger_diagonal_zero (E := FormSpace ε hε hbar coupling 0)
    (referenceFormOperator ε hε hbar coupling t) hs hbar x
  exact hh

def weakSolution (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w) :
    Solution (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
      (embedding ε hε hbar coupling 0) (formGenerator ε hε hbar coupling) where
  state := V.formState
  radius T := windowRadius ε hε hbar coupling s T w
  slopeBound T := massLipschitzBound ε hε hbar coupling s T w
  slopeBound_nonneg T := massLipschitzBound_nonneg ε hε hbar coupling s T w
  state_bound := formState_window_bound ε hε hbar coupling s w V
  slope_bound := massSlope_window_bound ε hε hbar coupling s w V
  slope_weak_continuous := massSlope_weakly_continuous ε hε hbar coupling s w V
  mass_lipschitz := massState_window_lipschitz ε hε hbar coupling s w V
  equation := mass_pairing_derivative ε hε hbar coupling s w V

theorem weakSolution_eq_flow (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0)
    (U : Solution (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
      (embedding ε hε hbar coupling 0) (formGenerator ε hε hbar coupling))
    (hi : U.state s = w) : U.state = (fun t => formFlow ε hε hbar coupling s t w) := by
  have hi' : U.state s =
      (weakSolution ε hε hbar coupling s w (weakTrajectory ε hε hbar coupling s w)).state s := by
    exact hi.trans (weak_trajectory_initial ε hε hbar coupling s w _).symm
  have hh := unique (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (J := embedding ε hε hbar coupling 0) (A := formGenerator ε hε hbar coupling)
    (embedding_injective ε hε hbar coupling 0) (formGenerator_diagonal_zero ε hε hbar coupling)
    U (weakSolution ε hε hbar coupling s w (weakTrajectory ε hε hbar coupling s w))
    massScale massScale_pos massScale_tendsto s hi'
  exact hh

#print axioms formGenerator_diagonal_zero
#print axioms weakSolution
#print axioms weakSolution_eq_flow

end
end UnifiedTheory.Audit.KFCausalRegularizedWeakSolution
