/- The actual averaged trajectories inhabit the general weak-solution
class. Uniqueness now compares them with every solution in that class,
including sums and complex scalar multiples. -/
import UnifiedTheory.Audit.KFCausalWeakFormSolution
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakSolution
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormWindowBound
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedMassEnergy
open UnifiedTheory.Audit.KFCausalMassEnergyIdentities
open UnifiedTheory.Audit.KFCausalShiftedForm
open UnifiedTheory.Audit.KFCausalWeakFormSolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow

def formGenerator (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ) :
    FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0 →L[ℂ] FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0 :=
  (-Complex.I*((1/hbar:ℝ):ℂ)) • referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t

theorem formGenerator_diagonal_zero (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
    (x : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    (inner ℂ (formGenerator ε hε hbar hh hbound mass2 quartic vacuum t x) x).re = 0 := by
  have hs := formOperator_inner_symm (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := KFCausalAveragedOutputRescaling.EnergyOutputSpace)
    (staticMap ε hε hbar hh hbound mass2 quartic vacuum) (growingMap ε hε hbar hh hbound mass2 quartic vacuum) t
  have hpair := schrodinger_diagonal_zero (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0)
    (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t) hs hbar x
  exact hpair

def weakSolution (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w) :
    Solution (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0) (formGenerator ε hε hbar hh hbound mass2 quartic vacuum) where
  state := V.formState
  radius T := windowRadius ε hε hbar hh hbound mass2 quartic vacuum s T w
  slopeBound T := massLipschitzBound ε hε hbar hh hbound mass2 quartic vacuum s T w
  slopeBound_nonneg T := massLipschitzBound_nonneg ε hε hbar hh hbound mass2 quartic vacuum s T w
  state_bound := formState_window_bound ε hε hbar hh hbound mass2 quartic vacuum s w V
  slope_bound := massSlope_window_bound ε hε hbar hh hbound mass2 quartic vacuum s w V
  slope_weak_continuous := massSlope_weakly_continuous ε hε hbar hh hbound mass2 quartic vacuum s w V
  mass_lipschitz := massState_window_lipschitz ε hε hbar hh hbound mass2 quartic vacuum s w V
  equation := mass_pairing_derivative ε hε hbar hh hbound mass2 quartic vacuum s w V

theorem weakSolution_eq_flow (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0)
    (U : Solution (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0) (formGenerator ε hε hbar hh hbound mass2 quartic vacuum))
    (hi : U.state s = w) : U.state = (fun t => formFlow ε hε hbar hh hbound mass2 quartic vacuum s t w) := by
  have hi' : U.state s =
      (weakSolution ε hε hbar hh hbound mass2 quartic vacuum s w (weakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)).state s := by
    exact hi.trans (weak_trajectory_initial ε hε hbar hh hbound mass2 quartic vacuum s w _).symm
  have hpair := unique (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
    (J := embedding ε hε hbar hh hbound mass2 quartic vacuum 0) (A := formGenerator ε hε hbar hh hbound mass2 quartic vacuum)
    (embedding_injective ε hε hbar hh hbound mass2 quartic vacuum 0) (formGenerator_diagonal_zero ε hε hbar hh hbound mass2 quartic vacuum)
    U (weakSolution ε hε hbar hh hbound mass2 quartic vacuum s w (weakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w))
    massScale massScale_pos massScale_tendsto s hi'
  exact hpair

#print axioms formGenerator_diagonal_zero
#print axioms weakSolution
#print axioms weakSolution_eq_flow

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakSolution
