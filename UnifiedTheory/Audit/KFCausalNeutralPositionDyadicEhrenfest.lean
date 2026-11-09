/- Exact dynamics for the finite dyadic observable on the existing
unitary propagator. Its response bound retains the scale cancellation
and uses the already proved physical energy of the evolving state. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionDyadicFullResponse
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialEhrenfest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionDyadicEhrenfest
noncomputable section
open UnifiedTheory.Audit.KFCausalFiniteMultiplierAverage
open UnifiedTheory.Audit.KFCausalDyadicHeatCancellation (width width_pos)
open UnifiedTheory.Audit.KFCausalMixedDyadicStripResponse (responseConstant)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialFullResponse (response kineticConstant)
open UnifiedTheory.Audit.KFCausalNeutralPositionDyadicFullResponse (completed_form_mean_diagonal)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy timeEnergy_actual)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow_physical_norm)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialReferenceResponse (rate_response)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient coefficient_norm)

variable (ε : ℝ) (hε : 0 < ε) (h δ v : ℝ) (N : ℕ) (hδ : 0 < δ)
  (hh : |h| ≤ 2*Real.pi*ε/3) (hne : h ≠ 0) (m g k : ℝ)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "T" => formTransfer ε hε h hne hh m g k
local notation "A" => energyOutput ε hε h hne hh m g k
local notation "F" => formFlow ε hε h hne hh m g k

def characteristic (s t : ℝ) (w : V₀) : ℂ := mean N (fun j =>
  KFCausalNeutralPositionRadialEhrenfest.characteristic ε hε h (width δ j) v (width_pos δ hδ j) hh hne m g k s t w)

def exactRate (s t : ℝ) (w : V₀) : ℂ := mean N (fun j =>
  KFCausalNeutralPositionRadialEhrenfest.exactRate ε hε h (width δ j) v (width_pos δ hδ j) hh hne m g k s t w)

theorem expectation_derivative (s t : ℝ) (w : V₀) :
    HasDerivAt (fun z => characteristic ε hε h δ v N hδ hh hne m g k s z w)
      (exactRate ε hε h δ v N hδ hh hne m g k s t w) t := by
  simpa only [characteristic,exactRate,mean,smul_eq_mul,Finset.sum_apply] using
    (HasDerivAt.sum (fun j (_ : j ∈ Finset.range N) =>
      KFCausalNeutralPositionRadialEhrenfest.expectation_derivative ε hε h (width δ j) v
        (width_pos δ hδ j) hh hne m g k s t w)).const_mul (N:ℂ)⁻¹

theorem exactRate_continuous (s : ℝ) (w : V₀) :
    Continuous (fun t => exactRate ε hε h δ v N hδ hh hne m g k s t w) := by
  unfold exactRate mean
  apply Continuous.const_smul
  exact continuous_finset_sum _ (fun j _ => KFCausalNeutralPositionRadialEhrenfest.exactRate_continuous
    ε hε h (width δ j) v (width_pos δ hδ j) hh hne m g k s w)

theorem expectation_integral (s a b : ℝ) (w : V₀) :
    (∫ t in a..b, exactRate ε hε h δ v N hδ hh hne m g k s t w) =
      characteristic ε hε h δ v N hδ hh hne m g k s b w-
        characteristic ε hε h δ v N hδ hh hne m g k s a w :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => expectation_derivative ε hε h δ v N hδ hh hne m g k s t w)
    ((exactRate_continuous ε hε h δ v N hδ hh hne m g k s w).intervalIntegrable _ _)

theorem exactRate_response (s t : ℝ) (w : V₀) :
    exactRate ε hε h δ v N hδ hh hne m g k s t w =
      coefficient h*mean N (fun j => response ε hε h (width δ j) v (width_pos δ hδ j) hh hne m g k t
        (T 0 t (F s t w)) (T 0 t (F s t w))) := by
  have hj (j : ℕ) :
      KFCausalNeutralPositionRadialEhrenfest.exactRate ε hε h (width δ j) v
        (width_pos δ hδ j) hh hne m g k s t w =
      coefficient h*response ε hε h (width δ j) v (width_pos δ hδ j) hh hne m g k t
        (T 0 t (F s t w)) (T 0 t (F s t w)) :=
    rate_response ε hε h (width δ j) v (width_pos δ hδ j) hh hne m g k t (F s t w)
  exact (congrArg (mean N) (funext hj)).trans (mean_mul_left N (coefficient h) _)

theorem exactRate_energy_bound (hN : 0 < N) (s t : ℝ) (w : V₀) :
    ‖exactRate ε hε h δ v N hδ hh hne m g k s t w‖ ≤
      responseConstant ε δ v N*timeEnergy ε hε h hne hh m g k t (F s t w)+
        2*kineticConstant ε (width δ N) v*‖J w‖*
          Real.sqrt (timeEnergy ε hε h hne hh m g k t (F s t w)) := by
  let u := F s t w
  have he : ‖A t (T 0 t u)‖ = Real.sqrt (timeEnergy ε hε h hne hh m g k t u) :=
    (Real.sqrt_sq (norm_nonneg (A t (T 0 t u)))).symm.trans
      (congrArg Real.sqrt (timeEnergy_actual ε hε h hne hh m g k t u))
  have hb := completed_form_mean_diagonal ε hε h δ v N hδ hh hne m g k t hN (T 0 t u)
  have hn : ‖embedding ε hε h hne hh m g k t (T 0 t u)‖ = ‖J w‖ :=
    (congrArg norm (transfer_embedding ε hε h hne hh m g k 0 t u)).trans
      (formFlow_physical_norm ε hε h hne hh m g k s t w)
  have hc (z : ℂ) : ‖coefficient h*z‖ = ‖z‖/|h| := by
    rw [norm_mul,coefficient_norm]
    ring
  have hr := (congrArg norm (exactRate_response ε hε h δ v N hδ hh hne m g k s t w)).trans (hc _)
  calc
    _ = ‖mean N (fun j => response ε hε h (width δ j) v (width_pos δ hδ j) hh hne m g k t
        (T 0 t u) (T 0 t u))‖/|h| := hr
    _ ≤ responseConstant ε δ v N*‖A t (T 0 t u)‖^2+
        2*kineticConstant ε (width δ N) v*‖embedding ε hε h hne hh m g k t (T 0 t u)‖*
          ‖A t (T 0 t u)‖ := hb
    _ = responseConstant ε δ v N*timeEnergy ε hε h hne hh m g k t u+
        2*kineticConstant ε (width δ N) v*‖J w‖*‖A t (T 0 t u)‖ :=
      congrArg₂ (fun a b : ℝ => responseConstant ε δ v N*a+
        2*kineticConstant ε (width δ N) v*b*‖A t (T 0 t u)‖)
        (timeEnergy_actual ε hε h hne hh m g k t u) hn
    _ = _ := congrArg (fun a : ℝ => responseConstant ε δ v N*timeEnergy ε hε h hne hh m g k t u+
      2*kineticConstant ε (width δ N) v*‖J w‖*a) he

#print axioms expectation_derivative
#print axioms exactRate_continuous
#print axioms expectation_integral
#print axioms exactRate_response
#print axioms exactRate_energy_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionDyadicEhrenfest
