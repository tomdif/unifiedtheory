/- Forward energy stability, uniform in the resolvent cutoff, along
any strong solution of the actual bounded lifted approximation. This
estimate does not assert existence or convergence of these trajectories. -/
import UnifiedTheory.Audit.KFCausalClockFloorLiftedRegularization
import UnifiedTheory.Audit.KFCausalDissipativeFormGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorLiftedEnergyStability
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedRegularization
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "D" => referenceFormDerivative ε hε h hne hh m g k
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "A" => regularization ε hε h hne hh m g k

theorem form_derivative_bound (a t : ℝ) (ha : 0 ≤ a) (x : V) :
    energy (D t) x ≤ 2*energy (F a t) x :=
  KFCausalDissipativeFormGrowth.shifted_form_derivative_bound J
    (staticMap ε hε h hne hh m g k) (growingMap ε hε h hne hh m g k) a t ha x

theorem regularized_energy_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (u : ℝ → V) (hu : ∀ t, HasDerivAt u (A b t (u t)) t) (s t : ℝ) (hst : s ≤ t) :
    energy (F a t) (u t) ≤ Real.exp (2*(t-s))*energy (F a s) (u s) :=
  KFCausalDissipativeFormGrowth.dissipative_growth (F a) D (A b)
    (fun t => KFCausalMassResolventStability.shift_symmetric M (Q t)
      (mass_symmetric ε hε h hne hh m g k) (form_symmetric ε hε h hne hh m g k t) a)
    (referenceShift_derivative ε hε h hne hh m g k a)
    (fun t x => form_derivative_bound ε hε h hne hh m g k a t ha.le x)
    (fun t x => regularization_nonpositive ε hε h hne hh m g k a b t ha hb x) u hu s t hst

theorem regularized_norm_square_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (u : ℝ → V) (hu : ∀ t, HasDerivAt u (A b t (u t)) t) (s t : ℝ) (hst : s ≤ t) :
    KFCausalShiftedForm.lowerConstant a t*‖u t‖^2 ≤
      Real.exp (2*(t-s))*‖F a s‖*‖u s‖^2 :=
  (shift_energy_coercive ε hε h hne hh m g k a t (u t)).trans
    ((regularized_energy_bound ε hε h hne hh m g k a b ha hb u hu s t hst).trans
      ((mul_le_mul_of_nonneg_left (KFCausalWeightedMassEnergy.energy_norm_upper (F a s) (u s))
        (Real.exp_pos _).le).trans_eq (mul_assoc _ _ _).symm))

#print axioms form_derivative_bound
#print axioms regularized_energy_bound
#print axioms regularized_norm_square_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorLiftedEnergyStability
