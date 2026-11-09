/- An interval Cauchy estimate for two actual full-generator approximate
solutions with a derived common velocity-energy budget. -/
import UnifiedTheory.Audit.KFCausalClockFloorApproximationComparison
import UnifiedTheory.Audit.KFCausalClockFloorFullApproximationStability
import UnifiedTheory.Audit.KFCausalForcedEnergyGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorApproximationCauchy
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorDissipation
open UnifiedTheory.Audit.KFCausalClockFloorFullApproximationStability
open UnifiedTheory.Audit.KFCausalClockFloorApproximationComparison
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "M₀" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "D" => referenceFormDerivative ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "P" => transportDerivative ε hε h hne hh m g k
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k
local notation "ω" => quasiRate ε hε h hne hh m g k
local notation "θ" => coordinateRate ε hε h hne hh m g k
local notation "ρ" => energyRate ε hε h hne hh m g k

theorem difference_energy_bound (a b c s κ M l r : ℝ) (ha : 0 < a)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hlr : l ≤ r)
    (hparams : ∀ t ∈ Icc l r, q a s t < b ∧ q a s t < c ∧ ρ a s t ≤ κ)
    (u v : ℝ → V) (huC : ContinuousOn u (Icc l r)) (hvC : ContinuousOn v (Icc l r))
    (hu : ∀ t ∈ Ioo l r, HasDerivAt u (A a b s t (u t)) t)
    (hv : ∀ t ∈ Ioo l r, HasDerivAt v (A a c s t (v t)) t)
    (hi : u l = v l)
    (huV : ∀ t ∈ Icc l r, energy (F a t) (S a s t (A a b s t (u t))) ≤ M)
    (hvV : ∀ t ∈ Icc l r, energy (F a t) (S a s t (A a c s t (v t))) ≤ M) :
    energy (F a r) (S a s r (u r-v r)) ≤ Real.exp (κ*(r-l))*((6+κ)*M*(1/b+1/c)*(r-l)) := by
  have hcont := coefficient_continuity ε hε h hne hh m g k a s ha
  apply KFCausalForcedEnergyGrowth.drop_initial_zero (F a) (S a s) (fun t => u t-v t)
    κ ((6+κ)*M*(1/b+1/c)) l r (sub_eq_zero.mpr hi)
  exact KFCausalForcedEnergyGrowth.velocity_growth (F a) D (S a s) (P a s) (θ a s) (ω a s)
    κ M (1/b+1/c) l r hκ hM
    (KFCausalWeightedCauchyPairing.reciprocal_parameters b c hb hc).1.le hlr hcont.1 hcont.2.1
    (fun t => KFCausalMassResolventStability.shift_symmetric M₀ (Q t)
      (mass_symmetric ε hε h hne hh m g k) (form_symmetric ε hε h hne hh m g k t) a)
    (referenceShift_derivative ε hε h hne hh m g k a)
    (fun t => transport_derivative ε hε h hne hh m g k a s t ha)
    (fun t _ => coordinate_rate_nonnegative ε hε h hne hh m g k a s t ha)
    (fun t _ => quasi_rate_nonnegative ε hε h hne hh m g k a s t ha)
    (fun t ht => (hparams t ht).2.2)
    (fun t _ x => KFCausalClockFloorLiftedEnergyStability.form_derivative_bound ε hε h hne hh m g k
      a t ha.le (S a s t x))
    (fun t _ x => coordinate_derivative_bound ε hε h hne hh m g k a s t ha x)
    (fun t _ x => shift_energy_nonnegative ε hε h hne hh m g k a t ha (S a s t x))
    (fun t => u t-v t) (fun t => A a b s t (u t)-A a c s t (v t)) (huC.sub hvC)
    (fun t ht => (hu t ht).sub (hv t ht))
    (fun t ht => transported_comparison_pairing ε hε h hne hh m g k a b c s t M ha hb hc
      (hparams t ht).1 (hparams t ht).2.1 hM (u t) (v t)
      ((metric_energy ε hε h hne hh m g k a s t (A a b s t (u t))).trans_le (huV t ht))
      ((metric_energy ε hε h hne hh m g k a s t (A a c s t (v t))).trans_le (hvV t ht)))

#print axioms difference_energy_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorApproximationCauchy
