/- Uniform forward energy stability for the actual full-generator
approximations on compact time intervals. Existence of their trajectories
is supplied separately, rather than included in this estimate's hypotheses. -/
import UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorDissipation
import UnifiedTheory.Audit.KFCausalClockFloorLiftedEnergyStability
import UnifiedTheory.Audit.KFCausalTransportedQuasiGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorFullApproximationStability
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFixedResolventWindow
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorDissipation
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "D" => referenceFormDerivative ε hε h hne hh m g k
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "P" => referenceInverse ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "S'" => transportDerivative ε hε h hne hh m g k
local notation "C" => connection ε hε h hne hh m g k
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "W" => transportedMetric ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k
local notation "ω" => quasiRate ε hε h hne hh m g k
local notation "θ" => coordinateRate ε hε h hne hh m g k
local notation "ρ" => energyRate ε hε h hne hh m g k

theorem coefficient_continuity (a s : ℝ) (ha : 0 < a) :
    Continuous (F a) ∧ Continuous (S a s) ∧ Continuous (fun t => S a t s) ∧
      Continuous (C a s) ∧ Continuous (S' a s) := by
  have hf : Continuous (F a) := continuous_iff_continuousAt.mpr
    (fun t => (referenceShift_derivative ε hε h hne hh m g k a t).continuousAt)
  have hs : Continuous (S a s) := continuous_iff_continuousAt.mpr
    (fun t => (transport_derivative ε hε h hne hh m g k a s t ha).continuousAt)
  have hu : Continuous (fun t => S a t s) := continuous_iff_continuousAt.mpr
    (fun t => (transport_reverse_derivative ε hε h hne hh m g k a s t).continuousAt)
  have hc : Continuous (C a s) := continuous_iff_continuousAt.mpr
    (fun t => (connection_derivative ε hε h hne hh m g k a s t ha).continuousAt)
  have hp := referenceInverse_continuous ε hε h hne hh m g k a ha
  have hd := referenceForm_derivative_continuous ε hε h hne hh m g k
  exact ⟨hf,hs,hu,hc,((hp.mul hd).mul hs).neg⟩

theorem quasi_rate_continuous (a s : ℝ) (ha : 0 < a) : Continuous (ω a s) := by
  obtain ⟨hf,hs,hu,hc,_⟩ := coefficient_continuity ε hε h hne hh m g k a s ha
  have hd : Continuous (KFCausalShiftedForm.lowerConstant a) :=
    continuous_const.min (continuous_const.min (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
  exact (hf.norm.mul (((hs.mul hc).mul hu).norm)).div hd
    (fun t => ne_of_gt (KFCausalShiftedForm.lowerConstant_positive a t ha))

theorem coordinate_rate_continuous (a s : ℝ) (ha : 0 < a) : Continuous (θ a s) := by
  obtain ⟨hf,_,hu,_,hp⟩ := coefficient_continuity ε hε h hne hh m g k a s ha
  have hd : Continuous (KFCausalShiftedForm.lowerConstant a) :=
    continuous_const.min (continuous_const.min (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
  exact (hf.norm.mul ((hp.mul hu).norm)).div hd
    (fun t => ne_of_gt (KFCausalShiftedForm.lowerConstant_positive a t ha))

theorem energy_rate_continuous (a s : ℝ) (ha : 0 < a) : Continuous (ρ a s) :=
  (continuous_const.add (continuous_const.mul (coordinate_rate_continuous ε hε h hne hh m g k a s ha))).add
    (continuous_const.mul (quasi_rate_continuous ε hε h hne hh m g k a s ha))

theorem full_transported_bound (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbq : q a s t < b) (hbω : 2*ω a s t ≤ b) (f : V) :
    (inner ℂ (S a s t f) (F a t (S a s t (A a b s t f)))).re ≤
      (4*ω a s t)*energy (F a t) (S a s t f) :=
  KFCausalTransportedEnergyForm.pairing_bound_to_transported (S a s t) (F a t)
    (W a s t) (4*ω a s t) f (A a b s t f)
    (metric_pairing ε hε h hne hh m g k a s t f (A a b s t f))
    (metric_energy ε hε h hne hh m g k a s t f)
    (full_approximation_quasi_bound ε hε h hne hh m g k a b s t ha hb hbq hbω f)

theorem full_approximation_energy_growth (a b s κ l r : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlr : l ≤ r) (hparams : ∀ t ∈ Icc l r, q a s t < b ∧ 2*ω a s t ≤ b ∧ ρ a s t ≤ κ)
    (w : ℝ → V) (hwc : ContinuousOn w (Icc l r))
    (hw : ∀ t ∈ Ioo l r, HasDerivAt w (A a b s t (w t)) t) :
    energy (F a r) (S a s r (w r)) ≤ Real.exp (κ*(r-l))*energy (F a l) (S a s l (w l)) := by
  have hc := coefficient_continuity ε hε h hne hh m g k a s ha
  exact KFCausalTransportedQuasiGrowth.trajectory_growth (F a) D (S a s) (S' a s) (A a b s)
    (θ a s) (ω a s) κ l r hlr hc.1 hc.2.1
    (fun t => KFCausalMassResolventStability.shift_symmetric M (Q t)
      (mass_symmetric ε hε h hne hh m g k) (form_symmetric ε hε h hne hh m g k t) a)
    (referenceShift_derivative ε hε h hne hh m g k a)
    (fun t => transport_derivative ε hε h hne hh m g k a s t ha)
    (fun t _ x => KFCausalClockFloorLiftedEnergyStability.form_derivative_bound ε hε h hne hh m g k
      a t ha.le (S a s t x))
    (fun t _ x => coordinate_derivative_bound ε hε h hne hh m g k a s t ha x)
    (fun t ht x => full_transported_bound ε hε h hne hh m g k a b s t ha hb
      (hparams t ht).1 (hparams t ht).2.1 x)
    (fun t _ x => shift_energy_nonnegative ε hε h hne hh m g k a t ha (S a s t x))
    (fun t ht => (hparams t ht).2.2) w hwc hw

theorem uniform_energy_parameters (a s l r : ℝ) (ha : 0 < a) :
    ∃ b₀ κ : ℝ, 0 < b₀ ∧ 0 ≤ κ ∧ ∀ b, b₀ ≤ b → ∀ t ∈ Icc l r,
      q a s t < b ∧ 2*ω a s t ≤ b ∧ ρ a s t ≤ κ :=
  KFCausalTransportedQuasiGrowth.compact_rate_bounds (q a s) (ω a s) (ρ a s)
    (threshold_continuous ε hε h hne hh m g k a s ha)
    (quasi_rate_continuous ε hε h hne hh m g k a s ha)
    (energy_rate_continuous ε hε h hne hh m g k a s ha) l r

#print axioms coefficient_continuity
#print axioms quasi_rate_continuous
#print axioms coordinate_rate_continuous
#print axioms energy_rate_continuous
#print axioms full_transported_bound
#print axioms full_approximation_energy_growth
#print axioms uniform_energy_parameters
end
end UnifiedTheory.Audit.KFCausalClockFloorFullApproximationStability
