/- Derived quasi-dissipativity of the full fixed-domain generator and
uniform energy growth of its bounded regularizations at a fixed time. -/
import UnifiedTheory.Audit.KFCausalClockFloorFixedResolventWindow
import UnifiedTheory.Audit.KFCausalQuasiDissipativeResolvent
import UnifiedTheory.Audit.KFCausalTransportedEnergyForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorDissipation
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorLiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorFixedDomainApproximation
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)
open UnifiedTheory.Audit.KFCausalComplexMassPencil (phase)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "L" => liftedHamiltonian ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "S'" => transportDerivative ε hε h hne hh m g k
local notation "C" => connection ε hε h hne hh m g k
local notation "G" => fixedGenerator ε hε h hne hh m g k
local notation "R" => fullResolvent ε hε h hne hh m g k
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k

def transportedMetric (a s t : ℝ) : V →L[ℂ] V := KFCausalTransportedEnergyForm.metric (S a s t) (F a t)

def quasiRate (a s t : ℝ) : ℝ :=
  ‖F a t‖*‖(S a s t*C a s t)*S a t s‖/KFCausalShiftedForm.lowerConstant a t

def coordinateRate (a s t : ℝ) : ℝ :=
  ‖F a t‖*‖S' a s t*S a t s‖/KFCausalShiftedForm.lowerConstant a t

def energyRate (a s t : ℝ) : ℝ := 2+2*coordinateRate ε hε h hne hh m g k a s t+
  8*quasiRate ε hε h hne hh m g k a s t

theorem metric_energy (a s t : ℝ) (x : V) :
    energy (transportedMetric ε hε h hne hh m g k a s t) x = energy (F a t) (S a s t x) :=
  KFCausalTransportedEnergyForm.metric_energy (S a s t) (F a t) x

theorem metric_pairing (a s t : ℝ) (x y : V) :
    inner ℂ x (transportedMetric ε hε h hne hh m g k a s t y) =
      inner ℂ (S a s t x) (F a t (S a s t y)) :=
  KFCausalTransportedEnergyForm.metric_pairing (S a s t) (F a t) x y

theorem metric_symmetric (a s t : ℝ) :
    (transportedMetric ε hε h hne hh m g k a s t).toLinearMap.IsSymmetric :=
  KFCausalTransportedEnergyForm.metric_symmetric (S a s t) (F a t)
    (KFCausalMassResolventStability.shift_symmetric M (Q t)
      (mass_symmetric ε hε h hne hh m g k) (form_symmetric ε hε h hne hh m g k t) a)

theorem metric_nonnegative (a s t : ℝ) (ha : 0 < a) (x : V) :
    0 ≤ energy (transportedMetric ε hε h hne hh m g k a s t) x :=
  KFCausalTransportedEnergyForm.metric_nonnegative (S a s t) (F a t)
    (shift_energy_nonnegative ε hε h hne hh m g k a t ha) x

theorem quasi_rate_nonnegative (a s t : ℝ) (ha : 0 < a) : 0 ≤ quasiRate ε hε h hne hh m g k a s t :=
  div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (KFCausalShiftedForm.lowerConstant_positive a t ha).le

theorem coordinate_rate_nonnegative (a s t : ℝ) (ha : 0 < a) :
    0 ≤ coordinateRate ε hε h hne hh m g k a s t :=
  div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (KFCausalShiftedForm.lowerConstant_positive a t ha).le

theorem lifted_diagonal_real (a t : ℝ) (x y : V) (hxy : (x,y) ∈ (L t).graph) :
    (inner ℂ x (F a t y)).im = 0 :=
  KFCausalWeightedMassEnergy.weighted_diagonal_real M (Q t)
    (mass_symmetric ε hε h hne hh m g k) (form_symmetric ε hε h hne hh m g k t) a x y
    ((lifted_graph_iff ε hε h hne hh m g k t x y).mp hxy)

theorem full_generator_quasi_bound (a s t : ℝ) (ha : 0 < a) (x y : V)
    (hxy : (x,y) ∈ (G a s t).graph) :
    (inner ℂ x (transportedMetric ε hε h hne hh m g k a s t y)).re ≤
      quasiRate ε hε h hne hh m g k a s t*energy (transportedMetric ε hε h hne hh m g k a s t) x :=
  KFCausalTransportedEnergyForm.quasi_bound_of_eq (L t) (G a s t) (F a t) (S a s t) (S a t s)
    (C a s t) (transportedMetric ε hε h hne hh m g k a s t) (phase h)
    (KFCausalShiftedForm.lowerConstant a t) (quasiRate ε hε h hne hh m g k a s t) rfl rfl
    (KFCausalComplexMassPencil.phase_real h) (KFCausalShiftedForm.lowerConstant_positive a t ha)
    (transport_inverse ε hε h hne hh m g k a t s ha)
    (shift_energy_coercive ε hε h hne hh m g k a t)
    (conjugated_action ε hε h hne hh m g k a s t ha)
    (fun w z hz => lifted_diagonal_real ε hε h hne hh m g k a t (S a s t w) z hz) x y hxy

theorem full_approximation_quasi_bound (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbq : q a s t < b) (hbω : 2*quasiRate ε hε h hne hh m g k a s t ≤ b) (f : V) :
    (inner ℂ f (transportedMetric ε hε h hne hh m g k a s t (A a b s t f))).re ≤
      (4*quasiRate ε hε h hne hh m g k a s t)*
        energy (transportedMetric ε hε h hne hh m g k a s t) f :=
  KFCausalQuasiDissipativeResolvent.approximation_bound (G a s t)
    (transportedMetric ε hε h hne hh m g k a s t) (R a b s t) (A a b s t) b
    (quasiRate ε hε h hne hh m g k a s t)
    (metric_symmetric ε hε h hne hh m g k a s t)
    (metric_nonnegative ε hε h hne hh m g k a s t ha) hb
    (quasi_rate_nonnegative ε hε h hne hh m g k a s t ha) hbω rfl
    (full_resolvent_graph ε hε h hne hh m g k a b s t ha hb hbq)
    (full_generator_quasi_bound ε hε h hne hh m g k a s t ha) f

theorem coordinate_derivative_bound (a s t : ℝ) (ha : 0 < a) (f : V) :
    (inner ℂ (S a s t f) (F a t (S' a s t f))).re ≤
      coordinateRate ε hε h hne hh m g k a s t*energy (F a t) (S a s t f) :=
  KFCausalTransportedEnergyForm.bounded_transported_output (F a t) (S a s t) (S a t s) (S' a s t)
    (KFCausalShiftedForm.lowerConstant a t) (KFCausalShiftedForm.lowerConstant_positive a t ha)
    (transport_inverse ε hε h hne hh m g k a t s ha)
    (shift_energy_coercive ε hε h hne hh m g k a t) f

#print axioms metric_energy
#print axioms metric_pairing
#print axioms metric_symmetric
#print axioms metric_nonnegative
#print axioms quasi_rate_nonnegative
#print axioms coordinate_rate_nonnegative
#print axioms lifted_diagonal_real
#print axioms full_generator_quasi_bound
#print axioms full_approximation_quasi_bound
#print axioms coordinate_derivative_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorDissipation
