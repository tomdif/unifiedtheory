/- A consistent bounded approximation to the actual lifted Schrodinger
generator, with cutoff-independent shifted-form dissipation. The existence
of its limiting strong evolution is a separate obligation. -/
import UnifiedTheory.Audit.KFCausalClockFloorLiftedResolvent
import UnifiedTheory.Audit.KFCausalDenseResolventConvergence
import UnifiedTheory.Audit.KFCausalComplexMassCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorLiftedRegularization
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorLiftedResolvent
open UnifiedTheory.Audit.KFCausalComplexMassPencil (phase)
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "D" => referenceFormDerivative ε hε h hne hh m g k
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "L" => liftedHamiltonian ε hε h hne hh m g k
local notation "R" => schrodingerResolvent ε hε h hne hh m g k

def regularization (b t : ℝ) : V →L[ℂ] V := KFCausalMassResolventStability.approximation M (Q t) h b

def regularizationDerivative (b t : ℝ) : V →L[ℂ] V :=
  b • (b • KFCausalComplexMassCurve.derivative M Q D h b t)

theorem scaled_strong_limit (t : ℝ) (f : V) :
    Tendsto (fun b : ℝ => b • R b t f) atTop (𝓝 f) :=
  KFCausalDenseResolventConvergence.scaled_strong_limit (L t) (fun b => R b t) (phase h)
    (Real.sqrt (‖F 1 t‖/KFCausalShiftedForm.lowerConstant 1 t)) (Real.sqrt_nonneg _)
    (lifted_dense ε hε h hne hh m g k t)
    (fun b hb f => scaled_norm_bound ε hε h hne hh m g k 1 b t (by norm_num) hb f)
    (fun b hb x => resolvent_left ε hε h hne hh m g k b t hb x) f

theorem regularization_on_domain (b t : ℝ) (hb : 0 < b) (x : (L t).domain) :
    regularization ε hε h hne hh m g k b t (x:V) = b • R b t (phase h • L t x) :=
  KFCausalDenseResolventConvergence.generator_on_domain (L t) (R b t) (phase h) b
    (resolvent_left ε hε h hne hh m g k b t hb) x

theorem regularization_strong_limit (t : ℝ) (x : (L t).domain) :
    Tendsto (fun b : ℝ => regularization ε hε h hne hh m g k b t (x:V))
      atTop (𝓝 (phase h • L t x)) := by
  apply (scaled_strong_limit ε hε h hne hh m g k t (phase h • L t x)).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb
  exact (regularization_on_domain ε hε h hne hh m g k b t hb x).symm

theorem regularization_dissipation (a b t : ℝ) (hb : 0 < b) (f : V) :
    (inner ℂ f (F a t (regularization ε hε h hne hh m g k b t f))).re =
      -b*Complex.normSq (phase h)*energy (F a t) (resolvedOutput ε hε h hne hh m g k b t f) :=
  KFCausalMassResolventStability.approximation_dissipation M (Q t)
    (mass_symmetric ε hε h hne hh m g k) (form_symmetric ε hε h hne hh m g k t)
    h b a hne (complex_pencil_isUnit ε hε h hne hh m g k b t hb) f

theorem regularization_nonpositive (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (f : V) :
    (inner ℂ f (F a t (regularization ε hε h hne hh m g k b t f))).re ≤ 0 :=
  KFCausalMassResolventStability.approximation_nonpositive M (Q t)
    (mass_symmetric ε hε h hne hh m g k) (form_symmetric ε hε h hne hh m g k t)
    h b a hne hb.le (complex_pencil_isUnit ε hε h hne hh m g k b t hb)
    (shift_energy_nonnegative ε hε h hne hh m g k a t ha) f

theorem regularization_derivative (b t : ℝ) (hb : 0 < b) :
    HasDerivAt (regularization ε hε h hne hh m g k b)
      (regularizationDerivative ε hε h hne hh m g k b t) t :=
  KFCausalComplexMassCurve.approximation_derivative M Q D h b t
    (referenceForm_derivative ε hε h hne hh m g k t)
    (complex_pencil_isUnit ε hε h hne hh m g k b t hb)

theorem regularization_continuous (b : ℝ) (hb : 0 < b) :
    Continuous (regularization ε hε h hne hh m g k b) :=
  continuous_iff_continuousAt.mpr
    (fun t => (regularization_derivative ε hε h hne hh m g k b t hb).continuousAt)

theorem regularization_derivative_continuous (b : ℝ) (hb : 0 < b) :
    Continuous (regularizationDerivative ε hε h hne hh m g k b) :=
  ((KFCausalComplexMassCurve.derivative_continuous M Q D h b
    (continuous_iff_continuousAt.mpr
      (fun t => (referenceForm_derivative ε hε h hne hh m g k t).continuousAt))
    (referenceForm_derivative_continuous ε hε h hne hh m g k)
    (fun t => complex_pencil_isUnit ε hε h hne hh m g k b t hb)).const_smul b).const_smul b

#print axioms scaled_strong_limit
#print axioms regularization_on_domain
#print axioms regularization_strong_limit
#print axioms regularization_dissipation
#print axioms regularization_nonpositive
#print axioms regularization_derivative
#print axioms regularization_continuous
#print axioms regularization_derivative_continuous
end
end UnifiedTheory.Audit.KFCausalClockFloorLiftedRegularization
