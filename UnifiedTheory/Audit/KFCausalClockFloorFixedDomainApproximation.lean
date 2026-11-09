/- Consistent bounded approximations of the fixed-domain generator,
including its connection, and their uniform forward energy stability.
Strong-flow existence and Hamiltonian-domain propagation remain separate. -/
import UnifiedTheory.Audit.KFCausalClockFloorLiftedEnergyStability
import UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
import UnifiedTheory.Audit.KFCausalMovingGeneratorApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorFixedDomainApproximation
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorLiftedRegularization
open UnifiedTheory.Audit.KFCausalClockFloorLiftedEnergyStability
open UnifiedTheory.Audit.KFCausalComplexMassPencil (phase)
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "L" => liftedHamiltonian ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "S'" => transportDerivative ε hε h hne hh m g k
local notation "C" => connection ε hε h hne hh m g k
local notation "A" => regularization ε hε h hne hh m g k
local notation "G" => fixedGenerator ε hε h hne hh m g k

def fixedApproximation (a b s t : ℝ) : V →L[ℂ] V :=
  KFCausalMovingGeneratorApproximation.transformed (S a s t) (S a t s) (C a s t) (A b t)

theorem transport_inverse (a s t : ℝ) (ha : 0 < a) (v : V) :
    S a s t (S a t s v) = v := by
  have he := congrArg (fun T : V →L[ℂ] V => T v)
    (transport_compose ε hε h hne hh m g k a t s t ha)
  exact he.trans (congrArg (fun T : V →L[ℂ] V => T v)
    (transport_initial ε hε h hne hh m g k a t ha))

theorem connection_cancels_apply (a s t : ℝ) (ha : 0 < a) (v : V) :
    S a s t (C a s t v) = -S' a s t v :=
  congrArg (fun T : V →L[ℂ] V => T v)
    (connection_cancels ε hε h hne hh m g k a s t ha)

theorem approximation_continuous (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Continuous (fixedApproximation ε hε h hne hh m g k a b s) := by
  have hs : Continuous (S a s) := continuous_iff_continuousAt.mpr
    (fun t => (transport_derivative ε hε h hne hh m g k a s t ha).continuousAt)
  have hr : Continuous (fun t => S a t s) := continuous_iff_continuousAt.mpr
    (fun t => (transport_reverse_derivative ε hε h hne hh m g k a s t).continuousAt)
  have hc : Continuous (C a s) := continuous_iff_continuousAt.mpr
    (fun t => (connection_derivative ε hε h hne hh m g k a s t ha).continuousAt)
  exact (hr.mul ((regularization_continuous ε hε h hne hh m g k b hb).mul hs)).add hc

theorem approximation_strong_limit (a s t : ℝ) (ha : 0 < a) (w : (L s).domain) :
    Tendsto (fun b : ℝ => fixedApproximation ε hε h hne hh m g k a b s t (w:V))
      atTop (𝓝 (G a s t w)) := by
  let v : V := L s w+a • (w:V)-a • S a s t w
  have hg := transport_lifted_graph ε hε h hne hh m g k a s t ha (w:V) (L s w)
    ((L s).mem_graph w)
  exact KFCausalMovingGeneratorApproximation.transformed_graph_limit
    (L t) (S a s t) (S a t s) (C a s t) (S' a s t) (fun b => A b t) (phase h)
    (transport_inverse ε hε h hne hh m g k a s t ha)
    (transport_inverse ε hε h hne hh m g k a t s ha)
    (connection_cancels_apply ε hε h hne hh m g k a s t ha)
    (regularization_strong_limit ε hε h hne hh m g k t)
    (w:V) v (G a s t w) hg (transported_action ε hε h hne hh m g k a s t ha w)

theorem approximate_curve_transport (a b s t : ℝ) (ha : 0 < a) (w : ℝ → V)
    (hw : HasDerivAt w (fixedApproximation ε hε h hne hh m g k a b s t (w t)) t) :
    HasDerivAt (fun r => S a s r (w r)) (A b t (S a s t (w t))) t :=
  KFCausalMovingGeneratorApproximation.transported_derivative
    (S a s) (fun r => S a r s) (C a s) (A b) (S' a s)
    (fun r => transport_derivative ε hε h hne hh m g k a s r ha)
    (fun r => transport_inverse ε hε h hne hh m g k a s r ha)
    (fun r => connection_cancels_apply ε hε h hne hh m g k a s r ha) w t hw

theorem fixed_approximation_energy_bound (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (w : ℝ → V)
    (hw : ∀ r, HasDerivAt w (fixedApproximation ε hε h hne hh m g k a b s r (w r)) r)
    (hst : s ≤ t) :
    energy (F a t) (S a s t (w t)) ≤ Real.exp (2*(t-s))*energy (F a s) (w s) := by
  have he := regularized_energy_bound ε hε h hne hh m g k a b ha hb
    (fun r => S a s r (w r))
    (fun r => approximate_curve_transport ε hε h hne hh m g k a b s r ha w (hw r)) s t hst
  have hi : S a s s (w s) = w s :=
    congrArg (fun T : V →L[ℂ] V => T (w s))
      (transport_initial ε hε h hne hh m g k a s ha)
  exact he.trans_eq (congrArg (fun z : V => Real.exp (2*(t-s))*energy (F a s) z) hi)

#print axioms transport_inverse
#print axioms connection_cancels_apply
#print axioms approximation_continuous
#print axioms approximation_strong_limit
#print axioms approximate_curve_transport
#print axioms fixed_approximation_energy_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorFixedDomainApproximation
