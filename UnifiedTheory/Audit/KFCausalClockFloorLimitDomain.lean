/- The identified full-generator state limit preserves the fixed domain
for initial domain data. Its graph outputs have a derived uniform bound. -/
import UnifiedTheory.Audit.KFCausalApproximationDomainLimit
import UnifiedTheory.Audit.KFCausalClockFloorCommonStateFamily
import UnifiedTheory.Audit.KFCausalClockFloorUniformResolventLimit
import UnifiedTheory.Audit.KFCausalClockFloorPhysicalStateApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorLimitDomain
noncomputable section
open Set Filter Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorDissipation
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "G" => fixedGenerator ε hε h hne hh m g k
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "R" => fullResolvent ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k
local notation "ω" => quasiRate ε hε h hne hh m g k
local notation "ρ" => energyRate ε hε h hne hh m g k
local notation "U" => formFlow ε hε h hne hh m g k

theorem graph_bound_of_reference (a lam s l r : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hlr : l ≤ r) (hadm : ∀ t ∈ Icc l r, q a s t < lam) :
    ∀ x y : V, (x,y) ∈ (G a s l).graph → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Icc l r, ∃ v : V, ‖v‖ ≤ C ∧
        (S a t s (U l t (S a s l x)),v) ∈ (G a s t).graph :=
  KFCausalApproximationDomainLimit.family_graph_bound (G a s) (fun b t => A a b s t)
    (fun b t => b • R a b s t) (R a lam s) (F a) (S a s) (q a s) (ω a s) (ρ a s)
    (fun t x => S a t s (U l t (S a s l x))) lam l r
    (fun b hb hq => KFCausalClockFloorFullApproximateSolutions.approximation_continuousOn
      ε hε h hne hh m g k a b s l r ha hb hq)
    (fun t ht => full_resolvent_graph ε hε h hne hh m g k a lam s t ha hlam (hadm t ht))
    (fun t ht => full_resolvent_left ε hε h hne hh m g k a lam s t ha hlam (hadm t ht))
    (fun b hb t _ hq => KFCausalQuasiResolventVelocity.smoothed_graph (G a s t)
      (R a b s t) (A a b s t) b rfl
      (full_resolvent_graph ε hε h hne hh m g k a b s t ha hb hq))
    (KFCausalClockFloorUniformResolventLimit.varying_scaled_limit ε hε h hne hh m g k a s l r ha)
    (KFCausalClockFloorCommonStateFamily.exists_common_velocity_witnesses
      ε hε h hne hh m g k a lam s l r ha hlam hlr hadm)
    (KFCausalClockFloorUniformNormControl.uniform_norm_control ε hε h hne hh m g k a s l r ha)
    (KFCausalClockFloorPhysicalStateApproximation.exists_physical_approximation ε hε h hne hh m g k a s l r ha hlr)

theorem graph_bound (a s l r : ℝ) (ha : 0 < a) (hlr : l ≤ r) :
    ∀ x y : V, (x,y) ∈ (G a s l).graph → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Icc l r, ∃ v : V, ‖v‖ ≤ C ∧
        (S a t s (U l t (S a s l x)),v) ∈ (G a s t).graph :=
  Exists.elim (KFCausalClockFloorUniformGraphApproximations.exists_reference_parameter
    ε hε h hne hh m g k a s l r ha) (fun lam hlam =>
      graph_bound_of_reference ε hε h hne hh m g k a lam s l r ha hlam.1 hlr hlam.2)

theorem coordinate_domain (a s l r : ℝ) (ha : 0 < a) (hlr : l ≤ r)
    (x : (G a s l).domain) (t : ℝ) (ht : t ∈ Icc l r) :
    S a t s (U l t (S a s l x)) ∈ (G a s t).domain :=
  KFCausalApproximationDomainLimit.domain_of_graph_bound (G a s)
    (fun t x => S a t s (U l t (S a s l x))) l r
    (graph_bound ε hε h hne hh m g k a s l r ha hlr) x t ht

#print axioms graph_bound_of_reference
#print axioms graph_bound
#print axioms coordinate_domain
end
end UnifiedTheory.Audit.KFCausalClockFloorLimitDomain
