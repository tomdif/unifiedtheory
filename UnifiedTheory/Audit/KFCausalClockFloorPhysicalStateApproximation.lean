/- The actual full-generator approximations converge, for all completed
form-space initial states, to the existing physical form evolution in the
fixed coordinates. The physical clock regulator remains positive and fixed. -/
import UnifiedTheory.Audit.KFCausalClockFloorStateLimitIdentification
import UnifiedTheory.Audit.KFCausalClockFloorStateOperators
import UnifiedTheory.Audit.KFCausalIdentifiedStateOperatorAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorPhysicalStateApproximation
noncomputable section
open Set Filter Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "S" => transport ε hε h hne hh m g k
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k
local notation "F" => formFlow ε hε h hne hh m g k

theorem exists_physical_approximation (a s l r : ℝ) (ha : 0 < a) (hlr : l ≤ r) :
    ∃ B L : ℝ, 2 ≤ B ∧ 0 ≤ L ∧ ∃ P : ℕ → ℝ → V →L[ℂ] V,
      (∀ n : ℕ, ∀ t ∈ Icc l r, q a s t < B+n) ∧
      (∀ n, P n l = 1) ∧ (∀ n t, t ∈ Icc l r → ‖P n t‖ ≤ L) ∧
      (∀ n x, ContinuousOn (fun t => P n t x) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (fun z => P n z x) (A a (B+n) s t (P n t x)) (Icc l r) t) ∧
      ∀ x, ContinuousOn (fun t => S a t s (F l t (S a s l x))) (Icc l r) ∧
        TendstoUniformlyOn (fun n t => P n t x)
          (fun t => S a t s (F l t (S a s l x))) atTop (Icc l r) := by
  have hS : Continuous (fun t => S a t s) := continuous_iff_continuousAt.mpr
    (fun t => (transport_reverse_derivative ε hε h hne hh m g k a s t).continuousAt)
  exact KFCausalIdentifiedStateOperatorAssembly.identify (fun b t => A a b s t) (q a s)
    (fun t x => S a t s (F l t (S a s l x))) l r
    (fun x => (hS.clm_apply (formFlow_continuous ε hε h hne hh m g k l (S a s l x))).continuousOn)
    (KFCausalClockFloorStateLimitIdentification.uniform_limit_coordinate_formula ε hε h hne hh m g k a s l r ha)
    (KFCausalClockFloorStateOperators.exists_state_operators ε hε h hne hh m g k a s l r ha hlr)

#print axioms exists_physical_approximation
end
end UnifiedTheory.Audit.KFCausalClockFloorPhysicalStateApproximation
