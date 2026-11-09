/- Actual bounded state operators on the completed form space.
The limiting operators are strongly continuous; no limiting strong
generator equation or physical propagator identification is asserted here. -/
import UnifiedTheory.Audit.KFCausalClockFloorAllDataStateLimit
import UnifiedTheory.Audit.KFCausalStateOperatorAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorStateOperators
noncomputable section
open Set Filter Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k

theorem exists_state_operators (a s l r : ℝ) (ha : 0 < a) (hlr : l ≤ r) :
    ∃ B L : ℝ, 2 ≤ B ∧ 0 ≤ L ∧ ∃ P : ℕ → ℝ → V →L[ℂ] V, ∃ U : ℝ → V →L[ℂ] V,
      (∀ n : ℕ, ∀ t ∈ Icc l r, q a s t < B+n) ∧
      (∀ n, P n l = 1) ∧ U l = 1 ∧
      (∀ n t, t ∈ Icc l r → ‖P n t‖ ≤ L) ∧ (∀ t ∈ Icc l r, ‖U t‖ ≤ L) ∧
      (∀ n x, ContinuousOn (fun t => P n t x) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (fun z => P n z x) (A a (B+n) s t (P n t x)) (Icc l r) t) ∧
      ∀ x, ContinuousOn (fun t => U t x) (Icc l r) ∧
        TendstoUniformlyOn (fun n t => P n t x) (fun t => U t x) atTop (Icc l r) :=
  KFCausalStateOperatorAssembly.exists_state_operators (fun b => A a b s) (q a s) l r hlr
    (fun b hb hadm => KFCausalClockFloorFullApproximateSolutions.approximation_continuousOn
      ε hε h hne hh m g k a b s l r ha hb hadm)
    (KFCausalClockFloorAllDataStateLimit.exists_all_data_limits ε hε h hne hh m g k a s l r ha hlr)

#print axioms exists_state_operators
end
end UnifiedTheory.Audit.KFCausalClockFloorStateOperators
