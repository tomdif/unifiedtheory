/- Actual full-generator approximate trajectories converge uniformly in
the completed form norm for initial fixed-domain states. -/
import UnifiedTheory.Audit.KFCausalClockFloorCauchyApproximationFamily
import UnifiedTheory.Audit.KFCausalClockFloorUniformNormControl
import UnifiedTheory.Audit.KFCausalApproximationStateLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorApproximationStateLimit
noncomputable section
open Set Filter Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "G" => fixedGenerator ε hε h hne hh m g k
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k

theorem state_limit_of_reference (a lam s l r : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hlr : l ≤ r) (hadm : ∀ t ∈ Icc l r, q a s t < lam) (x y : V)
    (hxy : (x,y) ∈ (G a s l).graph) :
    ∃ B C : ℝ, 2 ≤ B ∧ 0 ≤ C ∧ ∃ w : ℕ → ℝ → V, ∃ u : ℝ → V,
      (∀ n, w n l = x ∧ ContinuousOn (w n) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (w n) (A a (B+n) s t (w n t)) (Icc l r) t) ∧
      u l = x ∧ ContinuousOn u (Icc l r) ∧ TendstoUniformlyOn w u atTop (Icc l r) ∧
      ∀ n : ℕ, ∀ t ∈ Icc l r, ‖w n t-u t‖^2 ≤ C/(B+n) :=
  KFCausalApproximationStateLimit.exists_state_limit (fun b => A a b s) (F a) (S a s) l r hlr x
    (KFCausalClockFloorCauchyApproximationFamily.exists_cauchy_family ε hε h hne hh m g k
      a lam s l r ha hlam hlr hadm x y hxy)
    (KFCausalClockFloorUniformNormControl.uniform_norm_control ε hε h hne hh m g k a s l r ha)

theorem exists_state_limit (a s l r : ℝ) (ha : 0 < a) (hlr : l ≤ r) (x y : V)
    (hxy : (x,y) ∈ (G a s l).graph) :
    ∃ B C : ℝ, 2 ≤ B ∧ 0 ≤ C ∧ ∃ w : ℕ → ℝ → V, ∃ u : ℝ → V,
      (∀ n, w n l = x ∧ ContinuousOn (w n) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (w n) (A a (B+n) s t (w n t)) (Icc l r) t) ∧
      u l = x ∧ ContinuousOn u (Icc l r) ∧ TendstoUniformlyOn w u atTop (Icc l r) ∧
      ∀ n : ℕ, ∀ t ∈ Icc l r, ‖w n t-u t‖^2 ≤ C/(B+n) :=
  Exists.elim (KFCausalClockFloorUniformGraphApproximations.exists_reference_parameter
    ε hε h hne hh m g k a s l r ha) (fun lam hlam =>
      state_limit_of_reference ε hε h hne hh m g k a lam s l r ha hlam.1 hlr hlam.2 x y hxy)

#print axioms state_limit_of_reference
#print axioms exists_state_limit
end
end UnifiedTheory.Audit.KFCausalClockFloorApproximationStateLimit
