/- Actual full-generator approximation states converge for every initial
form-space state, with a common threshold and initial-state stability. -/
import UnifiedTheory.Audit.KFCausalClockFloorCommonStateFamily
import UnifiedTheory.Audit.KFCausalClockFloorUniformNormControl
import UnifiedTheory.Audit.KFCausalAllDataStateConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorAllDataStateLimit
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

local notation "ω" => KFCausalClockFloorFullGeneratorDissipation.quasiRate ε hε h hne hh m g k
local notation "ρ" => KFCausalClockFloorFullGeneratorDissipation.energyRate ε hε h hne hh m g k

theorem all_data_limits_of_reference (a lam s l r : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hlr : l ≤ r) (hadm : ∀ t ∈ Icc l r, q a s t < lam) :
    ∃ B L : ℝ, 2 ≤ B ∧ 0 ≤ L ∧ ∃ w : ℕ → V → ℝ → V, ∃ u : V → ℝ → V,
      (∀ n x, w n x l = x ∧ ContinuousOn (w n x) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (w n x) (A a (B+n) s t (w n x t)) (Icc l r) t) ∧
      (∀ n : ℕ, ∀ t ∈ Icc l r, q a s t < B+n) ∧
      (∀ x, u x l = x ∧ ContinuousOn (u x) (Icc l r) ∧
        TendstoUniformlyOn (fun n => w n x) (u x) atTop (Icc l r)) ∧
      (∀ n x y t, t ∈ Icc l r → ‖w n x t-w n y t‖ ≤ L*‖x-y‖) ∧
      ∀ x y t, t ∈ Icc l r → ‖u x t-u y t‖ ≤ L*‖x-y‖ :=
  KFCausalAllDataStateConvergence.exists_all_data_limits (G a s l) (fun b => A a b s)
    (F a) (S a s) (q a s) (ω a s) (ρ a s) l r hlr
    (fixed_dense ε hε h hne hh m g k a s l)
    (KFCausalClockFloorCommonStateFamily.exists_stable_family ε hε h hne hh m g k
      a lam s l r ha hlam hlr hadm)
    (KFCausalClockFloorUniformNormControl.uniform_norm_control ε hε h hne hh m g k a s l r ha)
    (fun b c κ M t hb hc hκ hM hlt => KFCausalClockFloorApproximationCauchy.difference_energy_bound
      ε hε h hne hh m g k a b c s κ M l t ha hb hc hκ hM hlt)

theorem exists_all_data_limits (a s l r : ℝ) (ha : 0 < a) (hlr : l ≤ r) :
    ∃ B L : ℝ, 2 ≤ B ∧ 0 ≤ L ∧ ∃ w : ℕ → V → ℝ → V, ∃ u : V → ℝ → V,
      (∀ n x, w n x l = x ∧ ContinuousOn (w n x) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (w n x) (A a (B+n) s t (w n x t)) (Icc l r) t) ∧
      (∀ n : ℕ, ∀ t ∈ Icc l r, q a s t < B+n) ∧
      (∀ x, u x l = x ∧ ContinuousOn (u x) (Icc l r) ∧
        TendstoUniformlyOn (fun n => w n x) (u x) atTop (Icc l r)) ∧
      (∀ n x y t, t ∈ Icc l r → ‖w n x t-w n y t‖ ≤ L*‖x-y‖) ∧
      ∀ x y t, t ∈ Icc l r → ‖u x t-u y t‖ ≤ L*‖x-y‖ :=
  Exists.elim (KFCausalClockFloorUniformGraphApproximations.exists_reference_parameter
    ε hε h hne hh m g k a s l r ha) (fun lam hlam =>
      all_data_limits_of_reference ε hε h hne hh m g k a lam s l r ha hlam.1 hlr hlam.2)

#print axioms all_data_limits_of_reference
#print axioms exists_all_data_limits
end
end UnifiedTheory.Audit.KFCausalClockFloorAllDataStateLimit
