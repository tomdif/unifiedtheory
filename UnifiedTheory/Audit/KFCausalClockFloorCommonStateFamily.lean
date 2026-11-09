/- A common full-generator approximation family for every form-space state,
with derived initial-state stability and graph-data velocity budgets. -/
import UnifiedTheory.Audit.KFCausalClockFloorUniformGraphApproximations
import UnifiedTheory.Audit.KFCausalClockFloorApproximationCauchy
import UnifiedTheory.Audit.KFCausalCommonStableFamily
import UnifiedTheory.Audit.KFCausalClockFloorUniformNormControl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorCommonStateFamily
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorDissipation
open UnifiedTheory.Audit.KFCausalClockFloorFullApproximationStability
open UnifiedTheory.Audit.KFCausalClockFloorGeneratorGraphDerivative
open UnifiedTheory.Audit.KFCausalClockFloorUniformGraphApproximations
open UnifiedTheory.Audit.KFCausalClockFloorApproximationComparison
open UnifiedTheory.Audit.KFCausalClockFloorApproximationCauchy
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "G" => fixedGenerator ε hε h hne hh m g k
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "R" => fullResolvent ε hε h hne hh m g k
local notation "D" => graphCorrection ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k
local notation "ω" => quasiRate ε hε h hne hh m g k
local notation "ρ" => energyRate ε hε h hne hh m g k

theorem exists_common_velocity_witnesses (a lam s l r : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hlr : l ≤ r) (hadm : ∀ t ∈ Icc l r, q a s t < lam) :
    ∃ B κ : ℝ, 2 ≤ B ∧ 0 ≤ κ ∧
      (∀ b, B ≤ b → ∀ t ∈ Icc l r, q a s t < b ∧ 2*ω a s t ≤ b ∧ ρ a s t ≤ κ) ∧
      ∀ x y : V, (x,y) ∈ (G a s l).graph → ∃ M : ℝ, 0 ≤ M ∧ ∀ b, B ≤ b →
        ∃ w : ℝ → V, w l = x ∧ ContinuousOn w (Icc l r) ∧ ∀ t ∈ Icc l r,
          HasDerivWithinAt w (A a b s t (w t)) (Icc l r) t ∧
          energy (F a t) (S a s t (A a b s t (w t))) ≤ M :=
  KFCausalCommonVelocityWitnesses.exists_common_witnesses (G a s) (fun b => A a b s)
    (R a lam s) (D a lam s) (F a) (S a s) (q a s) (ω a s) (ρ a s) lam l r
    (fun t v => shift_energy_nonnegative ε hε h hne hh m g k a t ha (S a s t v))
    (uniform_energy_parameters ε hε h hne hh m g k a s l r ha)
    (exists_uniform_graph_approximations ε hε h hne hh m g k a lam s l r ha hlam hlr hadm)
    (fun b hb t _ hbq hbω => transported_velocity_energy ε hε h hne hh m g k a b s t ha hb hbq hbω)

theorem exists_stable_family (a lam s l r : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hlr : l ≤ r) (hadm : ∀ t ∈ Icc l r, q a s t < lam) :
    ∃ B κ L : ℝ, 2 ≤ B ∧ 0 ≤ κ ∧ 0 ≤ L ∧ ∃ w : ℕ → V → ℝ → V,
      (∀ n x, w n x l = x ∧ ContinuousOn (w n x) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (w n x) (A a (B+n) s t (w n x t)) (Icc l r) t) ∧
      (∀ n : ℕ, ∀ t ∈ Icc l r, q a s t < B+n ∧ 2*ω a s t ≤ B+n ∧ ρ a s t ≤ κ) ∧
      (∀ n x y t, t ∈ Icc l r → ‖w n x t-w n y t‖ ≤ L*‖x-y‖) ∧
      ∀ x y : V, (x,y) ∈ (G a s l).graph → ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ t ∈ Icc l r,
        energy (F a t) (S a s t (A a (B+n) s t (w n x t))) ≤ M :=
  KFCausalCommonStableFamily.exists_stable_family (G a s l) (fun b => A a b s) (F a) (S a s)
    (q a s) (ω a s) (ρ a s) l r
    (exists_common_velocity_witnesses ε hε h hne hh m g k a lam s l r ha hlam hlr hadm)
    (fun b hb hadmb => KFCausalClockFloorFullApproximateSolutions.approximation_continuousOn
      ε hε h hne hh m g k a b s l r ha hb hadmb)
    (fun b hb hadmb => KFCausalClockFloorFullApproximateSolutions.exists_approximate_solution
      ε hε h hne hh m g k a b s l r ha hb hlr hadmb)
    (fun b κ t hb hlt => full_approximation_energy_growth ε hε h hne hh m g k a b s κ l t ha hb hlt)
    (KFCausalClockFloorUniformNormControl.uniform_norm_control ε hε h hne hh m g k a s l r ha)

#print axioms exists_common_velocity_witnesses
#print axioms exists_stable_family
end
end UnifiedTheory.Audit.KFCausalClockFloorCommonStateFamily
