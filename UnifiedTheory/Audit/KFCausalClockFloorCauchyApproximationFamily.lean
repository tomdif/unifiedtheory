/- Actual full-generator approximate trajectories form an energy-Cauchy
sequence on every finite interval for initial data in the fixed domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorUniformGraphApproximations
import UnifiedTheory.Audit.KFCausalClockFloorApproximationCauchy
import UnifiedTheory.Audit.KFCausalCauchyApproximationFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorCauchyApproximationFamily
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

theorem exists_velocity_family (a lam s l r : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hlr : l ≤ r) (hadm : ∀ t ∈ Icc l r, q a s t < lam) (x y : V)
    (hxy : (x,y) ∈ (G a s l).graph) :
    ∃ B κ M : ℝ, 2 ≤ B ∧ 0 ≤ κ ∧ 0 ≤ M ∧ ∃ w : ℕ → ℝ → V, ∀ n,
      w n l = x ∧ ContinuousOn (w n) (Icc l r) ∧ ∀ t ∈ Icc l r,
        HasDerivWithinAt (w n) (A a (B+n) s t (w n t)) (Icc l r) t ∧
        energy (F a t) (S a s t (A a (B+n) s t (w n t))) ≤ M ∧
        q a s t < B+n ∧ 2*ω a s t ≤ B+n ∧ ρ a s t ≤ κ :=
  KFCausalGraphVelocityFamily.exists_velocity_family (G a s) (fun b => A a b s)
    (R a lam s) (D a lam s) (F a) (S a s) (q a s) (ω a s) (ρ a s) lam l r
    (fun t v => shift_energy_nonnegative ε hε h hne hh m g k a t ha (S a s t v))
    (uniform_energy_parameters ε hε h hne hh m g k a s l r ha)
    (exists_uniform_graph_approximations ε hε h hne hh m g k a lam s l r ha hlam hlr hadm)
    (fun b hb t _ hbq hbω => transported_velocity_energy ε hε h hne hh m g k a b s t ha hb hbq hbω)
    x y hxy

theorem exists_cauchy_family (a lam s l r : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hlr : l ≤ r) (hadm : ∀ t ∈ Icc l r, q a s t < lam) (x y : V)
    (hxy : (x,y) ∈ (G a s l).graph) :
    ∃ B C : ℝ, 2 ≤ B ∧ 0 ≤ C ∧ ∃ w : ℕ → ℝ → V,
      (∀ n, w n l = x ∧ ContinuousOn (w n) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (w n) (A a (B+n) s t (w n t)) (Icc l r) t) ∧
      ∀ n m : ℕ, ∀ t ∈ Icc l r,
        energy (F a t) (S a s t (w n t-w m t)) ≤ C*(1/(B+n)+1/(B+m)) :=
  KFCausalCauchyApproximationFamily.exists_cauchy_family (fun b => A a b s)
    (F a) (S a s) (q a s) (ω a s) (ρ a s) l r hlr x
    (exists_velocity_family ε hε h hne hh m g k a lam s l r ha hlam hlr hadm x y hxy)
    (fun b c κ M t hb hc hκ hM hlt => difference_energy_bound ε hε h hne hh m g k a b c s κ M l t
      ha hb hc hκ hM hlt)

#print axioms exists_velocity_family
#print axioms exists_cauchy_family
end
end UnifiedTheory.Audit.KFCausalClockFloorCauchyApproximationFamily
