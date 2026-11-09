/- Uniform bounds on the actual state and generator graph output along
domain-preserving full-generator approximations. The limiting flow is separate. -/
import UnifiedTheory.Audit.KFCausalClockFloorDomainApproximateSolutions
import UnifiedTheory.Audit.KFCausalClockFloorGraphEnergyStability
import UnifiedTheory.Audit.KFCausalUniformGraphTrajectories

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorUniformGraphApproximations
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
open UnifiedTheory.Audit.KFCausalClockFloorFixedResolventWindow
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorDissipation
open UnifiedTheory.Audit.KFCausalClockFloorFullApproximationStability
open UnifiedTheory.Audit.KFCausalClockFloorGeneratorGraphDerivative
open UnifiedTheory.Audit.KFCausalClockFloorDomainApproximateSolutions
open UnifiedTheory.Audit.KFCausalClockFloorGraphEnergyStability
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "G" => fixedGenerator ε hε h hne hh m g k
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "R" => fullResolvent ε hε h hne hh m g k
local notation "D" => graphCorrection ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k
local notation "ω" => quasiRate ε hε h hne hh m g k
local notation "ρ" => energyRate ε hε h hne hh m g k
local notation "σ" => graphEnergyRate ε hε h hne hh m g k

theorem exists_reference_parameter (a s l r : ℝ) (ha : 0 < a) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ t ∈ Icc l r, q a s t < lam :=
  KFCausalUniformGraphTrajectories.exists_reference_parameter (q a s) l r
    (threshold_continuous ε hε h hne hh m g k a s ha).continuousOn

theorem exists_uniform_graph_approximations (a lam s l r : ℝ) (ha : 0 < a)
    (hlam : 0 < lam) (hlr : l ≤ r) (hadm : ∀ t ∈ Icc l r, q a s t < lam) :
    ∃ b₀ κ : ℝ, 0 < b₀ ∧ 0 ≤ κ ∧ ∀ b, b₀ ≤ b → ∀ x y : V, (x,y) ∈ (G a s l).graph →
      ∃ w z : ℝ → V, w l = x ∧ z l = lam • x-y ∧
        ContinuousOn w (Icc l r) ∧ ContinuousOn z (Icc l r) ∧
        (∀ t ∈ Icc l r, w t = R a lam s t (z t)) ∧ ∀ t ∈ Icc l r,
          HasDerivWithinAt w (A a b s t (w t)) (Icc l r) t ∧
          HasDerivWithinAt z ((A a b s t-D a lam s t) (z t)) (Icc l r) t ∧
          (w t,lam • w t-z t) ∈ (G a s t).graph ∧
          energy (F a t) (S a s t (w t)) ≤ Real.exp (κ*(t-l))*energy (F a l) (S a s l x) ∧
          energy (F a t) (S a s t (z t)) ≤ Real.exp (κ*(t-l))*energy (F a l) (S a s l (lam • x-y)) ∧
          energy (F a t) (S a s t (lam • w t-z t)) ≤ Real.exp (κ*(t-l))*
            (2*lam^2*energy (F a l) (S a s l x)+2*energy (F a l) (S a s l (lam • x-y))) :=
  KFCausalUniformGraphTrajectories.exists_uniform_graph_bounds (G a s) (fun b => A a b s)
    (R a lam s) (D a lam s) (F a) (S a s) (q a s) (ω a s) (ρ a s) (σ a lam s) lam l r
    (uniform_auxiliary_parameters ε hε h hne hh m g k a lam s l r ha hlam hadm)
    (fun t => base_rate_le_graph_rate ε hε h hne hh m g k a lam s t ha)
    (fun t => KFCausalMassResolventStability.shift_symmetric M (Q t)
      (mass_symmetric ε hε h hne hh m g k) (form_symmetric ε hε h hne hh m g k t) a)
    (fun t => shift_energy_nonnegative ε hε h hne hh m g k a t ha)
    (fun b hb hq x y hxy => exists_domain_approximation ε hε h hne hh m g k a lam b s l r ha hlam hb hlr
      (fun t ht => ⟨hadm t ht,hq t ht⟩) x y hxy)
    (fun b κ t hb hlt => full_approximation_energy_growth ε hε h hne hh m g k a b s κ l t ha hb hlt)
    (fun b κ t hb hlt => auxiliary_energy_growth ε hε h hne hh m g k a lam b s κ l t ha hb hlt)

#print axioms exists_reference_parameter
#print axioms exists_uniform_graph_approximations
end
end UnifiedTheory.Audit.KFCausalClockFloorUniformGraphApproximations
