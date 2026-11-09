/- Actual solutions of the bounded full-generator approximations on every
finite forward interval, with a common energy bound as the spectral
parameter grows. This does not assert convergence of those solutions. -/
import UnifiedTheory.Audit.KFCausalClockFloorFullApproximationStability
import UnifiedTheory.Audit.KFCausalBoundedLinearIntervalFlow
import UnifiedTheory.Audit.KFCausalClockFloorFixedResolventCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorFullApproximateSolutions
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
open UnifiedTheory.Audit.KFCausalClockFloorFixedResolventCurve
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorDissipation
open UnifiedTheory.Audit.KFCausalClockFloorFullApproximationStability
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k
local notation "ω" => quasiRate ε hε h hne hh m g k
local notation "ρ" => energyRate ε hε h hne hh m g k

theorem approximation_continuousOn (a b s l r : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hadm : ∀ t ∈ Icc l r, q a s t < b) : ContinuousOn (A a b s) (Icc l r) :=
  fun t ht => (full_approximation_derivative ε hε h hne hh m g k a b s t ha hb
    (hadm t ht)).continuousAt.continuousWithinAt

theorem exists_approximate_solution (a b s l r : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlr : l ≤ r) (hadm : ∀ t ∈ Icc l r, q a s t < b) (x : V) :
    ∃ w : ℝ → V, w l = x ∧ ContinuousOn w (Icc l r) ∧
      ∀ t ∈ Icc l r, HasDerivWithinAt w (A a b s t (w t)) (Icc l r) t :=
  KFCausalBoundedLinearIntervalFlow.exists_interval_solution (A a b s) l r hlr
    (approximation_continuousOn ε hε h hne hh m g k a b s l r ha hb hadm) x

theorem exists_uniformly_stable_approximate_solutions (a s l r : ℝ) (ha : 0 < a)
    (hlr : l ≤ r) :
    ∃ b₀ κ : ℝ, 0 < b₀ ∧ 0 ≤ κ ∧ ∀ b, b₀ ≤ b → ∀ x : V,
      ∃ w : ℝ → V, w l = x ∧ ContinuousOn w (Icc l r) ∧
        (∀ t ∈ Icc l r, HasDerivWithinAt w (A a b s t (w t)) (Icc l r) t) ∧
        ∀ t ∈ Icc l r, energy (F a t) (S a s t (w t)) ≤
          Real.exp (κ*(t-l))*energy (F a l) (S a s l x) :=
  KFCausalBoundedLinearIntervalFlow.exists_uniformly_stable_solutions
    (fun b => A a b s) (F a) (S a s) (q a s) (ω a s) (ρ a s) l r hlr
    (uniform_energy_parameters ε hε h hne hh m g k a s l r ha)
    (fun b hb hadm => approximation_continuousOn ε hε h hne hh m g k a b s l r ha hb hadm)
    (fun b κ t hb hlt => full_approximation_energy_growth ε hε h hne hh m g k a b s κ l t ha hb hlt)

#print axioms approximation_continuousOn
#print axioms exists_approximate_solution
#print axioms exists_uniformly_stable_approximate_solutions
end
end UnifiedTheory.Audit.KFCausalClockFloorFullApproximateSolutions
