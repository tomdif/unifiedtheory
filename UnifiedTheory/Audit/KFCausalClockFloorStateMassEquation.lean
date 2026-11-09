/- Every uniform form-state limit of admissible full-generator
approximations satisfies the actual transported mass equation. -/
import UnifiedTheory.Audit.KFCausalClockFloorUniformResolventLimit
import UnifiedTheory.Audit.KFCausalTransportedMassLimit
import UnifiedTheory.Audit.KFCausalQuasiResolventVelocity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorStateMassEquation
noncomputable section
open Set Filter Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "D" => referenceFormDerivative ε hε h hne hh m g k
local notation "P" => referenceInverse ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "S'" => transportDerivative ε hε h hne hh m g k
local notation "R" => fullResolvent ε hε h hne hh m g k
local notation "G" => fixedGenerator ε hε h hne hh m g k
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

theorem transport_derivative_continuous (a s : ℝ) (ha : 0 < a) : Continuous (S' a s) := by
  have hp := referenceInverse_continuous ε hε h hne hh m g k a ha
  have hd := referenceForm_derivative_continuous ε hε h hne hh m g k
  have hs : Continuous (S a s) := continuous_iff_continuousAt.mpr
    (fun t => (transport_derivative ε hε h hne hh m g k a s t ha).continuousAt)
  exact ((hp.mul hd).mul hs).neg

theorem smoothed_mass_equation (a b s t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hadm : q a s t < b) (x : V) :
    M (S a s t (A a b s t x)+S' a s t (b • R a b s t x)) =
      c • Q t (S a s t (b • R a b s t x)) :=
  KFCausalTransportedMassLimit.mass_equation_from_graph (G a s t) M (S a s t) (S' a s t)
    (c • Q t) (R a b s t) (A a b s t) b rfl
    (full_resolvent_graph ε hε h hne hh m g k a b s t ha hb hadm)
    (transported_mass_equation ε hε h hne hh m g k a s t ha) x

theorem uniform_limit_mass_equation (a s l r : ℝ) (ha : 0 < a)
    (b : ℕ → ℝ) (hb : Tendsto b atTop atTop) (hbp : ∀ n, 0 < b n)
    (hadm : ∀ n t, t ∈ Icc l r → q a s t < b n)
    (w : ℕ → ℝ → V) (u : ℝ → V) (hu : ContinuousOn u (Icc l r))
    (hw : TendstoUniformlyOn w u atTop (Icc l r))
    (hd : ∀ n t, t ∈ Icc l r →
      HasDerivWithinAt (w n) (A a (b n) s t (w n t)) (Icc l r) t)
    (t : ℝ) (ht : t ∈ Ioo l r) :
    HasDerivAt (fun z => M (S a s z (u z))) (c • Q t (S a s t (u t))) t := by
  have hQ : Continuous Q := continuous_iff_continuousAt.mpr
    (fun z => (referenceForm_derivative ε hε h hne hh m g k z).continuousAt)
  exact KFCausalTransportedMassLimit.mass_derivative_limit M (S a s) (S' a s) (fun z => c • Q z)
    (fun n z => A a (b n) s z) (fun n z => b n • R a (b n) s z) w u l r
    (fun z => transport_derivative ε hε h hne hh m g k a s z ha)
    (transport_derivative_continuous ε hε h hne hh m g k a s ha).continuousOn
    (hQ.const_smul c).continuousOn hd
    (fun n z hz => smoothed_mass_equation ε hε h hne hh m g k a (b n) s z ha (hbp n) (hadm n z hz) (w n z))
    hw (KFCausalClockFloorUniformResolventLimit.varying_scaled_limit ε hε h hne hh m g k a s l r ha b hb w u hu hw)
    t ht

#print axioms transport_derivative_continuous
#print axioms smoothed_mass_equation
#print axioms uniform_limit_mass_equation
end
end UnifiedTheory.Audit.KFCausalClockFloorStateMassEquation
