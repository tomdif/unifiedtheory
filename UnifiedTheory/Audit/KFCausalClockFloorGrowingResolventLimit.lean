/- Strong convergence of the actual rescaled shifted resolvents to the
constructed growing Hamiltonian resolvent, including convergence in the
growing form norm and decay of the static penalty on these resolvent states.
This is an operator limit, not a long-time propagator comparison. -/
import UnifiedTheory.Audit.KFCausalPenaltyVariationalLimit
import UnifiedTheory.Audit.KFCausalClockFloorFastResolventIdentification

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingResolventLimit
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (FormSpace)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity (staticMap)
open UnifiedTheory.Audit.KFCausalClockFloorFastResolvent

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "I" => inclusion ε hε h hne hb m g k
local notation "A" => staticMap ε hε h hne hb m g k
local notation "r" => formLift ε hε h hne hb m g k
local notation "T" => target ε hε h hne hb m g k
local notation "D" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hne hb m g k

theorem comparison_budget (u : ℝ) (hu : 0 < u) (f : Hilbert) (v : V) :
    ‖I (r u f)-T f‖^2+(1/u)*‖A (r u f)‖^2 ≤ ‖I v-T f‖^2+(1/u)*‖A v‖^2 :=
  KFCausalPenaltyVariationalLimit.variational_minimum I A (T f) (1/u)
    (one_div_pos.mpr hu).le (r u f) v (variational ε hε h hne hb m g k u hu f)

theorem total_error_limit (f : Hilbert) :
    Tendsto (fun u => ‖I (r u f)-T f‖^2+(1/u)*‖A (r u f)‖^2) atTop (𝓝 0) :=
  KFCausalPenaltyVariationalLimit.cost_tendsto_zero I A (inclusion_dense ε hε h hne hb m g k)
    (T f) (fun u => r u f) (fun u hu => variational ε hε h hne hb m g k u hu f)

theorem form_strong_limit (f : Hilbert) :
    Tendsto (fun u => I (r u f)) atTop (𝓝 (T f)) :=
  KFCausalPenaltyVariationalLimit.strong_limit I A (inclusion_dense ε hε h hne hb m g k)
    (T f) (fun u => r u f) (fun u hu => variational ε hε h hne hb m g k u hu f)

private theorem mapped_limit {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (L : X → Y) (hL : Continuous L) (v : ℝ → X) (w : X) (q : ℝ → Y) (y : Y)
    (hv : Tendsto v atTop (𝓝 w)) (he : ∀ u, L (v u) = q u) (hy : L w = y) :
    Tendsto q atTop (𝓝 y) := by
  rw [← hy]
  exact ((hL.tendsto w).comp hv).congr' (Eventually.of_forall he)

theorem physical_strong_limit (f : Hilbert) :
    Tendsto (fun u => resolvent ε hε h hne hb m g k u f) atTop
      (𝓝 (limitResolvent ε hε h hne hb m g k f)) :=
  mapped_limit (KFCausalClosedGraphForm.embedding D)
    (KFCausalClosedGraphForm.embedding D).continuous (fun u => I (r u f)) (T f)
    (fun u => resolvent ε hε h hne hb m g k u f) (limitResolvent ε hε h hne hb m g k f)
    (form_strong_limit ε hε h hne hb m g k f)
    (fun u => (inclusion_embedding ε hε h hne hb m g k (r u f)).trans
      (formLift_embedding ε hε h hne hb m g k u f)) rfl

theorem growing_output_strong_limit (f : Hilbert) :
    Tendsto (fun u => KFCausalClockFloorAveragedRegularity.growingMap ε hε h hne hb m g k (r u f))
      atTop (𝓝 (KFCausalClosedGraphForm.energyOutput D (T f))) :=
  ((KFCausalClosedGraphForm.energyOutput D).continuous.tendsto (T f)).comp
    (form_strong_limit ε hε h hne hb m g k f)

theorem static_penalty_limit (f : Hilbert) :
    Tendsto (fun u => (1/u)*‖A (r u f)‖^2) atTop (𝓝 0) :=
  KFCausalPenaltyVariationalLimit.penalty_limit I A (inclusion_dense ε hε h hne hb m g k)
    (T f) (fun u => r u f) (fun u hu => variational ε hε h hne hb m g k u hu f)

#print axioms comparison_budget
#print axioms total_error_limit
#print axioms form_strong_limit
#print axioms physical_strong_limit
#print axioms growing_output_strong_limit
#print axioms static_penalty_limit
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingResolventLimit
