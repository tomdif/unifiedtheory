/- The physical clock core and response on the completed form space used
by the actual propagator, at each physical time. -/
import UnifiedTheory.Audit.KFCausalClosedGraphDiagonalAction
import UnifiedTheory.Audit.KFCausalClockFloorAveragedClockResponse
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorReferenceClockCore
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (formData)
open UnifiedTheory.Audit.KFCausalClockFloorClockOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalClockFloorAveragedResponseDecay
open UnifiedTheory.Audit.KFCausalClockFloorClockOutputForm
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalInvariantRangeCore (residual)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
local notation "𝒟" => formData ε hε h hne hh m g k t
local notation "𝒲" => FormSpace ε hε h hne hh m g k t
local notation "J" => embedding ε hε h hne hh m g k t
local notation "A" => energyOutput ε hε h hne hh m g k t
local notation "D" => defectOperator ε hε
local notation "L" => ContinuousLinearMap.compLpL 2 angleMeasure (outputAction ε hε h hh)

def formDefect : 𝒲 →L[ℂ] 𝒲 :=
  KFCausalClosedGraphDiagonalAction.action 𝒟 D L
    (KFCausalClockFloorAveragedClockCore.energy_graph_defect ε hε h hne hh m g k t)

local notation "F" => formDefect ε hε h hne hh m g k t

theorem defect_embedding (u : 𝒲) : J (F u) = D (J u) := rfl

theorem defect_output (u : 𝒲) : A (F u) = L (A u) := rfl

theorem residual_norm (u : 𝒲) : ‖residual F u‖ ≤ ‖u‖ :=
  KFCausalEmbeddedResponseDecay.residual_norm J A F D L 1 zero_le_one
    (defect_embedding ε hε h hne hh m g k t) (defect_output ε hε h hne hh m g k t)
    (fun v => by simpa only [one_mul] using form_norm_identity ε hε h hne hh m g k t v)
    (KFCausalClockFloorMomentumResponse.responseOperator_norm ε hε)
    (outputLp_residual_norm ε hε h hh) u

theorem residual_decay (u : 𝒲) :
    Tendsto (fun n : ℕ => (residual F : 𝒲 → 𝒲)^[n] u) atTop (𝓝 0) :=
  KFCausalEmbeddedResponseDecay.residual_decay J A F D L 1
    (defect_embedding ε hε h hne hh m g k t) (defect_output ε hε h hne hh m g k t)
    (fun v => by simpa only [one_mul] using form_norm_identity ε hε h hne hh m g k t v)
    (KFCausalClockFloorDefectPowerDecay.real_response_decay ε hε)
    (outputLp_residual_decay ε hε h hh) u

theorem defect_dense : DenseRange F :=
  KFCausalEmbeddedClockCore.range_dense F (residual_decay ε hε h hne hh m g k t)

theorem core_iff (u : 𝒲) : u ∈ Set.range F ↔ ∃ uc : 𝒲, (J u,J uc) ∈ (clockOperator ε hε).graph :=
  KFCausalEmbeddedClockCore.clock_range_iff J F D (clockOperator ε hε) (ε:ℂ)
    (Complex.ofReal_ne_zero.mpr hε.ne') (embedding_injective ε hε h hne hh m g k t)
    (defect_embedding ε hε h hne hh m g k t) (clock_defect_graph ε hε) (defect_clock ε hε) u

theorem clock_output_graphs (u uc : 𝒲) (hc : (J u,J uc) ∈ (clockOperator ε hε).graph) :
    ∀ᵐ θ ∂angleMeasure, ∀ i,
      (A u θ i,(A uc+deltaLp ε hε h hh (A u)) θ i) ∈ (clockOperator ε hε).graph :=
  KFCausalClockFloorAveragedClockResponse.output_graph_transfer J A F D L
    (deltaLp ε hε h hh) (clockOperator ε hε) (ε:ℂ)
    (embedding_injective ε hε h hne hh m g k t)
    (defect_embedding ε hε h hne hh m g k t) (defect_output ε hε h hne hh m g k t)
    (clock_defect_graph ε hε)
    (fun x y => ∀ᵐ θ ∂angleMeasure, ∀ i, (x θ i,y θ i) ∈ (clockOperator ε hε).graph)
    (output_clock_graphs ε hε h hh) u uc ((core_iff ε hε h hne hh m g k t u).mpr ⟨uc,hc⟩) hc

def clockResponse (u v : 𝒲) : ℂ := response ε hε h hh (A u) (A v)

theorem clockResponse_norm (u v : 𝒲) : ‖clockResponse ε hε h hne hh m g k t u v‖ ≤
    2*|h| * ‖A u‖*‖A v‖ := response_norm ε hε h hh (A u) (A v)

theorem clockResponse_continuous :
    Continuous (fun z : 𝒲 × 𝒲 => clockResponse ε hε h hne hh m g k t z.1 z.2) :=
  KFCausalClockFloorAveragedClockResponse.pullback_continuous A (response ε hε h hh)
    (response_continuous ε hε h hh)

theorem core_agreement (u uc v vc : 𝒲)
    (hu : (J u,J uc) ∈ (clockOperator ε hε).graph)
    (hv : (J v,J vc) ∈ (clockOperator ε hε).graph) :
    inner ℂ (A u) (A vc)-inner ℂ (A uc) (A v) = clockResponse ε hε h hne hh m g k t u v :=
  response_identity ε hε h hh (A u) (A uc) (A v) (A vc)
    (clock_output_graphs ε hε h hne hh m g k t u uc hu)
    (clock_output_graphs ε hε h hne hh m g k t v vc hv)

#print axioms defect_embedding
#print axioms defect_output
#print axioms residual_norm
#print axioms residual_decay
#print axioms defect_dense
#print axioms core_iff
#print axioms clock_output_graphs
#print axioms clockResponse_norm
#print axioms clockResponse_continuous
#print axioms core_agreement
end
end UnifiedTheory.Audit.KFCausalClockFloorReferenceClockCore
