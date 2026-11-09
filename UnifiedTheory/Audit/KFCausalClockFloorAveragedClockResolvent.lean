/- Bounded physical clock approximants preserve the propagator form.
Their exact commutator pairings are the full clock response evaluated on
strongly approximating form states, with a cutoff-independent bound. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockResolvent
import UnifiedTheory.Audit.KFCausalClockFloorReferenceClockCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedClockResolvent
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalInvariantRangeCore (residual)
open UnifiedTheory.Audit.KFCausalContractiveResidualResolvent
open UnifiedTheory.Audit.KFCausalResidualResolventApproximation

/-- The two real mixed terms cancel exactly. -/
theorem pairing_smoothing {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A : V →L[ℂ] E) (F : V →L[ℂ] V)
    (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖) (c b : ℝ) (hb : 0 < b) (u v : V) :
    inner ℂ (A (smoothing F hF b hb u)) (A ((c:ℂ) • resolvent F hF b hb v))-
      inner ℂ (A ((c:ℂ) • resolvent F hF b hb u)) (A (smoothing F hF b hb v)) =
    inner ℂ (A u) (A ((c:ℂ) • resolvent F hF b hb v))-
      inner ℂ (A ((c:ℂ) • resolvent F hF b hb u)) (A v) := by
  simp only [smoothing,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply,map_sub,map_smul,inner_sub_left,inner_sub_right,
    inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  ring

open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorReferenceClockCore
open UnifiedTheory.Audit.KFCausalClockFloorClockResolvent
open UnifiedTheory.Audit.KFCausalClockFloorClockOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalClockFloorAveragedResponseDecay (outputLp_residual_norm)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "𝒲" => FormSpace ε hε h hne hh m g k
local notation "J" => embedding ε hε h hne hh m g k
local notation "A" => energyOutput ε hε h hne hh m g k
local notation "T" => formTransfer ε hε h hne hh m g k
local notation "F" => formDefect ε hε h hne hh m g k
local notation "hF" => residual_norm ε hε h hne hh m g k
local notation "D" => defectOperator ε hε
local notation "hD" => KFCausalClockFloorMomentumResponse.responseOperator_norm ε hε
local notation "L" => ContinuousLinearMap.compLpL 2 angleMeasure (outputAction ε hε h hh)
local notation "hL" => outputLp_residual_norm ε hε h hh

def formResolvent (t b : ℝ) (hb : 0 < b) : 𝒲 t →L[ℂ] 𝒲 t := resolvent (F t) (hF t) b hb

def formApprox (t b : ℝ) (hb : 0 < b) : 𝒲 t →L[ℂ] 𝒲 t := (ε:ℂ) • formResolvent ε hε h hne hh m g k t b hb

def formSmoothing (t b : ℝ) (hb : 0 < b) : 𝒲 t →L[ℂ] 𝒲 t := smoothing (F t) (hF t) b hb

theorem resolvent_embedding (t b : ℝ) (hb : 0 < b) (u : 𝒲 t) :
    J t (formResolvent ε hε h hne hh m g k t b hb u) = physicalResolvent ε hε b hb (J t u) :=
  intertwine (J t) (F t) D (hF t) hD (defect_embedding ε hε h hne hh m g k t) b hb u

theorem resolvent_output (t b : ℝ) (hb : 0 < b) (u : 𝒲 t) :
    A t (formResolvent ε hε h hne hh m g k t b hb u) = resolvent L hL b hb (A t u) :=
  intertwine (A t) (F t) L (hF t) hL (defect_output ε hε h hne hh m g k t) b hb u

theorem approx_embedding (t b : ℝ) (hb : 0 < b) (u : 𝒲 t) :
    J t (formApprox ε hε h hne hh m g k t b hb u) = clockApprox ε hε b hb (J t u) :=
  (map_smul (J t) (ε:ℂ) (formResolvent ε hε h hne hh m g k t b hb u)).trans
    (congrArg (fun z : Hilbert => (ε:ℂ) • z) (resolvent_embedding ε hε h hne hh m g k t b hb u))

theorem smoothing_embedding (t b : ℝ) (hb : 0 < b) (u : 𝒲 t) :
    J t (formSmoothing ε hε h hne hh m g k t b hb u) = clockSmoothing ε hε b hb (J t u) :=
  smoothing_intertwine (J t) (F t) D (hF t) hD (defect_embedding ε hε h hne hh m g k t) b hb u

theorem smoothing_output (t b : ℝ) (hb : 0 < b) (u : 𝒲 t) :
    A t (formSmoothing ε hε h hne hh m g k t b hb u) = smoothing L hL b hb (A t u) :=
  smoothing_intertwine (A t) (F t) L (hF t) hL (defect_output ε hε h hne hh m g k t) b hb u

theorem smoothing_energy_bound (t b : ℝ) (hb : 0 < b) (u : 𝒲 t) :
    ‖A t (formSmoothing ε hε h hne hh m g k t b hb u)‖ ≤ 2*‖A t u‖ :=
  (congrArg norm (smoothing_output ε hε h hne hh m g k t b hb u)).le.trans (smoothing_norm L hL b hb (A t u))

theorem smoothing_strong {ι : Type*} (t : ℝ) (b : ι → ℝ) (hb : ∀ i, 0 < b i) (l : Filter ι)
    (hz : Tendsto b l (𝓝 0)) (u : 𝒲 t) :
    Tendsto (fun i => formSmoothing ε hε h hne hh m g k t (b i) (hb i) u) l (𝓝 u) :=
  smoothing_tendsto (F t) (hF t) (defect_dense ε hε h hne hh m g k t) b hb l hz u

theorem approx_transfer (s t b : ℝ) (hb : 0 < b) (u : 𝒲 s) :
    formApprox ε hε h hne hh m g k t b hb (T s t u) = T s t (formApprox ε hε h hne hh m g k s b hb u) := by
  apply embedding_injective ε hε h hne hh m g k t
  exact (approx_embedding ε hε h hne hh m g k t b hb (T s t u)).trans
    ((congrArg (clockApprox ε hε b hb) (transfer_embedding ε hε h hne hh m g k s t u)).trans
      ((approx_embedding ε hε h hne hh m g k s b hb u).symm.trans
        (transfer_embedding ε hε h hne hh m g k s t _).symm))

theorem smoothing_transfer (s t b : ℝ) (hb : 0 < b) (u : 𝒲 s) :
    formSmoothing ε hε h hne hh m g k t b hb (T s t u) = T s t (formSmoothing ε hε h hne hh m g k s b hb u) := by
  apply embedding_injective ε hε h hne hh m g k t
  exact (smoothing_embedding ε hε h hne hh m g k t b hb (T s t u)).trans
    ((congrArg (clockSmoothing ε hε b hb) (transfer_embedding ε hε h hne hh m g k s t u)).trans
      ((smoothing_embedding ε hε h hne hh m g k s b hb u).symm.trans
        (transfer_embedding ε hε h hne hh m g k s t _).symm))

theorem clock_graph (t b : ℝ) (hb : 0 < b) (u : 𝒲 t) :
    (J t (formSmoothing ε hε h hne hh m g k t b hb u),
      J t (formApprox ε hε h hne hh m g k t b hb u)) ∈ (clockOperator ε hε).graph :=
  (congrArg (fun z => z ∈ (clockOperator ε hε).graph)
    (Prod.ext (smoothing_embedding ε hε h hne hh m g k t b hb u)
      (approx_embedding ε hε h hne hh m g k t b hb u))).mpr (clock_smoothing_graph ε hε b hb (J t u))

theorem regularized_pairing (t b : ℝ) (hb : 0 < b) (u v : 𝒲 t) :
    inner ℂ (A t u) (A t (formApprox ε hε h hne hh m g k t b hb v))-
      inner ℂ (A t (formApprox ε hε h hne hh m g k t b hb u)) (A t v) =
      clockResponse ε hε h hne hh m g k t
        (formSmoothing ε hε h hne hh m g k t b hb u) (formSmoothing ε hε h hne hh m g k t b hb v) :=
  (pairing_smoothing (A t) (F t) (hF t) ε b hb u v).symm.trans
    (core_agreement ε hε h hne hh m g k t _ _ _ _
      (clock_graph ε hε h hne hh m g k t b hb u) (clock_graph ε hε h hne hh m g k t b hb v))

theorem regularized_pairing_bound (t b : ℝ) (hb : 0 < b) (u v : 𝒲 t) :
    ‖inner ℂ (A t u) (A t (formApprox ε hε h hne hh m g k t b hb v))-
      inner ℂ (A t (formApprox ε hε h hne hh m g k t b hb u)) (A t v)‖ ≤ 8*|h| * ‖A t u‖*‖A t v‖ := by
  have he := regularized_pairing ε hε h hne hh m g k t b hb u v
  calc
    _ = ‖clockResponse ε hε h hne hh m g k t
      (formSmoothing ε hε h hne hh m g k t b hb u) (formSmoothing ε hε h hne hh m g k t b hb v)‖ := congrArg norm he
    _ ≤ 2*|h| * ‖A t (formSmoothing ε hε h hne hh m g k t b hb u)‖*
        ‖A t (formSmoothing ε hε h hne hh m g k t b hb v)‖ := clockResponse_norm ε hε h hne hh m g k t _ _
    _ ≤ 2*|h| * (2*‖A t u‖)*(2*‖A t v‖) := by
      gcongr <;> apply smoothing_energy_bound
    _ = _ := by ring

#print axioms pairing_smoothing
#print axioms resolvent_embedding
#print axioms resolvent_output
#print axioms approx_embedding
#print axioms smoothing_embedding
#print axioms smoothing_output
#print axioms smoothing_energy_bound
#print axioms smoothing_strong
#print axioms approx_transfer
#print axioms smoothing_transfer
#print axioms clock_graph
#print axioms regularized_pairing
#print axioms regularized_pairing_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedClockResolvent
