/- A continuous clock-response form on the entire actual charge-averaged
form space, agreeing with the physical clock on its proved form core. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedClockCore
import UnifiedTheory.Audit.KFCausalClockFloorClockOutputForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedClockResponse
noncomputable section
open MeasureTheory
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormDefect
open UnifiedTheory.Audit.KFCausalClockFloorAveragedClockCore
open UnifiedTheory.Audit.KFCausalClockFloorClockOutputForm
open UnifiedTheory.Audit.KFCausalClockFloorClockOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction

/-- Transfer an output graph relation without assuming the desired clock composition. -/
theorem output_graph_transfer {V H Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (J : V →L[ℂ] H) (A : V →L[ℂ] Z) (F : V →L[ℂ] V) (D : H →L[ℂ] H)
    (R Q : Z →L[ℂ] Z) (C : H →ₗ.[ℂ] H) (c : ℂ)
    (hJ : Function.Injective J) (hF : ∀ u, J (F u) = D (J u))
    (hA : ∀ u, A (F u) = R (A u)) (hCD : ∀ f, (D f,c • f) ∈ C.graph)
    (S : Z → Z → Prop) (hS : ∀ w, S (R w) (c • w+Q (R w)))
    (u uc : V) (hu : u ∈ Set.range F) (hc : (J u,J uc) ∈ C.graph) :
    S (A u) (A uc+Q (A u)) := by
  rcases hu with ⟨w,rfl⟩
  have he : J uc = c • J w := C.mem_graph_snd_inj' hc (hCD (J w)) (hF w)
  have ec : uc = c • w := hJ (he.trans (map_smul J c w).symm)
  simpa only [ec,map_smul,hA] using hS (A w)

theorem pullback_continuous {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z] (A : V →L[ℂ] Z) (b : Z → Z → ℂ)
    (hb : Continuous (fun z : Z × Z => b z.1 z.2)) :
    Continuous (fun z : V × V => b (A z.1) (A z.2)) :=
  hb.comp (A.prodMap A).continuous

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
local notation "hb" => KFCausalClockFloorClosedEnergyDefect.energy_bound ε hε h hh
local notation "𝒱" => AveragedSpace ε hε h hb hne mass2 quartic vacuum t
local notation "J" => embedding ε hε h hb hne mass2 quartic vacuum t
local notation "A" => energyOutput ε hε h hb hne mass2 quartic vacuum t
local notation "F" => formAction ε hε h hne hh mass2 quartic vacuum t
local notation "R" => outputAction ε hε h hh
local notation "Y" => Lp (Output (Fin 8) Hilbert) 2 angleMeasure

theorem clock_output_graphs (u uc : 𝒱) (hc : (J u,J uc) ∈ (clockOperator ε hε).graph) :
    ∀ᵐ θ ∂angleMeasure, ∀ i,
      (A u θ i,(A uc+deltaLp ε hε h hh (A u)) θ i) ∈ (clockOperator ε hε).graph :=
  output_graph_transfer J A F (defectOperator ε hε) ((R).compLpL 2 angleMeasure)
    (deltaLp ε hε h hh) (clockOperator ε hε) (ε:ℂ)
    (embedding_injective ε hε h hb hne mass2 quartic vacuum t)
    (formAction_embedding ε hε h hne hh mass2 quartic vacuum t)
    (formAction_output ε hε h hne hh mass2 quartic vacuum t) (clock_defect_graph ε hε)
    (fun g k : Y => ∀ᵐ θ ∂angleMeasure, ∀ i, (g θ i,k θ i) ∈ (clockOperator ε hε).graph)
    (output_clock_graphs ε hε h hh) u uc
    ((formCore_iff ε hε h hne hh mass2 quartic vacuum t u).mpr ⟨uc,hc⟩) hc

def formResponse (u v : 𝒱) : ℂ := response ε hε h hh (A u) (A v)

theorem formResponse_norm (u v : 𝒱) :
    ‖formResponse ε hε h hne hh mass2 quartic vacuum t u v‖ ≤ 2*|h| * ‖A u‖*‖A v‖ :=
  response_norm ε hε h hh (A u) (A v)

set_option maxHeartbeats 4000000 in
theorem formResponse_continuous :
    Continuous (fun z : 𝒱 × 𝒱 => formResponse ε hε h hne hh mass2 quartic vacuum t z.1 z.2) :=
  pullback_continuous A (response ε hε h hh) (response_continuous ε hε h hh)

theorem core_agreement (u uc v vc : 𝒱)
    (hu : (J u,J uc) ∈ (clockOperator ε hε).graph)
    (hv : (J v,J vc) ∈ (clockOperator ε hε).graph) :
    inner ℂ (A u) (A vc)-inner ℂ (A uc) (A v) =
      formResponse ε hε h hne hh mass2 quartic vacuum t u v :=
  response_identity ε hε h hh (A u) (A uc) (A v) (A vc)
    (clock_output_graphs ε hε h hne hh mass2 quartic vacuum t u uc hu)
    (clock_output_graphs ε hε h hne hh mass2 quartic vacuum t v vc hv)

/-- Matching actual clock pairings on the core fixes the extension everywhere. -/
theorem extension_unique (b : 𝒱 × 𝒱 → ℂ) (hbcont : Continuous b)
    (hbcore : ∀ u uc v vc : 𝒱, (J u,J uc) ∈ (clockOperator ε hε).graph →
      (J v,J vc) ∈ (clockOperator ε hε).graph →
        b (u,v) = inner ℂ (A u) (A vc)-inner ℂ (A uc) (A v)) :
    b = fun z => formResponse ε hε h hne hh mass2 quartic vacuum t z.1 z.2 := by
  apply Continuous.ext_on
    ((formCore_dense ε hε h hne hh mass2 quartic vacuum t).prod
      (formCore_dense ε hε h hne hh mass2 quartic vacuum t)) hbcont
    (formResponse_continuous ε hε h hne hh mass2 quartic vacuum t)
  rintro ⟨u,v⟩ ⟨hu,hv⟩
  have huc_exists := (formCore_iff ε hε h hne hh mass2 quartic vacuum t u).mp hu
  rcases huc_exists with ⟨uc,huc⟩
  have hvc_exists := (formCore_iff ε hε h hne hh mass2 quartic vacuum t v).mp hv
  rcases hvc_exists with ⟨vc,hvc⟩
  exact (hbcore u uc v vc huc hvc).trans (core_agreement ε hε h hne hh mass2 quartic vacuum t u uc v vc huc hvc)

#print axioms pullback_continuous
#print axioms output_graph_transfer
#print axioms clock_output_graphs
#print axioms formResponse_norm
#print axioms formResponse_continuous
#print axioms core_agreement
#print axioms extension_unique
end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedClockResponse
