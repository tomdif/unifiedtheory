/- Nonnegative charge-averaged actual weak vacuum momentum response on
the coherent span. All commutator compositions exist. This is not yet an
Ehrenfest identity along the full time-dependent Hamiltonian evolution. -/
import UnifiedTheory.Audit.KFCausalCoherentVacuumCommutator
import UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalCoherentVacuumWeakForce
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan action_coherentSpan)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalCoherentVacuumCommutator

def weakResponse (h : ℝ) (g tb : ℝ → Hilbert) (θ : ℝ) : ℝ := (-2/h)*(inner ℂ (g θ) (tb θ)).im

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "T" => orderedExponential ε hε h
local notation "B" => pureMomentum ε hε h
local notation "J" => shearMomentum h
local notation "R" => KFCausalClockFloorPureClockVacuumResponse.response ε hε h hb
local notation "L" => KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb

include hb in
theorem actual_outputs_continuous (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g j : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph ∧ (g θ,j θ) ∈ (J).graph) :
    Continuous g ∧ Continuous j := by
  obtain ⟨u,v,hu,hv,hgraph,_,_⟩ :=
    KFCausalCoherentSpanVacuumSign.exists_nonnegative_actual_response ε a h hε ha hh hb f hf
  obtain ⟨rfl,rfl⟩ := KFCausalContinuousShearOrbitDomain.orbit_outputs_unique ε h hε hh f u v g j hgraph hg
  exact ⟨hu,hv⟩

theorem weak_response_identity (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g j b tb : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph ∧ (g θ,j θ) ∈ (J).graph)
    (hB : ∀ θ, (action h hh (2*Real.pi*θ) f,b θ) ∈ (B).graph)
    (hT : ∀ θ, (b θ,tb θ) ∈ (T).graph) :
    weakResponse h g tb = fun θ => R (g θ) (j θ) := by
  funext θ
  exact span_weak_response ε a h hε ha hh hb _
    (action_coherentSpan ε a h hε ha hh (2*Real.pi*θ) f hf)
    (g θ) (j θ) (b θ) (tb θ) (hg θ).1 (hg θ).2 (hB θ) (hT θ)

include hb in
theorem weak_response_integrable (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g j b tb : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph ∧ (g θ,j θ) ∈ (J).graph)
    (hB : ∀ θ, (action h hh (2*Real.pi*θ) f,b θ) ∈ (B).graph)
    (hT : ∀ θ, (b θ,tb θ) ∈ (T).graph) :
    Integrable (weakResponse h g tb) angleMeasure := by
  obtain ⟨hc,hd⟩ := actual_outputs_continuous ε a h hε ha hh hb f hf g j hg
  rw [weak_response_identity ε a h hε ha hh hb f hf g j b tb hg hB hT]
  exact KFCausalAveragedShearPairing.response_integrable ε h hε hh hb g j hc hd (fun θ => (hg θ).2)

theorem weak_response_lower_bound (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g j b tb : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph ∧ (g θ,j θ) ∈ (J).graph)
    (hB : ∀ θ, (action h hh (2*Real.pi*θ) f,b θ) ∈ (B).graph)
    (hT : ∀ θ, (b θ,tb θ) ∈ (T).graph) :
    0 ≤ (∫ θ, L (g θ) ∂angleMeasure) ∧
      (∫ θ, L (g θ) ∂angleMeasure) ≤ ∫ θ, weakResponse h g tb θ ∂angleMeasure := by
  rw [weak_response_identity ε a h hε ha hh hb f hf g j b tb hg hB hT]
  exact ⟨integral_nonneg (fun θ => (KFCausalClockFloorVacuumMomentumResponse.response_bounds ε hε h hb (g θ)).1),
    KFCausalCoherentSpanVacuumSign.vacuum_response_lower_bound ε a h hε ha hh hb f hf g j hg⟩

theorem exists_actual_weak_response (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) :
    ∃ g j b tb bg : ℝ → Hilbert, Continuous g ∧ Continuous j ∧
      (∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph ∧ (g θ,j θ) ∈ (J).graph ∧
        (action h hh (2*Real.pi*θ) f,b θ) ∈ (B).graph ∧ (b θ,tb θ) ∈ (T).graph ∧
        (g θ,bg θ) ∈ (B).graph) ∧
      weakResponse h g tb = (fun θ => R (g θ) (j θ)) ∧
      Integrable (weakResponse h g tb) angleMeasure ∧
      0 ≤ (∫ θ, L (g θ) ∂angleMeasure) ∧
      (∫ θ, L (g θ) ∂angleMeasure) ≤ ∫ θ, weakResponse h g tb θ ∂angleMeasure := by
  obtain ⟨g,j,hcg,hcj,hg,_,_⟩ :=
    KFCausalCoherentSpanVacuumSign.exists_nonnegative_actual_response ε a h hε ha hh hb f hf
  have hc (θ : ℝ) : ∃ b tb bg : Hilbert,
      (action h hh (2*Real.pi*θ) f,b) ∈ (B).graph ∧ (b,tb) ∈ (T).graph ∧ (g θ,bg) ∈ (B).graph := by
    obtain ⟨b,tb,bg,jg,hB,hT,hbg,_,_⟩ := span_compositions ε a h hε ha hh hb _
      (action_coherentSpan ε a h hε ha hh (2*Real.pi*θ) f hf) (g θ) (hg θ).1
    exact ⟨b,tb,bg,hB,hT,hbg⟩
  choose b tb bg hB hT hbg using hc
  exact ⟨g,j,b,tb,bg,hcg,hcj,fun θ => ⟨(hg θ).1,(hg θ).2,hB θ,hT θ,hbg θ⟩,
    weak_response_identity ε a h hε ha hh hb f hf g j b tb hg hB hT,
    weak_response_integrable ε a h hε ha hh hb f hf g j b tb hg hB hT,
    weak_response_lower_bound ε a h hε ha hh hb f hf g j b tb hg hB hT⟩

omit a ha hb in
theorem input_momentum_orbit (f b₀ : Hilbert) (hf : (f,b₀) ∈ (B).graph)
    (b : ℝ → Hilbert) (hB : ∀ θ, (action h hh (2*Real.pi*θ) f,b θ) ∈ (B).graph) :
    b = fun θ => action h hh (2*Real.pi*θ) b₀ := by
  funext θ
  exact (B).mem_graph_snd_inj' (hB θ)
    (KFCausalClockFloorPureClockChargeGraph.graph_charge ε hε h hh (2*Real.pi*θ) f b₀ hf) rfl

theorem exists_fixed_momentum_response (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) :
    ∃ (b₀ : Hilbert) (g j tb bg : ℝ → Hilbert), Continuous g ∧ Continuous j ∧ (f,b₀) ∈ (B).graph ∧
      (∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph ∧ (g θ,j θ) ∈ (J).graph ∧
        (action h hh (2*Real.pi*θ) b₀,tb θ) ∈ (T).graph ∧ (g θ,bg θ) ∈ (B).graph) ∧
      weakResponse h g tb = (fun θ => R (g θ) (j θ)) ∧
      Integrable (weakResponse h g tb) angleMeasure ∧
      0 ≤ (∫ θ, L (g θ) ∂angleMeasure) ∧
      (∫ θ, L (g θ) ∂angleMeasure) ≤ ∫ θ, weakResponse h g tb θ ∂angleMeasure := by
  obtain ⟨g,j,b,tb,bg,hcg,hcj,hgraph,he,hi,hL,hbound⟩ :=
    exists_actual_weak_response ε a h hε ha hh hb f hf
  have hd : f ∈ (B).domain := KFCausalClockFloorPureClockJointDomain.joint_domain ε hε h hh f
    (KFCausalCoherentLongitudinalDomain.coherentSpan_le_longitudinalDomain ε a h hε ha hh hf)
    (KFCausalCoherentShearDomain.coherentSpan_le_shearDomain ε a h hε ha hh hf)
  let b₀ := (B) ⟨f,hd⟩
  have hB₀ : (f,b₀) ∈ (B).graph := (B).mem_graph ⟨f,hd⟩
  have horbit := input_momentum_orbit ε h hε hh f b₀ hB₀ b (fun θ => (hgraph θ).2.2.1)
  refine ⟨b₀,g,j,tb,bg,hcg,hcj,hB₀,?_,he,hi,hL,hbound⟩
  intro θ
  refine ⟨(hgraph θ).1,(hgraph θ).2.1,?_,(hgraph θ).2.2.2.2⟩
  rw [← congrFun horbit θ]
  exact (hgraph θ).2.2.2.1

#print axioms actual_outputs_continuous
#print axioms weak_response_identity
#print axioms weak_response_integrable
#print axioms weak_response_lower_bound
#print axioms exists_actual_weak_response
#print axioms input_momentum_orbit
#print axioms exists_fixed_momentum_response
end
end UnifiedTheory.Audit.KFCausalCoherentVacuumWeakForce
