/- Paired squeezes act on the full completed unaveraged and charge-averaged
energy forms. All output and domain identities follow from graph closure. -/
import UnifiedTheory.Audit.KFCausalClockFloorSqueezeEnergy
import UnifiedTheory.Audit.KFCausalChargeSqueezeJointFlow
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
import UnifiedTheory.Audit.KFCausalAveragedFormAction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueeze
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport (transport transport_reverse)
open UnifiedTheory.Audit.KFCausalChargeSqueezeJointFlow (physical_charge)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEnergy
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClosedGraphForm (FormSpace embedding energyOutput energyGraph)
open UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian (formData)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def ambientAction (r : ℝ) :
    WithLp 2 (Hilbert × Output (Fin 8) Hilbert) →L[ℂ]
      WithLp 2 (Hilbert × Output (Fin 8) Hilbert) :=
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert (Output (Fin 8) Hilbert)
  e.symm.toContinuousLinearMap.comp
    (((transport r : Hilbert →L[ℂ] Hilbert).prodMap (outputAction r)).comp e.toContinuousLinearMap)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hb : |h| ≤ Real.pi*ε)
  (m q k t r : ℝ)
local notation "D" => formData ε hε h hb m q k t

theorem ambient_mem (u : FormSpace D) : ambientAction r u.val ∈ energyGraph D :=
  closed_energy_graph ε hε h r hb m q k t
    (embedding D u) (energyOutput D u) u.property

def unaveragedAction : FormSpace D →L[ℂ] FormSpace D where
  toFun u := ⟨ambientAction r u.val,ambient_mem ε hε h hb m q k t r u⟩
  map_add' u v := by
    apply Subtype.ext
    exact (ambientAction r).map_add u.val v.val
  map_smul' c u := by
    apply Subtype.ext
    exact (ambientAction r).map_smul c u.val
  cont := ((ambientAction r).continuous.comp continuous_subtype_val).subtype_mk _

theorem unaveraged_embedding (u : FormSpace D) :
    embedding D (unaveragedAction ε hε h hb m q k t r u) = transport r (embedding D u) := rfl

theorem unaveraged_output (u : FormSpace D) :
    energyOutput D (unaveragedAction ε hε h hb m q k t r u) =
      outputAction r (energyOutput D u) := rfl

open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy (AveragedSpace)
local notation "V" => AveragedSpace ε hε h hb hne m q k t
local notation "J" => KFCausalClockFloorAveragedEnergy.embedding ε hε h hb hne m q k t
local notation "A" => KFCausalClockFloorAveragedEnergy.energyOutput ε hε h hb hne m q k t
local notation "T" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h hb hne m q k t

def averagedAction : V →L[ℂ] V := by
  let F : FormSpace D →L[ℂ] FormSpace D := unaveragedAction ε hε h hb m q k t r
  let emb : FormSpace D →L[ℂ] Hilbert := embedding D
  let B : Hilbert →L[ℂ] Hilbert := transport r
  have hf : ∀ v, emb (F v) = B (emb v) := unaveraged_embedding ε hε h hb m q k t r
  have hc : ∀ (θ : ℝ) (f : Hilbert), transport r ((KFCausalPhysicalCircleAction.group h hne).action θ f) =
      (KFCausalPhysicalCircleAction.group h hne).action θ (transport r f) := physical_charge r h hne
  let L := KFCausalAveragedFormAction.formAction (H := Hilbert) (E := FormSpace D)
    (KFCausalPhysicalCircleAction.group h hne) (2*Real.pi)
    emb B F hf hc
  exact L

theorem averaged_embedding (u : V) : J (averagedAction ε hε h hne hb m q k t r u) =
    transport r (J u) := rfl

theorem averaged_output (u : V) : A (averagedAction ε hε h hne hb m q k t r u) =
    (outputAction r).compLp (A u) := by
  let v := KFCausalClockFloorAveragedEnergy.sectionMap ε hε h hb hne m q k t u
  let F := unaveragedAction ε hε h hb m q k t r
  change (energyOutput D).compLp (F.compLp v) = (outputAction r).compLp ((energyOutput D).compLp v)
  apply Lp.ext
  filter_upwards [(energyOutput D).coeFn_compLp (F.compLp v),F.coeFn_compLp v,
    (outputAction r).coeFn_compLp ((energyOutput D).compLp v),(energyOutput D).coeFn_compLp v]
    with θ h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  exact unaveraged_output ε hε h hb m q k t r _

theorem averaged_domain (f : Hilbert) : transport r f ∈ (T).domain ↔ f ∈ (T).domain := by
  have forward (p : ℝ) (x : Hilbert) (hx : x ∈ (T).domain) : transport p x ∈ (T).domain := by
    obtain ⟨u,rfl⟩ := (KFCausalClockFloorAveragedEnergy.energy_domain ε hε h hb hne m q k t x).mp hx
    exact (KFCausalClockFloorAveragedEnergy.energy_domain ε hε h hb hne m q k t _).mpr
      ⟨averagedAction ε hε h hne hb m q k t p u,rfl⟩
  constructor
  · intro hf
    simpa only [transport_reverse] using forward (-r) _ hf
  · exact forward r f

theorem averaged_graph (f : Hilbert)
    (g : Lp (Output (Fin 8) Hilbert) 2 angleMeasure)
    (hfg : (f,g) ∈ (T).graph) :
    (transport r f,(outputAction r).compLp g) ∈ (T).graph := by
  have hg := KFCausalAveragedEnergyGraph.averagedOperator_graph
    (H := Hilbert) (E := FormSpace D) (K := Output (Fin 8) Hilbert)
    (KFCausalPhysicalCircleAction.group h hne) (2*Real.pi) (embedding D) (energyOutput D)
    (KFCausalClosedGraphForm.embedding_injective D)
  rw [hg] at hfg ⊢
  obtain ⟨u,hu⟩ := hfg
  refine ⟨averagedAction ε hε h hne hb m q k t r u,?_⟩
  apply Prod.ext
  · exact (averaged_embedding ε hε h hne hb m q k t r u).trans
      (congrArg (transport r) (congrArg Prod.fst hu))
  · exact (averaged_output ε hε h hne hb m q k t r u).trans
      (congrArg (fun y => (outputAction r).compLp y) (congrArg Prod.snd hu))

#print axioms ambient_mem
#print axioms unaveraged_embedding
#print axioms unaveraged_output
#print axioms averaged_embedding
#print axioms averaged_output
#print axioms averaged_domain
#print axioms averaged_graph
end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueeze
