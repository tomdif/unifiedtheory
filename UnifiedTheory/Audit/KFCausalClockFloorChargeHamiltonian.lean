/- Every physical charge rotation preserves the completed averaged form
and reduces its actual self-adjoint Hamiltonian. This proves domain
invariance as well as commutation of values. -/
import UnifiedTheory.Audit.KFCausalAveragedFormRotation
import UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorChargeHamiltonian
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction
open UnifiedTheory.Audit.KFCausalAngleTranslation
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (orbit)

private theorem period_mul_div (θ : ℝ) : (2*Real.pi)*(θ/(2*Real.pi)) = θ :=
  mul_div_cancel₀ θ (mul_ne_zero (two_ne_zero : (2:ℝ) ≠ 0) Real.pi_ne_zero)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
local notation "hp" => hamiltonian_bound ε h hb
local notation "D" => formData ε hε h hh hb m g k t
local notation "Base" => KFCausalClockFloorFormHamiltonian.formData ε hε h hp m g k t
local notation "BaseSpace" => KFCausalClosedGraphForm.FormSpace Base
local notation "Target" => Output (Fin 8) Hilbert
local notation "V" => AveragedSpace ε hε h hp hh m g k t
local notation "J" => embedding ε hε h hp hh m g k t
local notation "A" => energyOutput ε hε h hp hh m g k t
local notation "𝓗" => hamiltonian ε hε h hh hb m g k t

abbrev rotatedForm (θ : ℝ) (u : V) := by
  let R := KFCausalAveragedFormRotation.graphRotate (group h hh) (2*Real.pi)
    (action_full_period h hh) Base
  exact R (θ/(2*Real.pi)) u

theorem rotated_embedding (θ : ℝ) (u : V) :
    J (rotatedForm ε hε h hh hb m g k t θ u) = action h hh θ (J u) := by
  have hr := KFCausalAveragedFormRotation.graphRotate_embedding (group h hh) (2*Real.pi)
    (action_full_period h hh) Base
  have he := hr (θ/(2*Real.pi)) u
  have ht := period_mul_div θ
  exact he.trans (congrArg (fun a => action h hh a (J u)) ht)

#print axioms rotated_embedding

theorem rotated_output (θ : ℝ) (u : V) :
    A (rotatedForm ε hε h hh hb m g k t θ u) = pullback (θ/(2*Real.pi)) (A u) := by
  have hr := KFCausalAveragedFormRotation.graphRotate_output (group h hh) (2*Real.pi)
    (action_full_period h hh) Base
  exact hr (θ/(2*Real.pi)) u

#print axioms rotated_output

theorem rotated_energy_pairing (θ : ℝ) (u v : V) :
    inner ℂ (A (rotatedForm ε hε h hh hb m g k t θ u))
      (A (rotatedForm ε hε h hh hb m g k t θ v)) = inner ℂ (A u) (A v) := by
  have hr := KFCausalAveragedFormRotation.graphRotate_pairing (group h hh) (2*Real.pi)
    (action_full_period h hh) Base
  exact hr (θ/(2*Real.pi)) u v

#print axioms rotated_energy_pairing

theorem rotated_energy_transport (θ : ℝ) (u v : V) :
    inner ℂ (A (rotatedForm ε hε h hh hb m g k t θ u)) (A v) =
      inner ℂ (A u) (A (rotatedForm ε hε h hh hb m g k t (-θ) v)) := by
  have hr := KFCausalAveragedFormRotation.graphRotate_transport (group h hh) (2*Real.pi)
    (action_full_period h hh) Base
  have he := hr (θ/(2*Real.pi)) u v
  let R := KFCausalAveragedFormRotation.graphRotate (group h hh) (2*Real.pi)
    (action_full_period h hh) Base
  exact he.trans (congrArg (fun a : ℝ => inner ℂ (A u) (A (R a v)))
    (neg_div (2*Real.pi) θ).symm)

#print axioms rotated_energy_transport

theorem action_hamiltonian_graph (θ : ℝ) (x : (𝓗).domain) :
    (action h hh θ (x:Hilbert), action h hh θ (𝓗 x)) ∈ (𝓗).graph := by
  have hs := graphFormVector_surjective ε hε h hh hb m g k t (KFCausalClosedGraphForm.formLift D x)
  let u := hs.choose
  have hu := hs.choose_spec
  have he : J u = (x:Hilbert) :=
    (congrArg (KFCausalClosedGraphForm.embedding D) hu).trans
      (KFCausalClosedGraphForm.embedding_formLift D x)
  have hp' (v : V) :
      inner ℂ (A (rotatedForm ε hε h hh hb m g k t θ u)) (A v) =
        inner ℂ (action h hh θ (𝓗 x)) (J v) := by
    have hv := hamiltonian_represents_averaged_form ε hε h hh hb m g k t x
      (rotatedForm ε hε h hh hb m g k t (-θ) v)
    have hpair := congrArg (fun z : KFCausalClosedGraphForm.FormSpace D =>
      inner ℂ (KFCausalClosedGraphForm.energyOutput D z)
        (A (rotatedForm ε hε h hh hb m g k t (-θ) v))) hu
    calc
      _ = inner ℂ (A u) (A (rotatedForm ε hε h hh hb m g k t (-θ) v)) :=
        rotated_energy_transport ε hε h hh hb m g k t θ u v
      _ = inner ℂ (𝓗 x) (J (rotatedForm ε hε h hh hb m g k t (-θ) v)) := hpair.trans hv
      _ = inner ℂ (𝓗 x) (action h hh (-θ) (J v)) :=
        congrArg (inner ℂ (𝓗 x)) (rotated_embedding ε hε h hh hb m g k t (-θ) v)
      _ = inner ℂ (action h hh θ (𝓗 x)) (J v) :=
        (KFCausalUnitaryWeakGenerator.inner_transport (group h hh) (J v) (𝓗 x) (-θ)).trans
          (congrArg (fun a : ℝ => inner ℂ (action h hh a (𝓗 x)) (J v)) (neg_neg θ))
  have hd := (hamiltonian_domain_characterization ε hε h hh hb m g k t
    (rotatedForm ε hε h hh hb m g k t θ u) (action h hh θ (𝓗 x))).mpr hp'
  exact (𝓗).mem_graph_iff'.mpr ⟨⟨_,hd.choose⟩, Prod.ext
    ((rotated_embedding ε hε h hh hb m g k t θ u).trans (congrArg (action h hh θ) he))
    hd.choose_spec⟩

theorem action_mem_hamiltonian_domain (θ : ℝ) (x : (𝓗).domain) :
    action h hh θ (x:Hilbert) ∈ (𝓗).domain :=
  LinearPMap.mem_domain_iff.mpr ⟨_, action_hamiltonian_graph ε hε h hh hb m g k t θ x⟩

theorem hamiltonian_action (θ : ℝ) (x : (𝓗).domain) :
    𝓗 ⟨action h hh θ (x:Hilbert), action_mem_hamiltonian_domain ε hε h hh hb m g k t θ x⟩ =
      action h hh θ (𝓗 x) :=
  (𝓗).mem_graph_snd_inj' ((𝓗).mem_graph _) (action_hamiltonian_graph ε hε h hh hb m g k t θ x) rfl

#print axioms action_hamiltonian_graph
#print axioms action_mem_hamiltonian_domain
#print axioms hamiltonian_action

end
end UnifiedTheory.Audit.KFCausalClockFloorChargeHamiltonian
