/- The paired squeeze on the graph presentation used by the actual physical
form evolution. It commutes with changing the reference time. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueeze
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorReferenceSqueeze
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (formData)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport (transport transport_reverse)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEnergy (outputAction)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)

def ambient (r : ℝ) : WithLp 2 (Hilbert × EnergyOutputSpace) →L[ℂ]
    WithLp 2 (Hilbert × EnergyOutputSpace) :=
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert EnergyOutputSpace
  e.symm.toContinuousLinearMap.comp
    (((transport r : Hilbert →L[ℂ] Hilbert).prodMap ((outputAction r).compLpL 2 _)).comp
      e.toContinuousLinearMap)

theorem transport_dual (r : ℝ) (f g : Hilbert) :
    inner ℂ (transport r f) g = inner ℂ f (transport (-r) g) := by
  have he := (transport r).inner_map_map f (transport (-r) g)
  have hi := transport_reverse (-r) g
  simp only [neg_neg] at hi
  rwa [hi] at he

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m q k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m q k
local notation "J" => embedding ε hε h hne hh m q k
local notation "A" => energyOutput ε hε h hne hh m q k
local notation "D" => formData ε hε h hne hh m q k
local notation "T" => formTransfer ε hε h hne hh m q k

theorem graph_squeeze (r t : ℝ) (u : V t) :
    ambient r u.val ∈ KFCausalClosedGraphForm.energyGraph (D t) :=
  KFCausalClockFloorAveragedSqueeze.averaged_graph ε hε h hne
    (hamiltonian_bound ε h hh) m q k t r (J t u) (A t u) u.property

def formAction (r t : ℝ) : V t →L[ℂ] V t where
  toFun u := ⟨ambient r u.val,graph_squeeze ε hε h hne hh m q k r t u⟩
  map_add' u v := by
    apply Subtype.ext
    exact (ambient r).map_add u.val v.val
  map_smul' c u := by
    apply Subtype.ext
    exact (ambient r).map_smul c u.val
  cont := ((ambient r).continuous.comp continuous_subtype_val).subtype_mk _

theorem formAction_embedding (r t : ℝ) (u : V t) :
    J t (formAction ε hε h hne hh m q k r t u) = transport r (J t u) := rfl

theorem formAction_output (r t : ℝ) (u : V t) :
    A t (formAction ε hε h hne hh m q k r t u) = (outputAction r).compLp (A t u) := rfl

theorem formAction_inverse (r t : ℝ) (u : V t) :
    formAction ε hε h hne hh m q k (-r) t (formAction ε hε h hne hh m q k r t u) = u := by
  apply embedding_injective ε hε h hne hh m q k t
  simp only [formAction_embedding,transport_reverse]

theorem formAction_transfer (r s t : ℝ) (u : V s) :
    T s t (formAction ε hε h hne hh m q k r s u) =
      formAction ε hε h hne hh m q k r t (T s t u) := by
  apply embedding_injective ε hε h hne hh m q k t
  simp only [transfer_embedding,formAction_embedding]

#print axioms transport_dual
#print axioms graph_squeeze
#print axioms formAction_embedding
#print axioms formAction_output
#print axioms formAction_inverse
#print axioms formAction_transfer
end
end UnifiedTheory.Audit.KFCausalClockFloorReferenceSqueeze
