/- Exact fixed-time operator-domain correspondence for the actual averaged
Hamiltonian. The right-hand side is an explicit variational condition on the
completed time-zero form, with weights [1,exp t,...,exp t,1,exp (2*t)].
It contains neither a conjugated Hamiltonian nor an assumed spectral basis.
This is not a Hermite/direct-integral spectral theorem. -/
import UnifiedTheory.Audit.KFCausalClockFloorBalancedSqueeze
import UnifiedTheory.Audit.KFCausalClosedFormUnitaryGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorBalancedHamiltonian
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorReferenceSqueeze (formAction formAction_embedding
  formAction_output formAction_inverse)
open KFCausalClockFloorBalancedSqueeze (balancedPairing balanced_output_pairing)
open KFCausalClockFloorSqueezeMovingPairing (outputLp_pairing)
open KFCausalClockFloorAveragedHamiltonian (formData hamiltonian)
open KFCausalPairedSqueezeTransport (transport transport_reverse)
open KFCausalStandingChargeOperator (zeroSector standingCharge standingCharge_zero_iff)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m q k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m q k
local notation "J" => embedding ε hε h hne hb m q k
local notation "A" => energyOutput ε hε h hne hb m q k
local notation "D" => formData ε hε h hne hb m q k
local notation "H" => hamiltonian ε hε h hne hb m q k
local notation "T" => formTransfer ε hε h hne hb m q k
local notation "R" => formAction ε hε h hne hb m q k

def frame (t : ℝ) : V 0 →L[ℂ] V t :=
  (R ((-1/2)*t) t).comp (T 0 t)

theorem frame_embedding (t : ℝ) (u : V 0) :
    J t (frame ε hε h hne hb m q k t u) = transport ((-1/2)*t) (J 0 u) := by
  change J t (R ((-1/2)*t) t (T 0 t u)) = _
  rw [formAction_embedding,transfer_embedding]

theorem frame_surjective (t : ℝ) :
    Function.Surjective (frame ε hε h hne hb m q k t) := by
  intro w
  refine ⟨T t 0 (R (-((-1/2)*t)) t w), ?_⟩
  change R ((-1/2)*t) t (T 0 t (T t 0 (R (-((-1/2)*t)) t w))) = w
  rw [transfer_inverse]
  simpa only [neg_neg] using
    formAction_inverse ε hε h hne hb m q k (-((-1/2)*t)) t w

theorem frame_pairing (t : ℝ) (u v : V 0) :
    inner ℂ (A t (frame ε hε h hne hb m q k t u))
      (A t (frame ε hε h hne hb m q k t v)) =
        balancedPairing t (A 0 u) (A 0 v) := by
  have output (w : V 0) : A t (frame ε hε h hne hb m q k t w) =
      KFCausalClockFloorAveragedSqueezeEnergy.outputLp ((-1/2)*t)
        (KFCausalClockFloorAveragedOutputTransport.timeOutputLp 0 t (A 0 w)) :=
    (formAction_output ε hε h hne hb m q k ((-1/2)*t) t (T 0 t w)).trans
      (congrArg ((KFCausalClockFloorSqueezeEnergy.outputAction ((-1/2)*t)).compLp)
        (transfer_energyOutput ε hε h hne hb m q k 0 t w))
  exact (congrArg₂ (inner ℂ) (output u) (output v)).trans
    ((outputLp_pairing ((-1/2)*t) _ _).trans
      (balanced_output_pairing t (A 0 u) (A 0 v)))

/-- An explicit reference-form graph condition, defined without `H` or `transport`. -/
def BalancedGraph (t : ℝ) (f g : Hilbert) : Prop :=
  ∃ u : V 0, J 0 u = f ∧
    ∀ v : V 0, balancedPairing t (A 0 u) (A 0 v) = inner ℂ g (J 0 v)

/-- Both directions hold on the full closed operator graph, not only on test vectors. -/
theorem hamiltonian_graph_iff (t : ℝ) (f g : Hilbert) :
    (transport ((-1/2)*t) f,transport ((-1/2)*t) g) ∈ (H t).graph ↔
      BalancedGraph ε hε h hne hb m q k t f g :=
  KFCausalClosedFormUnitaryGraph.graph_iff (D t) (transport ((-1/2)*t)) (J 0)
    (frame ε hε h hne hb m q k t) (frame_surjective ε hε h hne hb m q k t)
    (frame_embedding ε hε h hne hb m q k t)
    (fun u v => balancedPairing t (A 0 u) (A 0 v))
    (frame_pairing ε hε h hne hb m q k t) f g

theorem hamiltonian_domain_iff (t : ℝ) (f : Hilbert) :
    transport ((-1/2)*t) f ∈ (H t).domain ↔
      ∃ g : Hilbert, BalancedGraph ε hε h hne hb m q k t f g := by
  constructor
  · intro hf
    let y := H t ⟨transport ((-1/2)*t) f,hf⟩
    refine ⟨transport (-((-1/2)*t)) y, (hamiltonian_graph_iff ε hε h hne hb m q k t f _).mp ?_⟩
    have hi : transport ((-1/2)*t) (transport (-((-1/2)*t)) y) = y := by
      simpa only [neg_neg] using transport_reverse (-((-1/2)*t)) y
    rw [hi]
    exact (H t).mem_graph ⟨transport ((-1/2)*t) f,hf⟩
  · rintro ⟨g,hg⟩
    exact LinearPMap.mem_domain_of_mem_graph
      ((hamiltonian_graph_iff ε hε h hne hb m q k t f g).mpr hg)

theorem balancedGraph_unique (t : ℝ) (f g₁ g₂ : Hilbert)
    (h₁ : BalancedGraph ε hε h hne hb m q k t f g₁)
    (h₂ : BalancedGraph ε hε h hne hb m q k t f g₂) : g₁ = g₂ := by
  apply (transport ((-1/2)*t)).injective
  exact (H t).mem_graph_snd_inj'
    ((hamiltonian_graph_iff ε hε h hne hb m q k t f g₁).mpr h₁)
    ((hamiltonian_graph_iff ε hε h hne hb m q k t f g₂).mpr h₂) rfl

omit ε hε hb m q k in
theorem transport_zeroSector_iff (a : ℝ) (f : Hilbert) :
    transport a f ∈ zeroSector h hne ↔ f ∈ zeroSector h hne := by
  have forward (r : ℝ) (v : Hilbert) (hv : v ∈ zeroSector h hne) :
      transport r v ∈ zeroSector h hne := by
    intro θ
    change KFCausalPhysicalCircleAction.action h hne θ (transport r v) = transport r v
    exact (KFCausalChargeSqueezeJointFlow.physical_charge r h hne θ v).symm.trans
      (congrArg (transport r) (hv θ))
  constructor
  · intro hf
    have hr := forward (-a) (transport a f) hf
    rwa [transport_reverse] at hr
  · exact forward a f

omit ε hε hb m q k in
theorem transport_constraint_kernel_iff (a : ℝ) (f : Hilbert) :
    (transport a f,0) ∈ (standingCharge h hne).graph ↔
      (f,0) ∈ (standingCharge h hne).graph := by
  rw [standingCharge_zero_iff,standingCharge_zero_iff,transport_zeroSector_iff]

#print axioms frame_embedding
#print axioms frame_surjective
#print axioms frame_pairing
#print axioms hamiltonian_graph_iff
#print axioms hamiltonian_domain_iff
#print axioms balancedGraph_unique
#print axioms transport_zeroSector_iff
#print axioms transport_constraint_kernel_iff
end
end UnifiedTheory.Audit.KFCausalClockFloorBalancedHamiltonian
