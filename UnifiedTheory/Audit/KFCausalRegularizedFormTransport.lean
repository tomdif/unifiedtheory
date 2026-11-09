/- Exact transport of the completed homogeneous energy form between times.
The input domain is independent of time; no operator-domain equality is
assumed. All statements remain valid when the coupling vanishes. -/
import UnifiedTheory.Audit.KFCausalGraphTransport
import UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalRegularizedFormTransport
noncomputable section
open UnifiedTheory.Audit.KFCausalGraphTransport
open UnifiedTheory.Audit.KFCausalRegularizedFormDomain
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedClosedForm
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding

def timeOutput (s t : ℝ) : Output →L[ℂ] Output :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert Hilbert).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.id ℂ Hilbert).prodMap
      ((Real.exp (t-s) : ℂ) • ContinuousLinearMap.id ℂ Hilbert)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert Hilbert).toContinuousLinearMap)

theorem timeOutput_apply (s t : ℝ) (y : Output) :
    timeOutput s t y = WithLp.toLp 2 ((WithLp.ofLp y).1,
      (Real.exp (t-s) : ℂ) • (WithLp.ofLp y).2) := rfl

theorem exp_transition (s t : ℝ) : Real.exp (t-s) * Real.exp s = Real.exp t := by
  rw [← Real.exp_add, sub_add_cancel]

theorem timeOutput_core (ε : ℝ) (hε : 0 < ε) (hbar a b s t : ℝ)
    (f : functionCore ε hε hbar) :
    timeOutput s t (coreToJoint ε hε hbar a (b*Real.exp s) f) =
      coreToJoint ε hε hbar a (b*Real.exp t) f := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · change (Real.exp (t-s) : ℂ) • (((b*Real.exp s : ℝ) : ℂ) • coreToMomentum ε hε hbar f) =
      ((b*Real.exp t : ℝ) : ℂ) • coreToMomentum ε hε hbar f
    rw [smul_smul, ← Complex.ofReal_mul]
    congr 2
    calc
      Real.exp (t-s) * (b*Real.exp s) = b*(Real.exp (t-s)*Real.exp s) := by ring
      _ = _ := by rw [exp_transition]

theorem joint_graph_transport (ε : ℝ) (hε : 0 < ε) (hbar a b s t : ℝ)
    (z : Hilbert × Output) (hz : z ∈ (jointClosed ε hε hbar a (b*Real.exp s)).graph) :
    (z.1,timeOutput s t z.2) ∈ (jointClosed ε hε hbar a (b*Real.exp t)).graph := by
  rw [joint_closed_graph] at hz ⊢
  exact closure_transport (coreToHilbert ε hε hbar)
    (coreToJoint ε hε hbar a (b*Real.exp s)) (coreToJoint ε hε hbar a (b*Real.exp t))
    (timeOutput s t) (timeOutput_core ε hε hbar a b s t) z hz

theorem common_form_domain (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) :
    (jointClosed ε hε hbar (Real.sqrt (1/2)) (Real.sqrt coupling*Real.exp s)).domain =
    (jointClosed ε hε hbar (Real.sqrt (1/2)) (Real.sqrt coupling*Real.exp t)).domain :=
  closed_domain_eq (coreToHilbert ε hε hbar)
    (coreToJoint ε hε hbar (Real.sqrt (1/2)) (Real.sqrt coupling*Real.exp s))
    (coreToJoint ε hε hbar (Real.sqrt (1/2)) (Real.sqrt coupling*Real.exp t))
    (timeOutput s t) (timeOutput t s)
    (timeOutput_core ε hε hbar _ _ s t) (timeOutput_core ε hε hbar _ _ t s)

def graphTime (s t : ℝ) : WithLp 2 (Hilbert × Output) →L[ℂ] WithLp 2 (Hilbert × Output) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert Output).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.id ℂ Hilbert).prodMap (timeOutput s t)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert Output).toContinuousLinearMap)

theorem graphTime_mem (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (u : FormSpace ε hε hbar coupling s) : graphTime s t u ∈ energyGraph ε hε hbar coupling t :=
  joint_graph_transport ε hε hbar _ _ s t (WithLp.ofLp u.val) u.property

def formTransfer (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) :
    FormSpace ε hε hbar coupling s → FormSpace ε hε hbar coupling t :=
  fun u => ⟨graphTime s t u.val,graphTime_mem ε hε hbar coupling s t u⟩

theorem transfer_add (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (u v : FormSpace ε hε hbar coupling s) :
    formTransfer ε hε hbar coupling s t (u+v) =
      formTransfer ε hε hbar coupling s t u + formTransfer ε hε hbar coupling s t v := by
  apply Subtype.ext
  exact (graphTime s t).map_add u.val v.val

theorem transfer_smul (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (a : ℂ) (u : FormSpace ε hε hbar coupling s) :
    formTransfer ε hε hbar coupling s t (a • u) = a • formTransfer ε hε hbar coupling s t u := by
  apply Subtype.ext
  exact (graphTime s t).map_smul a u.val

theorem transfer_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) :
    Continuous (formTransfer ε hε hbar coupling s t) :=
  ((graphTime s t).continuous.comp continuous_subtype_val).subtype_mk _

theorem embedding_value (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (u : FormSpace ε hε hbar coupling t) :
    embedding ε hε hbar coupling t u = (WithLp.ofLp u.val).1 := rfl

theorem energyOutput_value (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (u : FormSpace ε hε hbar coupling t) :
    energyOutput ε hε hbar coupling t u = (WithLp.ofLp u.val).2 := rfl

theorem transfer_value (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (u : FormSpace ε hε hbar coupling s) :
    (formTransfer ε hε hbar coupling s t u).val = graphTime s t u.val := rfl

theorem graphTime_fst (s t : ℝ) (z : WithLp 2 (Hilbert × Output)) :
    (WithLp.ofLp (graphTime s t z)).1 = (WithLp.ofLp z).1 := rfl

theorem graphTime_snd (s t : ℝ) (z : WithLp 2 (Hilbert × Output)) :
    (WithLp.ofLp (graphTime s t z)).2 = timeOutput s t (WithLp.ofLp z).2 := rfl

theorem transfer_embedding (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (u : FormSpace ε hε hbar coupling s) :
    embedding ε hε hbar coupling t (formTransfer ε hε hbar coupling s t u) =
      embedding ε hε hbar coupling s u := by
  calc
    _ = (WithLp.ofLp (formTransfer ε hε hbar coupling s t u).val).1 :=
      embedding_value ε hε hbar coupling t _
    _ = (WithLp.ofLp (graphTime s t u.val)).1 :=
      congrArg (fun z : WithLp 2 (Hilbert × Output) => (WithLp.ofLp z).1)
        (transfer_value ε hε hbar coupling s t u)
    _ = (WithLp.ofLp u.val).1 := graphTime_fst s t u.val
    _ = _ := (embedding_value ε hε hbar coupling s u).symm

theorem transfer_energyOutput (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (u : FormSpace ε hε hbar coupling s) :
    energyOutput ε hε hbar coupling t (formTransfer ε hε hbar coupling s t u) =
      timeOutput s t (energyOutput ε hε hbar coupling s u) := by
  calc
    _ = (WithLp.ofLp (formTransfer ε hε hbar coupling s t u).val).2 :=
      energyOutput_value ε hε hbar coupling t _
    _ = (WithLp.ofLp (graphTime s t u.val)).2 :=
      congrArg (fun z : WithLp 2 (Hilbert × Output) => (WithLp.ofLp z).2)
        (transfer_value ε hε hbar coupling s t u)
    _ = timeOutput s t (WithLp.ofLp u.val).2 := graphTime_snd s t u.val
    _ = _ := congrArg (timeOutput s t) (energyOutput_value ε hε hbar coupling s u).symm

theorem transfer_inverse (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (u : FormSpace ε hε hbar coupling s) :
    formTransfer ε hε hbar coupling t s (formTransfer ε hε hbar coupling s t u) = u := by
  apply embedding_injective ε hε hbar coupling s
  rw [transfer_embedding ε hε hbar coupling t s, transfer_embedding ε hε hbar coupling s t]

theorem transfer_comp (ε : ℝ) (hε : 0 < ε) (hbar coupling r s t : ℝ)
    (u : FormSpace ε hε hbar coupling r) :
    formTransfer ε hε hbar coupling s t (formTransfer ε hε hbar coupling r s u) =
      formTransfer ε hε hbar coupling r t u := by
  apply embedding_injective ε hε hbar coupling t
  rw [transfer_embedding ε hε hbar coupling s t, transfer_embedding ε hε hbar coupling r s,
    transfer_embedding ε hε hbar coupling r t]

#print axioms timeOutput_core
#print axioms joint_graph_transport
#print axioms common_form_domain
#print axioms transfer_add
#print axioms transfer_smul
#print axioms transfer_continuous
#print axioms transfer_embedding
#print axioms transfer_energyOutput
#print axioms transfer_inverse
#print axioms transfer_comp

end
end UnifiedTheory.Audit.KFCausalRegularizedFormTransport
