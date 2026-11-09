/- Continuous linear equivalences between the actual completed joint
energy forms at different times. Their physical L2 embedding is fixed. -/
import UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport
import UnifiedTheory.Audit.KFCausalPhysicalFormHamiltonian
import UnifiedTheory.Audit.KFCausalClosedGraphTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalFormTransport
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport
open UnifiedTheory.Audit.KFCausalPhysicalFormHamiltonian (formData)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε)
  (mass2 quartic vacuum : ℝ)

abbrev FormSpace (t : ℝ) := KFCausalClosedGraphForm.FormSpace (formData ε hε hbar hh mass2 quartic vacuum t)
def embedding (t : ℝ) : FormSpace ε hε hbar hh mass2 quartic vacuum t →L[ℂ] Hilbert :=
  KFCausalClosedGraphForm.embedding (formData ε hε hbar hh mass2 quartic vacuum t)
def energyOutput (t : ℝ) : FormSpace ε hε hbar hh mass2 quartic vacuum t →L[ℂ] Output (Fin 8) Hilbert :=
  KFCausalClosedGraphForm.energyOutput (formData ε hε hbar hh mass2 quartic vacuum t)

theorem embedding_injective (t : ℝ) : Function.Injective (embedding ε hε hbar hh mass2 quartic vacuum t) :=
  KFCausalClosedGraphForm.embedding_injective (formData ε hε hbar hh mass2 quartic vacuum t)

theorem form_norm_identity (t : ℝ) (u : FormSpace ε hε hbar hh mass2 quartic vacuum t) :
    ‖u‖^2=‖embedding ε hε hbar hh mass2 quartic vacuum t u‖^2+
      ‖energyOutput ε hε hbar hh mass2 quartic vacuum t u‖^2 :=
  KFCausalClosedGraphForm.form_norm_identity (formData ε hε hbar hh mass2 quartic vacuum t) u

theorem energyOutput_norm_le (t : ℝ) (u : FormSpace ε hε hbar hh mass2 quartic vacuum t) :
    ‖energyOutput ε hε hbar hh mass2 quartic vacuum t u‖ ≤ ‖u‖ := WithLp.norm_snd_le Hilbert u.val

def graphTime (s t : ℝ) : WithLp 2 (Hilbert × Output (Fin 8) Hilbert) →L[ℂ]
    WithLp 2 (Hilbert × Output (Fin 8) Hilbert) := KFCausalClosedGraphTransport.graphMap (timeOutput s t)

theorem timeMapsGraph (s t : ℝ) : KFCausalClosedGraphTransport.MapsGraph
    (formData ε hε hbar hh mass2 quartic vacuum s) (formData ε hε hbar hh mass2 quartic vacuum t) (timeOutput s t) :=
  closedEnergy_graph_transport ε hε hbar modelDirections pointField mass2 quartic vacuum s t hh

theorem graphTime_mem (s t : ℝ) (u : FormSpace ε hε hbar hh mass2 quartic vacuum s) :
    graphTime s t u.val ∈ KFCausalClosedGraphForm.energyGraph (formData ε hε hbar hh mass2 quartic vacuum t) :=
  closedEnergy_graph_transport ε hε hbar modelDirections pointField mass2 quartic vacuum s t hh
    (WithLp.ofLp u.val) u.property

def formTransfer (s t : ℝ) : FormSpace ε hε hbar hh mass2 quartic vacuum s →L[ℂ]
    FormSpace ε hε hbar hh mass2 quartic vacuum t :=
  KFCausalClosedGraphTransport.transfer (formData ε hε hbar hh mass2 quartic vacuum s)
    (formData ε hε hbar hh mass2 quartic vacuum t) (timeOutput s t)
    (timeMapsGraph ε hε hbar hh mass2 quartic vacuum s t)

theorem transfer_embedding (s t : ℝ) (u : FormSpace ε hε hbar hh mass2 quartic vacuum s) :
    embedding ε hε hbar hh mass2 quartic vacuum t (formTransfer ε hε hbar hh mass2 quartic vacuum s t u)=
      embedding ε hε hbar hh mass2 quartic vacuum s u :=
  KFCausalClosedGraphTransport.embedding_transfer (formData ε hε hbar hh mass2 quartic vacuum s)
    (formData ε hε hbar hh mass2 quartic vacuum t) (timeOutput s t)
    (timeMapsGraph ε hε hbar hh mass2 quartic vacuum s t) u

theorem transfer_energyOutput (s t : ℝ) (u : FormSpace ε hε hbar hh mass2 quartic vacuum s) :
    energyOutput ε hε hbar hh mass2 quartic vacuum t (formTransfer ε hε hbar hh mass2 quartic vacuum s t u)=
      timeOutput s t (energyOutput ε hε hbar hh mass2 quartic vacuum s u) :=
  KFCausalClosedGraphTransport.output_transfer (formData ε hε hbar hh mass2 quartic vacuum s)
    (formData ε hε hbar hh mass2 quartic vacuum t) (timeOutput s t)
    (timeMapsGraph ε hε hbar hh mass2 quartic vacuum s t) u

theorem transfer_inverse (s t : ℝ) (u : FormSpace ε hε hbar hh mass2 quartic vacuum s) :
    formTransfer ε hε hbar hh mass2 quartic vacuum t s (formTransfer ε hε hbar hh mass2 quartic vacuum s t u)=u :=
  KFCausalClosedGraphTransport.transfer_inverse (formData ε hε hbar hh mass2 quartic vacuum s)
    (formData ε hε hbar hh mass2 quartic vacuum t) (timeOutput s t) (timeOutput t s)
    (timeMapsGraph ε hε hbar hh mass2 quartic vacuum s t) (timeMapsGraph ε hε hbar hh mass2 quartic vacuum t s) u

theorem transfer_comp (r s t : ℝ) (u : FormSpace ε hε hbar hh mass2 quartic vacuum r) :
    formTransfer ε hε hbar hh mass2 quartic vacuum s t (formTransfer ε hε hbar hh mass2 quartic vacuum r s u)=
      formTransfer ε hε hbar hh mass2 quartic vacuum r t u :=
  KFCausalClosedGraphTransport.transfer_comp (formData ε hε hbar hh mass2 quartic vacuum r)
    (formData ε hε hbar hh mass2 quartic vacuum s) (formData ε hε hbar hh mass2 quartic vacuum t)
    (timeOutput r s) (timeOutput s t) (timeOutput r t)
    (timeMapsGraph ε hε hbar hh mass2 quartic vacuum r s) (timeMapsGraph ε hε hbar hh mass2 quartic vacuum s t)
    (timeMapsGraph ε hε hbar hh mass2 quartic vacuum r t) u

theorem transfer_self (t : ℝ) (u : FormSpace ε hε hbar hh mass2 quartic vacuum t) :
    formTransfer ε hε hbar hh mass2 quartic vacuum t t u=u :=
  KFCausalClosedGraphTransport.transfer_self (formData ε hε hbar hh mass2 quartic vacuum t)
    (timeOutput t t) (timeMapsGraph ε hε hbar hh mass2 quartic vacuum t t) u

def formEquiv (s t : ℝ) : FormSpace ε hε hbar hh mass2 quartic vacuum s ≃L[ℂ]
    FormSpace ε hε hbar hh mass2 quartic vacuum t :=
  KFCausalClosedGraphTransport.transferEquiv (formData ε hε hbar hh mass2 quartic vacuum s)
    (formData ε hε hbar hh mass2 quartic vacuum t) (timeOutput s t) (timeOutput t s)
    (timeMapsGraph ε hε hbar hh mass2 quartic vacuum s t) (timeMapsGraph ε hε hbar hh mass2 quartic vacuum t s)

#print axioms embedding_injective
#print axioms form_norm_identity
#print axioms energyOutput_norm_le
#print axioms graphTime_mem
#print axioms transfer_embedding
#print axioms transfer_energyOutput
#print axioms transfer_inverse
#print axioms transfer_comp
#print axioms transfer_self
#print axioms formEquiv

end
end UnifiedTheory.Audit.KFCausalPhysicalFormTransport
