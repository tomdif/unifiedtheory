/- A fixed-time positive self-adjoint Hamiltonian for the unaveraged,
revised clock-floor six-coordinate candidate, built from the joint graph
closure of its eight ordered factors. This does not assert charge
averaging, time-dependent evolution, a regulator limit, or identification
with the finite spin model or physical spacetime. -/
import UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
import UnifiedTheory.Audit.KFCausalClosedGraphForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (commonEnergyDomain)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε)
  (mass2 quartic vacuum t : ℝ)

def formData : KFCausalClosedGraphForm.Data Hilbert (Output (Fin 8) Hilbert) where
  operator := closedEnergy ε hε hbar modelDirections pointField mass2 quartic vacuum t
  closed := closedEnergy_closed ε hε hbar modelDirections pointField mass2 quartic vacuum t hh
  dense := closedEnergy_dense ε hε hbar modelDirections pointField mass2 quartic vacuum t hh

local notation "𝒟" => formData ε hε hbar hh mass2 quartic vacuum t

def hamiltonian : Hilbert →ₗ.[ℂ] Hilbert := KFCausalClosedGraphForm.hamiltonian 𝒟

theorem hamiltonian_selfAdjoint : IsSelfAdjoint (hamiltonian ε hε hbar hh mass2 quartic vacuum t) :=
  KFCausalClosedGraphForm.hamiltonian_selfAdjoint 𝒟

theorem hamiltonian_closed : (hamiltonian ε hε hbar hh mass2 quartic vacuum t).IsClosed :=
  KFCausalClosedGraphForm.hamiltonian_closed 𝒟

theorem hamiltonian_dense : Dense ((hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain : Set Hilbert) :=
  KFCausalClosedGraphForm.hamiltonian_dense 𝒟

theorem hamiltonian_positive (x : (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain) :
    0 ≤ (inner ℂ (hamiltonian ε hε hbar hh mass2 quartic vacuum t x) (x:Hilbert)).re :=
  KFCausalClosedGraphForm.hamiltonian_positive 𝒟 x

theorem hamiltonian_represents_form (x : (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain)
    (u : KFCausalClosedGraphForm.FormSpace 𝒟) :
    inner ℂ (KFCausalClosedGraphForm.energyOutput 𝒟 (KFCausalClosedGraphForm.formLift 𝒟 x))
      (KFCausalClosedGraphForm.energyOutput 𝒟 u) =
    inner ℂ (hamiltonian ε hε hbar hh mass2 quartic vacuum t x) (KFCausalClosedGraphForm.embedding 𝒟 u) :=
  KFCausalClosedGraphForm.hamiltonian_represents_form 𝒟 x u

theorem hamiltonian_energy (x : (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain) :
    (inner ℂ (hamiltonian ε hε hbar hh mass2 quartic vacuum t x) (x:Hilbert)).re =
      ‖KFCausalClosedGraphForm.energyOutput 𝒟 (KFCausalClosedGraphForm.formLift 𝒟 x)‖^2 :=
  KFCausalClosedGraphForm.hamiltonian_energy 𝒟 x

theorem hamiltonian_domain_characterization (u : KFCausalClosedGraphForm.FormSpace 𝒟) (y : Hilbert) :
    (∃ hx : KFCausalClosedGraphForm.embedding 𝒟 u ∈ (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain,
      hamiltonian ε hε hbar hh mass2 quartic vacuum t ⟨KFCausalClosedGraphForm.embedding 𝒟 u,hx⟩=y) ↔
    ∀ v, inner ℂ (KFCausalClosedGraphForm.energyOutput 𝒟 u) (KFCausalClosedGraphForm.energyOutput 𝒟 v)=
      inner ℂ y (KFCausalClosedGraphForm.embedding 𝒟 v) :=
  KFCausalClosedGraphForm.hamiltonian_domain_characterization 𝒟 u y

def commonFormVector (f : commonEnergyDomain ε hε hbar modelDirections pointField) :
    KFCausalClosedGraphForm.FormSpace 𝒟 :=
  ⟨WithLp.toLp 2 ((f:Hilbert),jointOutput ε hε hbar modelDirections pointField mass2 quartic vacuum t f),
    jointOutput_closed_graph ε hε hbar modelDirections pointField mass2 quartic vacuum t hh f⟩

theorem commonFormVector_embedding (f : commonEnergyDomain ε hε hbar modelDirections pointField) :
    KFCausalClosedGraphForm.embedding 𝒟 (commonFormVector ε hε hbar hh mass2 quartic vacuum t f)=f := rfl

theorem commonFormVector_output (f : commonEnergyDomain ε hε hbar modelDirections pointField) :
    KFCausalClosedGraphForm.energyOutput 𝒟 (commonFormVector ε hε hbar hh mass2 quartic vacuum t f)=
      jointOutput ε hε hbar modelDirections pointField mass2 quartic vacuum t f := rfl

theorem commonFormVector_energy (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (f : commonEnergyDomain ε hε hbar modelDirections pointField) :
    ‖KFCausalClosedGraphForm.energyOutput 𝒟 (commonFormVector ε hε hbar hh mass2 quartic vacuum t f)‖^2=
      seedEnergy ε hε hbar modelDirections pointField mass2 quartic vacuum t f :=
  jointOutput_norm_seedEnergy ε hε hbar modelDirections pointField mass2 quartic vacuum t hm hq hv f

theorem commonFormVector_norm (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (f : commonEnergyDomain ε hε hbar modelDirections pointField) :
    ‖commonFormVector ε hε hbar hh mass2 quartic vacuum t f‖^2=
      ‖(f:Hilbert)‖^2+seedEnergy ε hε hbar modelDirections pointField mass2 quartic vacuum t f := by
  rw [KFCausalClosedGraphForm.form_norm_identity,commonFormVector_embedding,
    commonFormVector_energy ε hε hbar hh mass2 quartic vacuum t hm hq hv]

theorem hamiltonian_seed_energy (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (x : (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain)
    (hx : (x:Hilbert) ∈ commonEnergyDomain ε hε hbar modelDirections pointField) :
    (inner ℂ (hamiltonian ε hε hbar hh mass2 quartic vacuum t x) (x:Hilbert)).re =
      seedEnergy ε hε hbar modelDirections pointField mass2 quartic vacuum t ⟨x,hx⟩ := by
  have hl : KFCausalClosedGraphForm.formLift 𝒟 x = commonFormVector ε hε hbar hh mass2 quartic vacuum t ⟨x,hx⟩ :=
    KFCausalClosedGraphForm.embedding_injective 𝒟 (KFCausalClosedGraphForm.embedding_formLift 𝒟 x)
  rw [hamiltonian_energy,hl,commonFormVector_energy ε hε hbar hh mass2 quartic vacuum t hm hq hv]

#print axioms hamiltonian_selfAdjoint
#print axioms hamiltonian_closed
#print axioms hamiltonian_dense
#print axioms hamiltonian_positive
#print axioms hamiltonian_represents_form
#print axioms hamiltonian_energy
#print axioms hamiltonian_domain_characterization
#print axioms commonFormVector_embedding
#print axioms commonFormVector_output
#print axioms commonFormVector_energy
#print axioms commonFormVector_norm
#print axioms hamiltonian_seed_energy

end
end UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian
