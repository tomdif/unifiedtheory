/- Dense coupled and clock-ordered domains with every transverse
direction controlled on one common smooth representative. The full matter
potential and charge-averaged Hamiltonian still require further estimates. -/
import UnifiedTheory.Audit.KFCausalAllTransverseTrialEnergy
import UnifiedTheory.Audit.KFCausalFullTransverseEnergySpace
import UnifiedTheory.Audit.KFCausalClockDressedDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFullTransverseJointDomain
noncomputable section
open MeasureTheory
open scoped ContDiff
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalDampedProductDomain
open UnifiedTheory.Audit.KFCausalCoupledTrialDensity
open UnifiedTheory.Audit.KFCausalCoupledJointDomain
open UnifiedTheory.Audit.KFCausalLongitudinalExponential
open UnifiedTheory.Audit.KFCausalPhysicalClockPowers
open UnifiedTheory.Audit.KFCausalClockDressedProducts
open UnifiedTheory.Audit.KFCausalClockDressedActions
open UnifiedTheory.Audit.KFCausalClockDressedDomain
open UnifiedTheory.Audit.KFCausalTransverseTrialDerivative
open UnifiedTheory.Audit.KFCausalAllTransverseTrialEnergy
open UnifiedTheory.Audit.KFCausalFullTransverseEnergySpace

theorem trialState_mem_allEnergySpace (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : SchwartzMap TailSpace ℂ) : trialState ε a p hε ha ψ (ψ.memLp 2 volume) ∈ allEnergySpace := by
  apply (mem_allEnergySpace_iff _).mpr
  exact ⟨trialFunction ε a p ψ,trialFunction_memLp ε a p hε ha ψ (ψ.memLp 2 volume),
    fun s => trialFunction_transverse_smooth ε a p s ψ,
    all_derivative_memLp ε a p hε ha ψ,trialState_coe ε a p hε ha ψ (ψ.memLp 2 volume)⟩

def allJointSpace (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Submodule ℂ Hilbert :=
  allEnergySpace ⊓ (longitudinalExponential ε hε hbar (1/2)).domain

theorem trialFamily_mem_allJointSpace (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| < Real.pi*ε) (v : ℝ × SchwartzMap TailSpace ℂ) :
    trialFamily ε a hε ha v ∈ allJointSpace ε hε hbar :=
  ⟨trialState_mem_allEnergySpace ε a v.1 hε ha v.2,
    trialState_half_domain ε a v.1 hbar hε ha hh v.2 v.2.integrable (v.2.memLp 2 volume)⟩

theorem allJointSpace_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| < Real.pi*ε) :
    (allJointSpace ε hε hbar).topologicalClosure=⊤ := by
  have hs : Submodule.span ℂ (Set.range (trialFamily ε 1 hε zero_lt_one)) ≤ allJointSpace ε hε hbar := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,rfl⟩
    exact trialFamily_mem_allJointSpace ε 1 hbar hε zero_lt_one hh v
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_trial_span ε 1 hε zero_lt_one] at hc
  exact top_unique hc

theorem allJointSpace_conditions (ε hbar : ℝ) (hε : 0 < ε) (f : Hilbert) :
    f ∈ allJointSpace ε hε hbar ↔
      f ∈ (longitudinalExponential ε hε hbar (1/2)).domain ∧
        ∃ g : Configuration → ℂ, MemLp g 2 ∧ (∀ s, ContDiff ℝ ∞ (fun y : Transverse => g (s,y))) ∧
          (∀ v : Transverse, MemLp (derivative v g) 2) ∧ f =ᵐ[volume] g := by
  change (f ∈ allEnergySpace ∧ _) ↔ _
  rw [mem_allEnergySpace_iff]
  exact and_comm

def allOrderedSpace (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Submodule ℂ Hilbert :=
  (clockPower (1/2)).domain ⊓ preimageSpace (clockPower (-(1/2))) (allJointSpace ε hε hbar)

theorem dressedFamily_mem_allOrderedSpace (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| < Real.pi*ε) (v : ℝ × SchwartzMap TailSpace ℂ) :
    dressedFamily ε a hε ha v ∈ allOrderedSpace ε hε hbar :=
  ⟨dressed_clock_domain ε a v.1 hε ha v.2 (v.2.memLp 2 volume),
    trialState ε a v.1 hε ha v.2 (v.2.memLp 2 volume),
    dressed_inverse_graph ε a v.1 hε ha v.2 (v.2.memLp 2 volume),
    trialFamily_mem_allJointSpace ε a hbar hε ha hh v⟩

theorem allOrderedSpace_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| < Real.pi*ε) :
    (allOrderedSpace ε hε hbar).topologicalClosure=⊤ := by
  have hs : Submodule.span ℂ (Set.range (dressedFamily ε 1 hε zero_lt_one)) ≤ allOrderedSpace ε hε hbar := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,rfl⟩
    exact dressedFamily_mem_allOrderedSpace ε 1 hbar hε zero_lt_one hh v
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_dressed_span ε 1 hε zero_lt_one] at hc
  exact top_unique hc

theorem allOrderedSpace_conditions (ε hbar : ℝ) (hε : 0 < ε) (f : Hilbert) :
    f ∈ allOrderedSpace ε hε hbar ↔ f ∈ (clockPower (1/2)).domain ∧
      ∃ hf : f ∈ (clockPower (-(1/2))).domain, clockPower (-(1/2)) ⟨f,hf⟩ ∈ allJointSpace ε hε hbar := by
  change (_ ∧ f ∈ preimageSpace _ _) ↔ _
  rw [preimageSpace_conditions]
  rfl

theorem allOrderedSpace_le_orderedSpace (ε hbar : ℝ) (hε : 0 < ε) :
    allOrderedSpace ε hε hbar ≤ orderedSpace ε hε hbar := by
  rintro f ⟨hA,g,hg,hjoint⟩
  exact ⟨hA,g,hg,allEnergySpace_le_energySpace hjoint.1,hjoint.2⟩

#print axioms trialState_mem_allEnergySpace
#print axioms trialFamily_mem_allJointSpace
#print axioms allJointSpace_dense
#print axioms allJointSpace_conditions
#print axioms dressedFamily_mem_allOrderedSpace
#print axioms allOrderedSpace_dense
#print axioms allOrderedSpace_conditions
#print axioms allOrderedSpace_le_orderedSpace

end
end UnifiedTheory.Audit.KFCausalFullTransverseJointDomain
