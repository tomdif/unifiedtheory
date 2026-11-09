/- A dense common domain of the actual transverse momenta, longitudinal
half-exponential and ordered field-square factor. Clock ordering is kept
explicit. This does not assert closedness of their composed energy form. -/
import UnifiedTheory.Audit.KFCausalTransverseMomentumDerivative
import UnifiedTheory.Audit.KFCausalMatterOrderedDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalMomentumMatterDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalTransverseMomentumDerivative
open UnifiedTheory.Audit.KFCausalLongitudinalExponential
open UnifiedTheory.Audit.KFCausalPhysicalClockPowers
open UnifiedTheory.Audit.KFCausalClockDressedDomain
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain
open UnifiedTheory.Audit.KFCausalCoupledTrialDensity
open UnifiedTheory.Audit.KFCausalClockDressedProducts

def momentumSpace (hbar : ℝ) : Submodule ℂ Hilbert :=
  ⨅ v : Transverse, (transverseMomentum hbar v).domain

theorem momentumSpace_mem (hbar : ℝ) (f : Hilbert) :
    f ∈ momentumSpace hbar ↔ ∀ v : Transverse, f ∈ (transverseMomentum hbar v).domain := by
  simp only [momentumSpace,Submodule.mem_iInf]

def operatorJointSpace (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (l : Transverse →L[ℝ] ℝ) : Submodule ℂ Hilbert :=
  momentumSpace hbar ⊓ preimageSpace (longitudinalExponential ε hε hbar (1/2)) (fieldSquare l).domain

theorem matterJointSpace_le_operatorJointSpace (ε hbar : ℝ) (hε : 0 < ε)
    (l : Transverse →L[ℝ] ℝ) : matterJointSpace ε hε hbar l ≤ operatorJointSpace ε hε hbar l := by
  intro f hf
  refine ⟨(momentumSpace_mem hbar f).mpr ?_,hf.2⟩
  intro v
  exact allEnergySpace_le_momentum_domain hbar v hf.1.1

theorem operatorJointSpace_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : (operatorJointSpace ε hε hbar l).topologicalClosure=⊤ := by
  have hc := Submodule.topologicalClosure_mono (matterJointSpace_le_operatorJointSpace ε hbar hε l)
  rw [matterJointSpace_dense ε hbar hε hh l] at hc
  exact top_unique hc

theorem operatorJointSpace_conditions (ε hbar : ℝ) (hε : 0 < ε)
    (l : Transverse →L[ℝ] ℝ) (f : Hilbert) :
    f ∈ operatorJointSpace ε hε hbar l ↔
      (∀ v : Transverse, f ∈ (transverseMomentum hbar v).domain) ∧
      ∃ hE : f ∈ (longitudinalExponential ε hε hbar (1/2)).domain,
        longitudinalExponential ε hε hbar (1/2) ⟨f,hE⟩ ∈ (fieldSquare l).domain := by
  change (f ∈ momentumSpace hbar ∧ f ∈ preimageSpace _ _) ↔ _
  rw [momentumSpace_mem,preimageSpace_conditions]

def operatorOrderedSpace (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (l : Transverse →L[ℝ] ℝ) : Submodule ℂ Hilbert :=
  (clockPower (1/2)).domain ⊓ preimageSpace (clockPower (-(1/2))) (operatorJointSpace ε hε hbar l)

theorem matterOrderedSpace_le_operatorOrderedSpace (ε hbar : ℝ) (hε : 0 < ε)
    (l : Transverse →L[ℝ] ℝ) : matterOrderedSpace ε hε hbar l ≤ operatorOrderedSpace ε hε hbar l := by
  rintro f ⟨hA,g,hg,hm⟩
  exact ⟨hA,g,hg,matterJointSpace_le_operatorJointSpace ε hbar hε l hm⟩

theorem operatorOrderedSpace_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : (operatorOrderedSpace ε hε hbar l).topologicalClosure=⊤ := by
  have hc := Submodule.topologicalClosure_mono (matterOrderedSpace_le_operatorOrderedSpace ε hbar hε l)
  rw [matterOrderedSpace_dense ε hbar hε hh l] at hc
  exact top_unique hc

theorem operatorOrderedSpace_conditions (ε hbar : ℝ) (hε : 0 < ε)
    (l : Transverse →L[ℝ] ℝ) (f : Hilbert) :
    f ∈ operatorOrderedSpace ε hε hbar l ↔ f ∈ (clockPower (1/2)).domain ∧
      ∃ hD : f ∈ (clockPower (-(1/2))).domain,
        clockPower (-(1/2)) ⟨f,hD⟩ ∈ operatorJointSpace ε hε hbar l := by
  change (_ ∧ f ∈ preimageSpace _ _) ↔ _
  rw [preimageSpace_conditions]
  rfl

theorem trialFamily_mem_operatorJointSpace (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| ≤ Real.pi*ε) (l : Transverse →L[ℝ] ℝ) (v : ℝ × SchwartzMap TailSpace ℂ) :
    trialFamily ε a hε ha v ∈ operatorJointSpace ε hε hbar l :=
  matterJointSpace_le_operatorJointSpace ε hbar hε l
    (trialFamily_mem_matterJointSpace ε a hbar hε ha hh l v)

theorem dressedFamily_mem_operatorOrderedSpace (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| ≤ Real.pi*ε) (l : Transverse →L[ℝ] ℝ) (v : ℝ × SchwartzMap TailSpace ℂ) :
    dressedFamily ε a hε ha v ∈ operatorOrderedSpace ε hε hbar l :=
  matterOrderedSpace_le_operatorOrderedSpace ε hbar hε l
    (dressedFamily_mem_matterOrderedSpace ε a hbar hε ha hh l v)

#print axioms momentumSpace_mem
#print axioms matterJointSpace_le_operatorJointSpace
#print axioms operatorJointSpace_dense
#print axioms operatorJointSpace_conditions
#print axioms matterOrderedSpace_le_operatorOrderedSpace
#print axioms operatorOrderedSpace_dense
#print axioms operatorOrderedSpace_conditions
#print axioms trialFamily_mem_operatorJointSpace
#print axioms dressedFamily_mem_operatorOrderedSpace

end
end UnifiedTheory.Audit.KFCausalMomentumMatterDomain
