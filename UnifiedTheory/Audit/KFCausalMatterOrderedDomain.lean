/- A dense ordered domain including the field and field-square factors
after the actual longitudinal half-exponential. This is not closedness of
the Hamiltonian form or a theorem about charge-averaged evolution. -/
import UnifiedTheory.Audit.KFCausalTransverseFieldSquare
import UnifiedTheory.Audit.KFCausalFullTransverseJointDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalMatterOrderedDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalDampedProductDomain
open UnifiedTheory.Audit.KFCausalCoupledTrialDensity
open UnifiedTheory.Audit.KFCausalLongitudinalExponential
open UnifiedTheory.Audit.KFCausalPhysicalClockPowers
open UnifiedTheory.Audit.KFCausalClockDressedProducts
open UnifiedTheory.Audit.KFCausalClockDressedActions
open UnifiedTheory.Audit.KFCausalClockDressedDomain
open UnifiedTheory.Audit.KFCausalFullTransverseEnergySpace
open UnifiedTheory.Audit.KFCausalFullTransverseJointDomain
open UnifiedTheory.Audit.KFCausalShiftedProductAction
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare

def pointField : Transverse →L[ℝ] ℝ where
  toFun x := x 2+x 3+x 4
  map_add' := by intro x y; simp only [Pi.add_apply]; ring
  map_smul' := by intro c x; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring
  cont := by fun_prop

theorem pointField_apply (x : Transverse) : pointField x=x 2+x 3+x 4 := rfl

def matterJointSpace (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (l : Transverse →L[ℝ] ℝ) : Submodule ℂ Hilbert :=
  allJointSpace ε hε hbar ⊓ preimageSpace (longitudinalExponential ε hε hbar (1/2)) (fieldSquare l).domain

theorem trialFamily_mem_matterJointSpace (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| ≤ Real.pi*ε) (l : Transverse →L[ℝ] ℝ) (v : ℝ × SchwartzMap TailSpace ℂ) :
    trialFamily ε a hε ha v ∈ matterJointSpace ε hε hbar l :=
  ⟨⟨trialState_mem_allEnergySpace ε a v.1 hε ha v.2,
      trialState_half_domain_closed_strip ε a v.1 hbar hε ha hh v.2 v.2.integrable (v.2.memLp 2 volume)⟩,
    shiftedState ε a v.1 (-(1/2)*hbar) hε ha (half_shift_bound ε hbar hh) v.2 (v.2.memLp 2 volume),
    trial_exponential_graph ε a v.1 hbar (1/2) hε ha (half_shift_bound ε hbar hh) v.2 v.2.integrable (v.2.memLp 2 volume),
    shiftedState_fieldSquare_domain ε a v.1 (-(1/2)*hbar) hε ha (half_shift_bound ε hbar hh) v.2 l⟩

theorem matterJointSpace_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : (matterJointSpace ε hε hbar l).topologicalClosure=⊤ := by
  have hs : Submodule.span ℂ (Set.range (trialFamily ε 1 hε zero_lt_one)) ≤ matterJointSpace ε hε hbar l := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,rfl⟩
    exact trialFamily_mem_matterJointSpace ε 1 hbar hε zero_lt_one hh l v
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_trial_span ε 1 hε zero_lt_one] at hc
  exact top_unique hc

theorem matterJointSpace_conditions (ε hbar : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ) (f : Hilbert) :
    f ∈ matterJointSpace ε hε hbar l ↔ f ∈ allJointSpace ε hε hbar ∧
      ∃ hf : f ∈ (longitudinalExponential ε hε hbar (1/2)).domain,
        longitudinalExponential ε hε hbar (1/2) ⟨f,hf⟩ ∈ (fieldSquare l).domain := by
  change (_ ∧ f ∈ preimageSpace _ _) ↔ _
  rw [preimageSpace_conditions]
  rfl

def matterOrderedSpace (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (l : Transverse →L[ℝ] ℝ) : Submodule ℂ Hilbert :=
  (clockPower (1/2)).domain ⊓ preimageSpace (clockPower (-(1/2))) (matterJointSpace ε hε hbar l)

theorem dressedFamily_mem_matterOrderedSpace (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| ≤ Real.pi*ε) (l : Transverse →L[ℝ] ℝ) (v : ℝ × SchwartzMap TailSpace ℂ) :
    dressedFamily ε a hε ha v ∈ matterOrderedSpace ε hε hbar l :=
  ⟨dressed_clock_domain ε a v.1 hε ha v.2 (v.2.memLp 2 volume),
    trialState ε a v.1 hε ha v.2 (v.2.memLp 2 volume),
    dressed_inverse_graph ε a v.1 hε ha v.2 (v.2.memLp 2 volume),
    trialFamily_mem_matterJointSpace ε a hbar hε ha hh l v⟩

theorem matterOrderedSpace_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : (matterOrderedSpace ε hε hbar l).topologicalClosure=⊤ := by
  have hs : Submodule.span ℂ (Set.range (dressedFamily ε 1 hε zero_lt_one)) ≤ matterOrderedSpace ε hε hbar l := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,rfl⟩
    exact dressedFamily_mem_matterOrderedSpace ε 1 hbar hε zero_lt_one hh l v
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_dressed_span ε 1 hε zero_lt_one] at hc
  exact top_unique hc

theorem matterOrderedSpace_conditions (ε hbar : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ) (f : Hilbert) :
    f ∈ matterOrderedSpace ε hε hbar l ↔ f ∈ (clockPower (1/2)).domain ∧
      ∃ hf : f ∈ (clockPower (-(1/2))).domain,
        clockPower (-(1/2)) ⟨f,hf⟩ ∈ matterJointSpace ε hε hbar l := by
  change (_ ∧ f ∈ preimageSpace _ _) ↔ _
  rw [preimageSpace_conditions]
  rfl

theorem matterOrderedSpace_le_allOrderedSpace (ε hbar : ℝ) (hε : 0 < ε)
    (l : Transverse →L[ℝ] ℝ) : matterOrderedSpace ε hε hbar l ≤ allOrderedSpace ε hε hbar := by
  rintro f ⟨hA,g,hg,hm⟩
  exact ⟨hA,g,hg,hm.1⟩

theorem matterJointSpace_linear_energy (ε hbar : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ)
    (f : Hilbert) (hf : f ∈ matterJointSpace ε hε hbar l) :
    ∃ hE : f ∈ (longitudinalExponential ε hε hbar (1/2)).domain,
      MemLp (fun z : Configuration => (l z.2:ℂ)*
        (longitudinalExponential ε hε hbar (1/2) ⟨f,hE⟩) z) 2 := by
  rcases ((matterJointSpace_conditions ε hbar hε l f).mp hf).2 with ⟨hE,hQ⟩
  exact ⟨hE,fieldSquare_linear_energy l _ hQ⟩

theorem pointField_ordered_domain_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε) :
    (matterOrderedSpace ε hε hbar pointField).topologicalClosure=⊤ :=
  matterOrderedSpace_dense ε hbar hε hh pointField

#print axioms pointField_apply
#print axioms trialFamily_mem_matterJointSpace
#print axioms matterJointSpace_dense
#print axioms matterJointSpace_conditions
#print axioms dressedFamily_mem_matterOrderedSpace
#print axioms matterOrderedSpace_dense
#print axioms matterOrderedSpace_conditions
#print axioms matterOrderedSpace_le_allOrderedSpace
#print axioms matterJointSpace_linear_energy
#print axioms pointField_ordered_domain_dense

end
end UnifiedTheory.Audit.KFCausalMatterOrderedDomain
