/- The actual physical factors Phi E D and Phi^2 E D are densely
defined and closable. Explicit trial outputs establish dense natural
domains for D E Phi and D E Phi^2, without commuting any factors. -/
import UnifiedTheory.Audit.KFCausalFieldTrialGraphs
import UnifiedTheory.Audit.KFCausalTripleOperatorComposition
import UnifiedTheory.Audit.KFCausalClosedOrderedFactorDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalMatterFactorClosure
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalCoupledTrialDensity
open UnifiedTheory.Audit.KFCausalPhysicalClockPowers
open UnifiedTheory.Audit.KFCausalLongitudinalExponential
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalFieldTrialGraphs
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition
open UnifiedTheory.Audit.KFCausalTripleOperatorComposition
open UnifiedTheory.Audit.KFCausalOrderedExponentialClosure
open UnifiedTheory.Audit.KFCausalMomentumMatterDomain

def matterFactor (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (A : Hilbert →ₗ.[ℂ] Hilbert) :
    Hilbert →ₗ.[ℂ] Hilbert := composition A (orderedExponential ε hε hbar)
def reversedMatterFactor (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (A : Hilbert →ₗ.[ℂ] Hilbert) :
    Hilbert →ₗ.[ℂ] Hilbert := composition (reversedExponential ε hε hbar) A

theorem trial_mem_reversedLinear (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| ≤ Real.pi*ε) (l : Transverse →L[ℝ] ℝ) (v : ℝ × SchwartzMap TailSpace ℂ) :
    trialFamily ε a hε ha v ∈ (reversedMatterFactor ε hε hbar (physicalField l)).domain := by
  apply (composition_domain _ _ _).mpr
  exact ⟨linearState ε a v.1 hε ha l v.2,trial_physicalField_graph ε a v.1 hε ha l v.2,
    linearState_mem_reversedExponential ε a v.1 hbar hε ha hh l v.2⟩

theorem trial_mem_reversedQuadratic (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| ≤ Real.pi*ε) (l : Transverse →L[ℝ] ℝ) (v : ℝ × SchwartzMap TailSpace ℂ) :
    trialFamily ε a hε ha v ∈ (reversedMatterFactor ε hε hbar (fieldSquare l)).domain := by
  apply (composition_domain _ _ _).mpr
  exact ⟨quadraticState ε a v.1 hε ha l v.2,trial_fieldSquare_graph ε a v.1 hε ha l v.2,
    quadraticState_mem_reversedExponential ε a v.1 hbar hε ha hh l v.2⟩

theorem reversedLinear_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) :
    Dense ((reversedMatterFactor ε hε hbar (physicalField l)).domain : Set Hilbert) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hs : Submodule.span ℂ (Set.range (trialFamily ε 1 hε zero_lt_one)) ≤
      (reversedMatterFactor ε hε hbar (physicalField l)).domain := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,rfl⟩
    exact trial_mem_reversedLinear ε 1 hbar hε zero_lt_one hh l v
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_trial_span ε 1 hε zero_lt_one] at hc
  exact top_unique hc

theorem reversedQuadratic_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) :
    Dense ((reversedMatterFactor ε hε hbar (fieldSquare l)).domain : Set Hilbert) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hs : Submodule.span ℂ (Set.range (trialFamily ε 1 hε zero_lt_one)) ≤
      (reversedMatterFactor ε hε hbar (fieldSquare l)).domain := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,rfl⟩
    exact trial_mem_reversedQuadratic ε 1 hbar hε zero_lt_one hh l v
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_trial_span ε 1 hε zero_lt_one] at hc
  exact top_unique hc

theorem matterFactor_formalAdjoint (ε hbar : ℝ) (hε : 0 < ε)
    (A : Hilbert →ₗ.[ℂ] Hilbert) (hA : IsSelfAdjoint A) :
    (matterFactor ε hε hbar A).IsFormalAdjoint (reversedMatterFactor ε hε hbar A) :=
  triple_formalAdjoint A _ _ hA (longitudinal_exponential_selfAdjoint ε hε hbar (1/2))
    (clockPower_selfAdjoint (-(1/2)))

theorem linearMatter_closable (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : (matterFactor ε hε hbar (physicalField l)).IsClosable :=
  triple_closable _ _ _ (physicalField_selfAdjoint l)
    (longitudinal_exponential_selfAdjoint ε hε hbar (1/2)) (clockPower_selfAdjoint (-(1/2)))
    (reversedLinear_dense ε hbar hε hh l)

theorem quadraticMatter_closable (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : (matterFactor ε hε hbar (fieldSquare l)).IsClosable :=
  triple_closable _ _ _ (fieldSquare_selfAdjoint l)
    (longitudinal_exponential_selfAdjoint ε hε hbar (1/2)) (clockPower_selfAdjoint (-(1/2)))
    (reversedQuadratic_dense ε hbar hε hh l)

theorem orderedSpace_le_matterFactor (ε hbar : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ)
    (A : Hilbert →ₗ.[ℂ] Hilbert) (hA : (fieldSquare l).domain ≤ A.domain) :
    operatorOrderedSpace ε hε hbar l ≤ (matterFactor ε hε hbar A).domain := by
  rintro f ⟨_,g,hg,hj⟩
  obtain ⟨y,hy,hyA⟩ := hj.2
  apply (composition_domain _ _ _).mpr
  exact ⟨y,(composition_graph _ _ _ _).mpr ⟨g,hg,hy⟩,hA hyA⟩

theorem linearMatter_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : Dense ((matterFactor ε hε hbar (physicalField l)).domain : Set Hilbert) :=
  (Submodule.dense_iff_topologicalClosure_eq_top.mpr (operatorOrderedSpace_dense ε hbar hε hh l)).mono
    (orderedSpace_le_matterFactor ε hbar hε l _ (fieldSquare_domain_le_physicalField l))

theorem quadraticMatter_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : Dense ((matterFactor ε hε hbar (fieldSquare l)).domain : Set Hilbert) :=
  (Submodule.dense_iff_topologicalClosure_eq_top.mpr (operatorOrderedSpace_dense ε hbar hε hh l)).mono
    (orderedSpace_le_matterFactor ε hbar hε l _ le_rfl)

def closedMatterFactor (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (A : Hilbert →ₗ.[ℂ] Hilbert) :
    Hilbert →ₗ.[ℂ] Hilbert := (matterFactor ε hε hbar A).closure

theorem matterFactor_le_closure (ε hbar : ℝ) (hε : 0 < ε) (A : Hilbert →ₗ.[ℂ] Hilbert) :
    matterFactor ε hε hbar A ≤ closedMatterFactor ε hε hbar A :=
  (matterFactor ε hε hbar A).le_closure

theorem closedLinearMatter_closed (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : (closedMatterFactor ε hε hbar (physicalField l)).IsClosed :=
  (linearMatter_closable ε hbar hε hh l).closure_isClosed

theorem closedQuadraticMatter_closed (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : (closedMatterFactor ε hε hbar (fieldSquare l)).IsClosed :=
  (quadraticMatter_closable ε hbar hε hh l).closure_isClosed

theorem closedLinearMatter_graph (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) :
    (closedMatterFactor ε hε hbar (physicalField l)).graph=
      (matterFactor ε hε hbar (physicalField l)).graph.topologicalClosure :=
  (linearMatter_closable ε hbar hε hh l).graph_closure_eq_closure_graph.symm

theorem closedQuadraticMatter_graph (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) :
    (closedMatterFactor ε hε hbar (fieldSquare l)).graph=
      (matterFactor ε hε hbar (fieldSquare l)).graph.topologicalClosure :=
  (quadraticMatter_closable ε hbar hε hh l).graph_closure_eq_closure_graph.symm

theorem closedLinearMatter_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : Dense ((closedMatterFactor ε hε hbar (physicalField l)).domain : Set Hilbert) :=
  (linearMatter_dense ε hbar hε hh l).mono (matterFactor_le_closure ε hbar hε _).1

theorem closedQuadraticMatter_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : Dense ((closedMatterFactor ε hε hbar (fieldSquare l)).domain : Set Hilbert) :=
  (quadraticMatter_dense ε hbar hε hh l).mono (matterFactor_le_closure ε hbar hε _).1

#print axioms trial_mem_reversedLinear
#print axioms trial_mem_reversedQuadratic
#print axioms reversedLinear_dense
#print axioms reversedQuadratic_dense
#print axioms matterFactor_formalAdjoint
#print axioms linearMatter_closable
#print axioms quadraticMatter_closable
#print axioms orderedSpace_le_matterFactor
#print axioms linearMatter_dense
#print axioms quadraticMatter_dense
#print axioms matterFactor_le_closure
#print axioms closedLinearMatter_closed
#print axioms closedQuadraticMatter_closed
#print axioms closedLinearMatter_graph
#print axioms closedQuadraticMatter_graph
#print axioms closedLinearMatter_dense
#print axioms closedQuadraticMatter_dense

end
end UnifiedTheory.Audit.KFCausalMatterFactorClosure
