/- The actual physical factors Phi E D and Phi^2 E D are densely
defined and closable. Explicit trial outputs establish dense natural
domains for D E Phi and D E Phi^2, without commuting any factors. -/
import UnifiedTheory.Audit.KFCausalClockFloorFieldGraphs
import UnifiedTheory.Audit.KFCausalTripleOperatorComposition
import UnifiedTheory.Audit.KFCausalClockFloorCommonDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorMatterClosure
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockFloorWeightedProducts
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalClockFloorFieldGraphs
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition
open UnifiedTheory.Audit.KFCausalTripleOperatorComposition
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDensity
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)

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
    (inverseClockHalf_selfAdjoint ε)

theorem linearMatter_closable (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : (matterFactor ε hε hbar (physicalField l)).IsClosable :=
  triple_closable _ _ _ (physicalField_selfAdjoint l)
    (longitudinal_exponential_selfAdjoint ε hε hbar (1/2)) (inverseClockHalf_selfAdjoint ε)
    (reversedLinear_dense ε hbar hε hh l)

theorem quadraticMatter_closable (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) : (matterFactor ε hε hbar (fieldSquare l)).IsClosable :=
  triple_closable _ _ _ (fieldSquare_selfAdjoint l)
    (longitudinal_exponential_selfAdjoint ε hε hbar (1/2)) (inverseClockHalf_selfAdjoint ε)
    (reversedQuadratic_dense ε hbar hε hh l)

theorem energyFactor_closable (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    (energyFactor ε hε hbar v l i).IsClosable := by
  fin_cases i
  · exact (clockHalf_selfAdjoint ε).isClosed.isClosable
  · exact clockMomentum_closable ε hbar hε (v 0)
  · exact clockMomentum_closable ε hbar hε (v 1)
  · exact clockMomentum_closable ε hbar hε (v 2)
  · exact clockMomentum_closable ε hbar hε (v 3)
  · exact linearMatter_closable ε hbar hε hh l
  · exact quadraticMatter_closable ε hbar hε hh l
  · exact orderedExponential_closable ε hε hbar

#print axioms trial_mem_reversedLinear
#print axioms trial_mem_reversedQuadratic
#print axioms reversedLinear_dense
#print axioms reversedQuadratic_dense
#print axioms matterFactor_formalAdjoint
#print axioms linearMatter_closable
#print axioms quadraticMatter_closable
#print axioms energyFactor_closable

end
end UnifiedTheory.Audit.KFCausalClockFloorMatterClosure
