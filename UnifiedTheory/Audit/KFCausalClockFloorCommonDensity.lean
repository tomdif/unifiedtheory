/- Density of the full natural eight-factor domain for the revised
clock-floor model. It follows from an explicit product family, whose
ordered clock, momentum, matter and exponential domains are all proved.
This does not assert density inside the charge-zero sector. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoreGradient
import UnifiedTheory.Audit.KFCausalClockFloorCoreMatter
import UnifiedTheory.Audit.KFCausalClockFloorCoreDensity
import UnifiedTheory.Audit.KFCausalClockFloorCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorCommonDensity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit (TailSpace)
open UnifiedTheory.Audit.KFCausalClockFloorCoreStates
open UnifiedTheory.Audit.KFCausalClockFloorCoreDerivative
open UnifiedTheory.Audit.KFCausalClockFloorCoreGradient
open UnifiedTheory.Audit.KFCausalClockFloorCoreMatter
open UnifiedTheory.Audit.KFCausalClockFloorCoreDensity
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open UnifiedTheory.Audit.KFCausalShiftedProductAction (half_shift_bound)
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalTransverseMomentumDerivative
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

theorem trialState_momentum_domain (ε a p hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : SchwartzMap TailSpace ℂ) (v : Transverse) :
    trialState ε a p hε ha ψ (ψ.memLp 2 volume) ∈ (transverseMomentum hbar v).domain := by
  rw [trialState_toLp]
  exact derivative_momentum_domain hbar _ v (trialFunction_memLp ε a p hε ha ψ (ψ.memLp 2 volume))
    (all_derivative_memLp ε a p hε ha ψ v) (fun s => trialFunction_transverse_differentiable ε a p s ψ)

theorem dressed_clockMomentum_domain (ε a p hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : SchwartzMap TailSpace ℂ) (v : Transverse) :
    dressedState ε a p hε ha ψ (ψ.memLp 2 volume) ∈ (clockMomentum ε hbar v).domain := by
  apply (composition_domain _ _ _).mpr
  exact ⟨_,dressed_inverse_graph ε a p hε ha ψ (ψ.memLp 2 volume),
    trialState_momentum_domain ε a p hbar hε ha ψ v⟩

theorem dressed_ordered_graph (ε a p hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| ≤ Real.pi*ε) (ψ : SchwartzMap TailSpace ℂ) :
    (dressedState ε a p hε ha ψ (ψ.memLp 2 volume),
      shiftedState ε a p (-(1/2:ℝ)*hbar) hε ha (half_shift_bound ε hbar hh) ψ (ψ.memLp 2 volume)) ∈
        (orderedExponential ε hε hbar).graph := by
  apply (composition_graph _ _ _ _).mpr
  exact ⟨_,dressed_inverse_graph ε a p hε ha ψ (ψ.memLp 2 volume),
    trial_exponential_graph ε a p hbar (1/2) hε ha (half_shift_bound ε hbar hh) ψ ψ.integrable (ψ.memLp 2 volume)⟩

theorem dressed_linearMatter_domain (ε a p hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| ≤ Real.pi*ε) (ψ : SchwartzMap TailSpace ℂ) (l : Transverse →L[ℝ] ℝ) :
    dressedState ε a p hε ha ψ (ψ.memLp 2 volume) ∈ (matterFactor ε hε hbar (physicalField l)).domain := by
  apply (composition_domain _ _ _).mpr
  exact ⟨_,dressed_ordered_graph ε a p hbar hε ha hh ψ,
    shiftedState_physicalField_domain ε a p _ hε ha (half_shift_bound ε hbar hh) ψ l⟩

theorem dressed_quadraticMatter_domain (ε a p hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| ≤ Real.pi*ε) (ψ : SchwartzMap TailSpace ℂ) (l : Transverse →L[ℝ] ℝ) :
    dressedState ε a p hε ha ψ (ψ.memLp 2 volume) ∈ (matterFactor ε hε hbar (fieldSquare l)).domain := by
  apply (composition_domain _ _ _).mpr
  exact ⟨_,dressed_ordered_graph ε a p hbar hε ha hh ψ,
    shiftedState_fieldSquare_domain ε a p _ hε ha (half_shift_bound ε hbar hh) ψ l⟩

theorem family_mem_commonEnergyDomain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| ≤ Real.pi*ε) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (k : ℝ × SchwartzMap TailSpace ℂ) : family ε a hε ha k ∈ commonEnergyDomain ε hε hbar v l := by
  apply (commonEnergyDomain_iff ε hε hbar v l _).mpr
  intro i
  fin_cases i
  · exact LinearPMap.mem_domain_of_mem_graph (dressed_clock_graph ε a k.1 hε ha k.2 (k.2.memLp 2 volume))
  · exact dressed_clockMomentum_domain ε a k.1 hbar hε ha k.2 (v 0)
  · exact dressed_clockMomentum_domain ε a k.1 hbar hε ha k.2 (v 1)
  · exact dressed_clockMomentum_domain ε a k.1 hbar hε ha k.2 (v 2)
  · exact dressed_clockMomentum_domain ε a k.1 hbar hε ha k.2 (v 3)
  · exact dressed_linearMatter_domain ε a k.1 hbar hε ha hh k.2 l
  · exact dressed_quadraticMatter_domain ε a k.1 hbar hε ha hh k.2 l
  · exact LinearPMap.mem_domain_of_mem_graph (dressed_ordered_graph ε a k.1 hbar hε ha hh k.2)

theorem commonEnergyDomain_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    Dense (commonEnergyDomain ε hε hbar v l : Set Hilbert) := by
  have hs : Submodule.span ℂ (Set.range (family ε 1 hε zero_lt_one)) ≤ commonEnergyDomain ε hε hbar v l := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    exact family_mem_commonEnergyDomain ε 1 hbar hε zero_lt_one hh v l k
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_family_span] at hc
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr (top_unique hc)

theorem energyFactor_domain_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    Dense ((energyFactor ε hε hbar v l i).domain : Set Hilbert) := by
  apply (commonEnergyDomain_dense ε hbar hε hh v l).mono
  intro f hf
  exact (commonEnergyDomain_iff ε hε hbar v l f).mp hf i

theorem clockMomentum_closable (ε hbar : ℝ) (hε : 0 < ε) (v : Transverse) :
    (clockMomentum ε hbar v).IsClosable := by
  apply composition_closable _ _ (transverseMomentum_selfAdjoint hbar v) (inverseClockHalf_selfAdjoint ε)
  apply (transverseMomentum_selfAdjoint hbar v).dense_domain.mono
  intro f hf
  apply (composition_domain _ _ _).mpr
  exact ⟨_,(transverseMomentum hbar v).mem_graph ⟨f,hf⟩,inverseClockHalf_domain ε hε _⟩

#print axioms trialState_momentum_domain
#print axioms dressed_clockMomentum_domain
#print axioms dressed_ordered_graph
#print axioms dressed_linearMatter_domain
#print axioms dressed_quadraticMatter_domain
#print axioms family_mem_commonEnergyDomain
#print axioms commonEnergyDomain_dense
#print axioms energyFactor_domain_dense
#print axioms clockMomentum_closable

end
end UnifiedTheory.Audit.KFCausalClockFloorCommonDensity
