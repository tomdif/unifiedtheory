/- Exact revised exponential graphs for field-coefficient product trials.
Their zero-power subfamily is dense under the actual revised unitary. -/
import UnifiedTheory.Audit.KFCausalClockFloorShiftedCoefficient
import UnifiedTheory.Audit.KFCausalClockFloorCoreStates
import UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
import UnifiedTheory.Audit.KFCausalDampedProductTotality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorWeightedProducts
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (FrequencyHilbert)
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit (TailSpace)
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum (realTrial)
open UnifiedTheory.Audit.KFCausalDampedProductTotality
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalClockFloorFieldCoefficient
open UnifiedTheory.Audit.KFCausalClockFloorShiftedCoefficient
open UnifiedTheory.Audit.KFCausalClockFloorProductStates
open UnifiedTheory.Audit.KFCausalClockFloorCoreStates
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
open UnifiedTheory.Audit.KFCausalShiftedProductAction (half_shift_bound)

theorem zero_shift_bound (ε : ℝ) (hε : 0 < ε) : |(0:ℝ)| ≤ Real.pi*ε/2 := by
  rw [abs_zero]
  positivity

def weightedState (ε a j p y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hj : 0 ≤ j)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : SchwartzMap TailSpace ℂ) : Hilbert :=
  productState ε hε (shiftedWeighted ε a j p y) ψ
    (shiftedWeighted_memLp ε a j p y hε ha hj hy) (ψ.memLp 2 volume)

theorem weightedState_coe (ε a j p y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hj : 0 ≤ j)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : SchwartzMap TailSpace ℂ) :
    weightedState ε a j p y hε ha hj hy ψ =ᵐ[volume]
      weightedFunction ε hε (configurationProduct (shiftedWeighted ε a j p y) ψ) :=
  productState_coe ε hε _ ψ _ _

theorem weightedState_zero_power (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : SchwartzMap TailSpace ℂ) :
    weightedState ε a 0 p 0 hε ha le_rfl (zero_shift_bound ε hε) ψ =
      trialState ε a p hε ha ψ (ψ.memLp 2 volume) := by
  have hg : shiftedWeighted ε a 0 p 0=modulate p (realTrial ε a) := by
    rw [shiftedWeighted_zero]
    congr 1
    funext q
    rw [weightedLine_real ε a 0 hε]
    simp [realTrial]
  apply Lp.ext
  filter_upwards [weightedState_coe ε a 0 p 0 hε ha le_rfl (zero_shift_bound ε hε) ψ,
    trialState_coe ε a p hε ha ψ (ψ.memLp 2 volume)] with z hw ht
  rw [hw,ht,trialFunction_eq_weighted,hg]

theorem weightedState_exponential_graph (ε a j p hbar b : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hj : 0 ≤ j) (hb : |-b*hbar| ≤ Real.pi*ε/2)
    (ψ : SchwartzMap TailSpace ℂ) :
    (weightedState ε a j p 0 hε ha hj (zero_shift_bound ε hε) ψ,
      weightedState ε a j p (-b*hbar) hε ha hj hb ψ) ∈
        (longitudinalExponential ε hε hbar b).graph := by
  apply product_exponential_graph ε hbar b hε _ _ ψ
    (shiftedWeighted_integrable ε a j p 0 hε ha hj (zero_shift_bound ε hε)) _
    (shiftedWeighted_integrable ε a j p (-b*hbar) hε ha hj hb) _ (ψ.integrable) _
  intro k
  rw [shiftedWeighted_fourier ε a j p (-b*hbar) hε ha hj hb,shiftedWeighted_zero]
  rw [show -2*Real.pi*k*(-b*hbar) = b*(2*Real.pi*hbar*k) by ring]

theorem weightedState_mem_reversedExponential (ε a j p hbar : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hj : 0 ≤ j) (hh : |hbar| ≤ Real.pi*ε)
    (ψ : SchwartzMap TailSpace ℂ) :
    weightedState ε a j p 0 hε ha hj (zero_shift_bound ε hε) ψ ∈
      (reversedExponential ε hε hbar).domain := by
  apply (reversed_domain ε hε hbar _).mpr
  exact LinearPMap.mem_domain_of_mem_graph
    (weightedState_exponential_graph ε a j p hbar (1/2) hε ha hj (half_shift_bound ε hbar hh) ψ)

def trialFamily (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (v : ℝ × SchwartzMap TailSpace ℂ) : Hilbert :=
  trialState ε a v.1 hε ha v.2 (v.2.memLp 2 volume)

theorem lift_trial (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (v : ℝ × SchwartzMap TailSpace ℂ) :
    lift ε hε (euclideanTrial ε a hε.le ha v) = trialFamily ε a hε ha v := rfl

theorem dense_trial_span (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    (Submodule.span ℂ (Set.range (trialFamily ε a hε ha))).topologicalClosure = ⊤ := by
  let L : FrequencyHilbert →L[ℂ] Hilbert := lift ε hε
  have hd : DenseRange L := (lift ε hε).surjective.denseRange
  have he := hd.topologicalClosure_map_submodule (dense_euclidean_trial_span ε a hε.le ha)
  have ht : (L : FrequencyHilbert → Hilbert) ∘ euclideanTrial ε a hε.le ha = trialFamily ε a hε ha :=
    funext (lift_trial ε a hε ha)
  rw [Submodule.map_span,← Set.range_comp] at he
  change (Submodule.span ℂ (Set.range ((L : FrequencyHilbert → Hilbert) ∘ euclideanTrial ε a hε.le ha))).topologicalClosure=⊤ at he
  rw [ht] at he
  exact he

#print axioms zero_shift_bound
#print axioms weightedState_coe
#print axioms weightedState_zero_power
#print axioms weightedState_exponential_graph
#print axioms weightedState_mem_reversedExponential
#print axioms lift_trial
#print axioms dense_trial_span

end
end UnifiedTheory.Audit.KFCausalClockFloorWeightedProducts
