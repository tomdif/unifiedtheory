/- Exact physical exponential and inverse-clock graphs for the scalar
field-coefficient trials tensored with Schwartz transverse packets. -/
import UnifiedTheory.Audit.KFCausalShiftedFieldCoefficient
import UnifiedTheory.Audit.KFCausalOrderedExponentialClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalWeightedProductActions
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalCoupledProductDomain
open UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
open UnifiedTheory.Audit.KFCausalDampedProductDomain
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalFieldCoefficientTrials
open UnifiedTheory.Audit.KFCausalShiftedFieldCoefficient
open UnifiedTheory.Audit.KFCausalProductExponentialGraph
open UnifiedTheory.Audit.KFCausalPhysicalClockPowers
open UnifiedTheory.Audit.KFCausalLongitudinalExponential
open UnifiedTheory.Audit.KFCausalShiftedProductAction
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition
open UnifiedTheory.Audit.KFCausalOrderedExponentialClosure

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

def inverseWeightedState (ε a j p y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hj : 0 ≤ j)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : SchwartzMap TailSpace ℂ) : Hilbert :=
  productState ε hε (inverseHalfWeighted ε a j p y hε) ψ
    (inverseHalfWeighted_memLp ε a j p y hε ha hj hy) (ψ.memLp 2 volume)

theorem weightedState_inverse_clock_graph (ε a j p y : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hj : 0 ≤ j) (hy : |y| ≤ Real.pi*ε/2)
    (ψ : SchwartzMap TailSpace ℂ) :
    (weightedState ε a j p y hε ha hj hy ψ,inverseWeightedState ε a j p y hε ha hj hy ψ) ∈
      (clockPower (-(1/2))).graph := by
  apply (clockPower_graph _ _ _).mpr
  filter_upwards [productState_coe ε hε (inverseHalfWeighted ε a j p y hε) ψ
    (inverseHalfWeighted_memLp ε a j p y hε ha hj hy) (ψ.memLp 2 volume),
    weightedState_coe ε a j p y hε ha hj hy ψ] with z hi hs
  change inverseWeightedState ε a j p y hε ha hj hy ψ z = _ at hi
  rw [hi,hs]
  have he : (chartIso ε hε).symm (chart ε z.1)=z.1 := (chartIso ε hε).symm_apply_apply _
  simp only [weightedFunction,configurationProduct,coordinateHomeomorph_apply,inverseHalfWeighted,he]
  ring

theorem weightedState_mem_reversedExponential (ε a j p hbar : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hj : 0 ≤ j) (hh : |hbar| ≤ Real.pi*ε)
    (ψ : SchwartzMap TailSpace ℂ) :
    weightedState ε a j p 0 hε ha hj (zero_shift_bound ε hε) ψ ∈
      (reversedExponential ε hε hbar).domain := by
  apply (composition_domain _ _ _).mpr
  refine ⟨_,weightedState_exponential_graph ε a j p hbar (1/2) hε ha hj
    (half_shift_bound ε hbar hh) ψ,?_⟩
  exact LinearPMap.mem_domain_of_mem_graph
    (weightedState_inverse_clock_graph ε a j p (-(1/2)*hbar) hε ha hj (half_shift_bound ε hbar hh) ψ)

#print axioms zero_shift_bound
#print axioms weightedState_coe
#print axioms weightedState_zero_power
#print axioms weightedState_exponential_graph
#print axioms weightedState_inverse_clock_graph
#print axioms weightedState_mem_reversedExponential

end
end UnifiedTheory.Audit.KFCausalWeightedProductActions
