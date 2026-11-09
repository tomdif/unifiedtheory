/- Product-core states for the revised model, their clock dressings, and
the exact longitudinal exponential output. The transverse packet remains
arbitrary L1/L2; no Gaussian shape or charge invariance is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorProductStates
import UnifiedTheory.Audit.KFCausalClockFloorCoreWeights
import UnifiedTheory.Audit.KFCausalShiftedProductAction
import UnifiedTheory.Audit.KFCausalClockFloorClockHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoreStates
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseDilationPullback
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalDampedGaussianTotality
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalShiftedDampedScalar
open UnifiedTheory.Audit.KFCausalClockFloorProductStates
open UnifiedTheory.Audit.KFCausalClockFloorCoreWeights
open UnifiedTheory.Audit.KFCausalClockFloorFlow
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorTestPullback (weight)
open UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge (amplitude)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorExponential

def trialFunction (ε a p : ℝ) (ψ : TailSpace → ℂ) (x : Configuration) : ℂ :=
  (Real.sqrt (Real.exp x.1+ε):ℂ)*(modulate p (realTrial ε a) (chart ε x.1)*
    pullback x.1 (ψ ∘ transverseCoordinates) x.2)

def trialState (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) : Hilbert :=
  productState ε hε (modulate p (realTrial ε a)) ψ (modulated_memLp ε a p hε.le ha) hψ

def dressedState (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) : Hilbert :=
  productState ε hε (dressedScalar ε a hε p) ψ (dressedScalar_memLp ε a hε ha p) hψ

def clockEnergyState (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) : Hilbert :=
  productState ε hε (wholeScalar ε a hε p) ψ (wholeScalar_memLp ε a hε ha p) hψ

def shiftedState (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) : Hilbert :=
  productState ε hε (shiftedScalar ε a p y) ψ (shiftedScalar_memLp ε a p y hε ha hy) hψ

theorem trialFunction_eq_weighted (ε a p : ℝ) (hε : 0 < ε) (ψ : TailSpace → ℂ) :
    trialFunction ε a p ψ = weightedFunction ε hε (configurationProduct (modulate p (realTrial ε a)) ψ) := by
  funext x
  simp only [trialFunction,weightedFunction,weight,amplitude,Complex.ofReal_mul,
    configurationProduct,coordinateHomeomorph,straightening,pullback,Function.comp_apply]
  change _ = ((Real.sqrt (Real.exp x.1+ε):ℂ)*(Real.exp (-x.1):ℂ))*
    (modulate p (realTrial ε a) (chart ε x.1)*ψ (transverseCoordinates (flow (-x.1) x.2)))
  ring

theorem trialFunction_memLp (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) : MemLp (trialFunction ε a p ψ) 2 := by
  rw [trialFunction_eq_weighted ε a p hε ψ]
  exact weighted_memLp ε hε _ (configuration_memLp _ ψ (modulated_memLp ε a p hε.le ha) hψ)

theorem trialState_coe (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    trialState ε a p hε ha ψ hψ =ᵐ[volume] trialFunction ε a p ψ := by
  rw [trialFunction_eq_weighted ε a p hε ψ]
  exact productState_coe ε hε _ ψ (modulated_memLp ε a p hε.le ha) hψ

theorem trialState_toLp (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    trialState ε a p hε ha ψ hψ = (trialFunction_memLp ε a p hε ha ψ hψ).toLp (trialFunction ε a p ψ) := by
  apply Lp.ext
  exact (trialState_coe ε a p hε ha ψ hψ).trans (trialFunction_memLp ε a p hε ha ψ hψ).coeFn_toLp.symm

theorem clock_coordinate (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    KFCausalClockTrialWeights.clock ε hε (coordinateHomeomorph ε hε x).1 = Real.exp x.1 := by
  change Real.exp ((chartIso ε hε).symm (chart ε x.1)) = Real.exp x.1
  rw [← chartIso_apply ε hε,OrderIso.symm_apply_apply]

theorem trial_to_dressed_graph (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    (trialState ε a p hε ha ψ hψ,dressedState ε a p hε ha ψ hψ) ∈ (clockHalf ε).graph := by
  apply (clockHalf_graph ε _ _).mpr
  filter_upwards [productState_coe ε hε _ ψ (modulated_memLp ε a p hε.le ha) hψ,
    productState_coe ε hε _ ψ (dressedScalar_memLp ε a hε ha p) hψ] with x ht hd
  unfold dressedState trialState
  rw [hd,ht]
  simp only [weightedFunction,configurationProduct,dressedScalar,halfScalar,modulate,clock_coordinate,halfWeight]
  ring

theorem dressed_inverse_graph (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    (dressedState ε a p hε ha ψ hψ,trialState ε a p hε ha ψ hψ) ∈ (inverseClockHalf ε).graph :=
  (half_inverse_graph ε hε _ _).mp (trial_to_dressed_graph ε a p hε ha ψ hψ)

theorem dressed_clock_graph (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    (dressedState ε a p hε ha ψ hψ,clockEnergyState ε a p hε ha ψ hψ) ∈ (clockHalf ε).graph := by
  apply (clockHalf_graph ε _ _).mpr
  filter_upwards [productState_coe ε hε _ ψ (dressedScalar_memLp ε a hε ha p) hψ,
    productState_coe ε hε _ ψ (wholeScalar_memLp ε a hε ha p) hψ] with x hd hc
  unfold clockEnergyState dressedState
  rw [hc,hd]
  simp only [weightedFunction,configurationProduct,wholeScalar,dressedScalar,halfScalar,modulate,clock_coordinate,halfWeight]
  have hs : (Real.sqrt (Real.exp x.1+ε):ℂ)^2 = ((Real.exp x.1+ε:ℝ):ℂ) := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt (by positivity)]
  rw [Complex.ofReal_add] at hs
  linear_combination -weight ε x * (Real.fourierChar (p*(coordinateHomeomorph ε hε x).1):ℂ)*
    realTrial ε a (coordinateHomeomorph ε hε x).1 *
    ψ (transverseCoordinates (coordinateHomeomorph ε hε x).2) * hs

theorem trial_exponential_graph (ε a p hbar b : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hb : |-b*hbar| ≤ Real.pi*ε/2) (ψ : TailSpace → ℂ)
    (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2) :
    (trialState ε a p hε ha ψ hψ₂,shiftedState ε a p (-b*hbar) hε ha hb ψ hψ₂) ∈
      (longitudinalExponential ε hε hbar b).graph := by
  apply product_exponential_graph ε hbar b hε _ _ ψ
    (modulate_integrable p _ (realTrial_integrable ε a hε.le ha))
    (modulated_memLp ε a p hε.le ha)
    (shiftedScalar_integrable ε a p (-b*hbar) hε ha hb)
    (shiftedScalar_memLp ε a p (-b*hbar) hε ha hb) hψ₁ hψ₂
  intro k
  rw [shiftedScalar_fourier ε a p (-b*hbar) hε ha hb]
  rw [show -2*Real.pi*k*(-b*hbar) = b*(2*Real.pi*hbar*k) by ring]

#print axioms trialFunction_eq_weighted
#print axioms trialFunction_memLp
#print axioms trialState_coe
#print axioms trialState_toLp
#print axioms clock_coordinate
#print axioms trial_to_dressed_graph
#print axioms dressed_inverse_graph
#print axioms dressed_clock_graph
#print axioms trial_exponential_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorCoreStates
