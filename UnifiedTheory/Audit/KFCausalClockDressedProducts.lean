/- Clock-dressed product states in the actual physical Hilbert space.
The coordinate formula and Gaussian clock moments prove their L2 membership. -/
import UnifiedTheory.Audit.KFCausalClockTrialWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockDressedProducts
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalCoupledProductDomain
open UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
open UnifiedTheory.Audit.KFCausalDampedProductDomain
open UnifiedTheory.Audit.KFCausalClockTrialWeights

def clockFunction (ε a p b : ℝ) (ψ : TailSpace → ℂ) (z : Configuration) : ℂ :=
  (Real.exp (b*z.1):ℂ)*trialFunction ε a p ψ z

def clockProduct (ε a p b : ℝ) (hε : 0 < ε) (ψ : TailSpace → ℂ)
    (hb : MemLp (clockTrial ε a hε p b) 2) (hψ : MemLp ψ 2) : Hilbert :=
  productState ε hε (clockTrial ε a hε p b) ψ hb hψ

theorem clockFunction_eq_weighted (ε a p b : ℝ) (hε : 0 < ε) (ψ : TailSpace → ℂ) :
    clockFunction ε a p b ψ = weightedFunction ε hε (configurationProduct (clockTrial ε a hε p b) ψ) := by
  funext z
  have hs : (chartIso ε hε).symm (chart ε z.1)=z.1 := (chartIso ε hε).symm_apply_apply _
  simp only [clockFunction,trialFunction_eq_weighted ε a p hε ψ,weightedFunction,
    configurationProduct,coordinateHomeomorph_apply,clockTrial,hs]
  ring

theorem clockFunction_memLp (ε a p b : ℝ) (hε : 0 < ε) (ψ : TailSpace → ℂ)
    (hb : MemLp (clockTrial ε a hε p b) 2) (hψ : MemLp ψ 2) :
    MemLp (clockFunction ε a p b ψ) 2 := by
  rw [clockFunction_eq_weighted ε a p b hε ψ]
  exact weighted_memLp ε hε _ (configuration_memLp _ ψ hb hψ)

theorem clockProduct_coe (ε a p b : ℝ) (hε : 0 < ε) (ψ : TailSpace → ℂ)
    (hb : MemLp (clockTrial ε a hε p b) 2) (hψ : MemLp ψ 2) :
    clockProduct ε a p b hε ψ hb hψ =ᵐ[volume] clockFunction ε a p b ψ := by
  rw [clockFunction_eq_weighted ε a p b hε ψ]
  exact productState_coe ε hε _ ψ hb hψ

theorem clockProduct_toLp (ε a p b : ℝ) (hε : 0 < ε) (ψ : TailSpace → ℂ)
    (hb : MemLp (clockTrial ε a hε p b) 2) (hψ : MemLp ψ 2) :
    clockProduct ε a p b hε ψ hb hψ =
      (clockFunction_memLp ε a p b hε ψ hb hψ).toLp (clockFunction ε a p b ψ) := by
  apply Lp.ext
  exact (clockProduct_coe ε a p b hε ψ hb hψ).trans (clockFunction_memLp ε a p b hε ψ hb hψ).coeFn_toLp.symm

theorem clockProduct_norm_square (ε a p b : ℝ) (hε : 0 < ε) (ψ : TailSpace → ℂ)
    (hb : MemLp (clockTrial ε a hε p b) 2) (hψ : MemLp ψ 2) :
    ‖clockProduct ε a p b hε ψ hb hψ‖^2 =
      (∫ q, ‖clockTrial ε a hε p b q‖^2)*(∫ y, ‖ψ y‖^2) :=
  productState_norm_square ε hε _ ψ hb hψ

def dressedState (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a) (ψ : TailSpace → ℂ)
    (hψ : MemLp ψ 2) : Hilbert := clockProduct ε a p (1/2) hε ψ (clockTrial_half_memLp ε a hε ha p) hψ

def clockEnergyState (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a) (ψ : TailSpace → ℂ)
    (hψ : MemLp ψ 2) : Hilbert := clockProduct ε a p 1 hε ψ (clockTrial_one_memLp ε a hε ha p) hψ

#print axioms clockFunction_eq_weighted
#print axioms clockFunction_memLp
#print axioms clockProduct_coe
#print axioms clockProduct_toLp
#print axioms clockProduct_norm_square

end
end UnifiedTheory.Audit.KFCausalClockDressedProducts
