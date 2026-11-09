/- A concrete ten-dimensional family of canonical tests: clock position,
four charged positions, and all five transverse momenta. Neutral position
and clock momentum are deliberately absent from this family. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedChargedTestControl
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockTestControl
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentumTestControl
import UnifiedTheory.Audit.KFCausalCanonicalWeylSumBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalCanonicalTenDirections
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (Frequency operator characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalComplementaryPositionTests (antiDirection positionTest positionTest_canonical)
open UnifiedTheory.Audit.KFCausalComplementaryPhysicalMomenta (physicalDirection)
open UnifiedTheory.Audit.KFCausalComplementaryMomentumTests (momentumTest)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockTestControl (clockTest)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def positionLinear (i : Fin 5) : Configuration →L[ℝ] ℝ :=
  ![positionFrequency 1 0,positionFrequency 0 (antiDirection 0),positionFrequency 0 (antiDirection 1),
    positionFrequency 0 (physicalDirection 0),positionFrequency 0 (physicalDirection 1)] i

def momentumDirection (j : Fin 5) : Transverse :=
  ![physicalDirection 0,physicalDirection 1,physicalDirection 2,antiDirection 0,antiDirection 1] j

def positionAxis (h u : ℝ) (i : Fin 5) : Hilbert ≃ₗᵢ[ℂ] Hilbert := operator volume h (u • positionLinear i,0)
def momentumAxis (h u : ℝ) (j : Fin 5) : Hilbert ≃ₗᵢ[ℂ] Hilbert := operator volume h (0,(0,u • momentumDirection j))

def frequency (q p : Fin 5 → ℝ) : Frequency (X := Configuration) :=
  (∑ i, q i • positionLinear i,∑ j, (0,p j • momentumDirection j))

theorem positionAxis_clock (h u : ℝ) (f : Hilbert) : positionAxis h u 0 f = clockTest h u f := by
  have he : u • positionLinear 0 = positionFrequency u 0 := by
    apply ContinuousLinearMap.ext
    intro x
    simp [positionLinear,positionFrequency,KFCausalPhysicalGaussianConcentration.dot]
  change operator volume h (u • positionLinear 0,0) f = _
  rw [he]
  rfl

theorem axes_control (h ρ δ : ℝ) (f : Hilbert)
    (hc : ∀ u : ℝ, |u| ≤ ρ → ‖clockTest h u f-f‖ < δ)
    (ha : ∀ i : Fin 2, ∀ u : ℝ, |u| ≤ ρ → ‖positionTest u i f-f‖ < δ)
    (hm : ∀ j : Fin 3, ∀ u : ℝ, |u| ≤ ρ → ‖momentumTest h u j f-f‖ < δ)
    (hg : ∀ k i : Fin 2, ∀ u : ℝ, |u| ≤ ρ → ‖KFCausalClockFloorDisplacedChargedTestControl.test h u k i f-f‖ < δ) :
    (∀ i : Fin 5, ∀ u : ℝ, |u| ≤ ρ → ‖positionAxis h u i f-f‖ < δ) ∧
    (∀ j : Fin 5, ∀ u : ℝ, |u| ≤ ρ → ‖momentumAxis h u j f-f‖ < δ) := by
  constructor
  · intro i u hu
    fin_cases i
    · change ‖positionAxis h u 0 f-f‖ < δ
      rw [positionAxis_clock]
      exact hc u hu
    · change ‖operator volume h (u • positionFrequency 0 (antiDirection 0),0) f-f‖ < δ
      rw [← positionTest_canonical]
      exact ha 0 u hu
    · change ‖operator volume h (u • positionFrequency 0 (antiDirection 1),0) f-f‖ < δ
      rw [← positionTest_canonical]
      exact ha 1 u hu
    · exact hg 0 0 u hu
    · exact hg 0 1 u hu
  · intro j u hu
    fin_cases j
    · exact hm 0 u hu
    · exact hm 1 u hu
    · exact hm 2 u hu
    · exact hg 1 0 u hu
    · exact hg 1 1 u hu

theorem simultaneous_bound (h : ℝ) (q p : Fin 5 → ℝ) (f : Hilbert) :
    ‖operator volume h (frequency q p) f-f‖ ≤
      (∑ i, ‖positionAxis h (q i) i f-f‖)+(∑ j, ‖momentumAxis h (p j) j f-f‖) :=
  KFCausalCanonicalWeylSumBounds.canonical_sum_bound volume Finset.univ Finset.univ h
    (fun i => q i • positionLinear i) (fun j => (0,p j • momentumDirection j)) f

theorem simultaneous_small (h ρ δ : ℝ) (q p : Fin 5 → ℝ) (f : Hilbert)
    (hq : ∀ i, |q i| ≤ ρ) (hp : ∀ j, |p j| ≤ ρ)
    (hpos : ∀ i : Fin 5, ∀ u : ℝ, |u| ≤ ρ → ‖positionAxis h u i f-f‖ < δ/10)
    (hmom : ∀ j : Fin 5, ∀ u : ℝ, |u| ≤ ρ → ‖momentumAxis h u j f-f‖ < δ/10) :
    ‖operator volume h (frequency q p) f-f‖ < δ := by
  have ha : (∑ i, ‖positionAxis h (q i) i f-f‖) < ∑ _ : Fin 5, δ/10 :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hpos i (q i) (hq i))
  have hb : (∑ j, ‖momentumAxis h (p j) j f-f‖) < ∑ _ : Fin 5, δ/10 :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hmom j (p j) (hp j))
  have hs := simultaneous_bound h q p f
  norm_num at ha hb
  linarith

#print axioms positionAxis_clock
#print axioms axes_control
#print axioms simultaneous_bound
#print axioms simultaneous_small

end
end UnifiedTheory.Audit.KFCausalCanonicalTenDirections
