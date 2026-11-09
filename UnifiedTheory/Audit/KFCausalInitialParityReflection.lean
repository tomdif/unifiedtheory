/- Reflection of the four charged physical coordinates, with clock and
neutral coordinate fixed. It is an actual L2 unitary. The path-zero
Gaussian profile transforms by the corresponding source reflection. -/
import UnifiedTheory.Audit.KFCausalStructuredShearMean
import Mathlib.MeasureTheory.Constructions.Pi

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalInitialParityReflection
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback (unitaryPullback unitaryPullback_coe)
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation (path path_zero)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile exponent position)

def coordinate (i : Fin 5) : ℝ ≃ᵐ ℝ :=
  if i=4 then MeasurableEquiv.refl ℝ else (Homeomorph.neg ℝ).toMeasurableEquiv

def reflection : Configuration ≃ᵐ Configuration :=
  (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piCongrRight coordinate)

theorem reflection_apply (x : Configuration) : reflection x =
    (x.1,fun i => if i=4 then x.2 i else -x.2 i) := by
  apply Prod.ext
  · rfl
  · funext i
    change coordinate i (x.2 i) = if i=4 then x.2 i else -x.2 i
    by_cases hi : i=4 <;> simp [coordinate,hi]

theorem reflection_preserving : MeasurePreserving reflection := by
  have hc (i : Fin 5) : MeasurePreserving (coordinate i) := by
    by_cases hi : i=4
    · simpa only [coordinate,if_pos hi] using (MeasurePreserving.id (volume : Measure ℝ))
    · simpa only [coordinate,if_neg hi] using (Measure.measurePreserving_neg (volume : Measure ℝ))
  exact (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_pi hc)

def operator : Hilbert ≃ₗᵢ[ℂ] Hilbert := unitaryPullback reflection reflection_preserving

theorem operator_coe (f : Hilbert) : operator f =ᵐ[volume] fun x => f (reflection x) :=
  unitaryPullback_coe _ _ f

def sourceReflection (b : Fin 5 → ℂ) (i : Fin 5) : ℂ := if i=4 then b i else -b i

theorem initial_profile (A D : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) :
    path A D α β b 0 (reflection x) = path A D α β (sourceReflection b) 0 x := by
  rw [path_zero,path_zero,reflection_apply]
  unfold profile exponent
  congr 2
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i=4 <;> simp [position,sourceReflection,hi]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i=4 <;> simp [position,hi]

#print axioms reflection_apply
#print axioms reflection_preserving
#print axioms operator_coe
#print axioms initial_profile
end
end UnifiedTheory.Audit.KFCausalInitialParityReflection
