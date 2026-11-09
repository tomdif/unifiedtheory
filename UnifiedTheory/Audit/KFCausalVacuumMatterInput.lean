/- One exact interface for the three already constructed vacuum and
matter second outputs. None denotes Q; some j denotes the original
quadratic or quartic reverseFactor-composed-energyFactor operator. -/
import UnifiedTheory.Audit.KFCausalSourcedWidthMatterSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalVacuumMatterInput
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorVacuumSquare (square)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalPhysicalCircleAction (action)
open KFCausalSourcedWidthMatterSquare (matterSecond)
open KFCausalSourcedWidthSecondInput (state)
open KFCausalSingleGaussianMixedSquare (original_strip)
open KFCausalEuclideanProductCoordinates (split)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalNormalizedChargeFlow (momentumScale)

def innerDegree : Option (Fin 2) → ℕ
  | none => 0
  | some j => KFCausalMixedFieldGaussianStrip.degree j

def innerSecond (ε h : ℝ) (hε : 0 < ε) : Option (Fin 2) → Hilbert →ₗ.[ℂ] Hilbert
  | none => square ε hε h
  | some j => matterSecond ε h j hε

variable (ε h a w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w) (hb : |h| ≤ ε/10)
local notation "hb₀" => original_strip ε h hε hb

def innerOutput : Option (Fin 2) → Hilbert
  | none => KFCausalSourcedWidthSecondInput.firstOutput ε h a w C p b P hε hh ha hw hb₀
  | some j => KFCausalSourcedWidthMatterSquare.firstOutput ε h a w C p b P j hε hh ha hw hb

theorem inner_graph (i : Option (Fin 2)) :
    (state ε h a w C p b P hε hh ha hw,innerOutput ε h a w C p b P hε hh ha hw hb i) ∈
      (innerSecond ε h hε i).graph := by
  cases i with
  | none => exact KFCausalSourcedWidthSecondInput.first_graph ε h a w C p b P hε hh ha hw hb₀
  | some j => exact KFCausalSourcedWidthMatterSquare.first_graph ε h a w C p b P j hε hh ha hw hb

theorem rotated_second_input_coe (i : Option (Fin 2)) (θ : ℝ) :
    clockMixed ε hε (inverseL ε hε (action h hh θ
      (innerOutput ε h a w C p b P hε hh ha hw hb i))) =ᵐ[volume]
      fun x => KFCausalMatterInsertionCoordinate.coefficient ε h (groundWidth h) w
        (momentumScale h) θ (x.2 0:ℂ) ((split 2 4).symm x)^innerDegree i*
        KFCausalWidthGaussianNeutralMultiplier.numerator ε h a (groundWidth h) w
          (momentumScale h) θ C p b P (x.2 0:ℂ) ((split 2 4).symm x) := by
  cases i with
  | none =>
      simpa only [innerDegree,pow_zero,one_mul,innerOutput] using
        KFCausalSourcedWidthNormalizedDensity.rotated_second_input_coe ε hε h a w C p b P hh hw ha hb₀ θ
  | some j =>
      exact KFCausalSourcedWidthMatterSecondInput.rotated_second_input_coe ε h a w C p b P hε hh ha hw hb₀ θ j

#print axioms inner_graph
#print axioms rotated_second_input_coe
end
end UnifiedTheory.Audit.KFCausalVacuumMatterInput
