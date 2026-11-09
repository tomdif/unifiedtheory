/- The actual radial strip operators have reflected adjoints. Cauchy's
estimate gives an O(|h|) difference for the opposite half-clock shifts,
uniform over all real clock and transverse coordinates at fixed cutoffs. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialExponential
import UnifiedTheory.Audit.KFCausalMixedRadialStripReflection
import UnifiedTheory.Audit.KFCausalUnitaryMultiplierPairing
import UnifiedTheory.Audit.KFCausalBoundedStripDifference

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialShiftPairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space FrequencyHilbert)
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates (straightening)
open UnifiedTheory.Audit.KFCausalMixedStripExponentialGraph (unitary)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialExponential (shifted)
open UnifiedTheory.Audit.KFCausalMixedRadialStripFamily
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMultiplier (stripBound)
open UnifiedTheory.Audit.KFCausalStripFamilyExponentialGraph (symbol)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (third_strip_subset)
open UnifiedTheory.Audit.KFCausalMixedRadialStripReflection (family_conj)

variable (ε h δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)

def coordinates : Hilbert ≃ₗᵢ[ℂ] FrequencyHilbert :=
  (unitary ε hε).trans (straightening ε hε)

theorem coordinates_apply (f : Hilbert) :
    coordinates ε hε f = straightening ε hε (unitary ε hε f) := rfl

theorem shifted_coe (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (f : Hilbert) :
    coordinates ε hε (shifted ε h δ v hε hδ y hy f) =ᵐ[volume]
      fun x => symbol (family ε h δ v) y x*(coordinates ε hε f) x := by
  rw [coordinates_apply,coordinates_apply]
  exact KFCausalMixedStripExponentialGraph.action_coe ε hε
    (family ε h δ v) (Real.pi*ε/3) (stripBound ε δ v)
    (family_line_continuous ε h δ v hε) (Real.exp_pos _).le
    (family_bound ε h δ v hε hδ) y hy f

include hε in
theorem symbol_reflection (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (x : Space) :
    starRingEnd ℂ (symbol (family ε h δ (-v)) (-y) x) =
      symbol (family ε h δ v) y x := by
  unfold symbol
  have hq := third_strip_subset ε hε ((x 0:ℂ)+(y:ℂ)*Complex.I) (by simpa using hy)
  have he : (x 0:ℂ)+(-y:ℝ)*Complex.I = starRingEnd ℂ ((x 0:ℂ)+(y:ℂ)*Complex.I) := by
    simp
  rw [he]
  exact family_conj ε h δ v hε _ hq _

theorem shifted_dual (y : ℝ) (hy : |y| ≤ Real.pi*ε/3)
    (hmy : |-y| ≤ Real.pi*ε/3) (f g : Hilbert) :
    inner ℂ f (shifted ε h δ v hε hδ y hy g) =
      inner ℂ (shifted ε h δ (-v) hε hδ (-y) hmy f) g :=
  KFCausalUnitaryMultiplierPairing.inner_dual (coordinates ε hε)
    (shifted ε h δ v hε hδ y hy) (shifted ε h δ (-v) hε hδ (-y) hmy)
    (symbol (family ε h δ v) y) (symbol (family ε h δ (-v)) (-y))
    (shifted_coe ε h δ v hε hδ y hy) (shifted_coe ε h δ (-v) hε hδ (-y) hmy)
    (symbol_reflection ε h δ v hε y hy) f g

theorem shifted_adjoint (y : ℝ) (hy : |y| ≤ Real.pi*ε/3)
    (hmy : |-y| ≤ Real.pi*ε/3) :
    (shifted ε h δ v hε hδ y hy).adjoint = shifted ε h δ (-v) hε hδ (-y) hmy :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    (fun f g => (shifted_dual ε h δ v hε hδ y hy hmy f g).symm)).symm

def responseConstant (ε δ v : ℝ) : ℝ := 2*stripBound ε δ v/(Real.pi*ε/3)

include hε in
theorem responseConstant_nonneg : 0 ≤ responseConstant ε δ v := by
  unfold responseConstant stripBound
  positivity

theorem shifted_difference (hh : |h| ≤ Real.pi*ε/3)
    (hm : |-h/2| ≤ Real.pi*ε/3) (hp : |h/2| ≤ Real.pi*ε/3) (f : Hilbert) :
    ‖shifted ε h δ v hε hδ (-h/2) hm f-shifted ε h δ v hε hδ (h/2) hp f‖ ≤
      (|h| *responseConstant ε δ v)*‖f‖ := by
  apply KFCausalUnitaryMultiplierPairing.difference_bound (coordinates ε hε)
    (shifted ε h δ v hε hδ (-h/2) hm) (shifted ε h δ v hε hδ (h/2) hp)
    (symbol (family ε h δ v) (-h/2)) (symbol (family ε h δ v) (h/2))
    (shifted_coe ε h δ v hε hδ (-h/2) hm) (shifted_coe ε h δ v hε hδ (h/2) hp)
  intro x
  exact (KFCausalBoundedStripDifference.vertical_difference (Real.pi*ε/3) (stripBound ε δ v)
    (by positivity) (fun q => family ε h δ v q (KFCausalEuclideanClockSplit.tail x))
    (family_analytic ε h δ v hε _) (fun q hq => family_bound ε h δ v hε hδ q hq _)
    (x 0) h hh).trans_eq (by unfold responseConstant; ring)

#print axioms coordinates_apply
#print axioms shifted_coe
#print axioms symbol_reflection
#print axioms shifted_dual
#print axioms shifted_adjoint
#print axioms responseConstant_nonneg
#print axioms shifted_difference

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialShiftPairing
