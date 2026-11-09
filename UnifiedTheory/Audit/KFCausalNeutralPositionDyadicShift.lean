/- A cancellation-preserving bound for the actual averaged physical
half-clock-shift operators. Every term is an already constructed radial
operator; the Hamiltonian and its domains are unchanged. -/
import UnifiedTheory.Audit.KFCausalMixedDyadicStripResponse
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialShiftPairing
import UnifiedTheory.Audit.KFCausalFiniteMultiplierAverage

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionDyadicShift
noncomputable section
open MeasureTheory
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space)
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit (tail)
open UnifiedTheory.Audit.KFCausalDyadicHeatCancellation (width width_pos)
open UnifiedTheory.Audit.KFCausalMixedDyadicStripResponse
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialExponential (shifted)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialShiftPairing (coordinates shifted_coe)
open UnifiedTheory.Audit.KFCausalFiniteMultiplierAverage (mean operator_mean_apply isometry_mean_representation)
open UnifiedTheory.Audit.KFCausalMixedRadialStripFamily (family)
open UnifiedTheory.Audit.KFCausalStripFamilyExponentialGraph (symbol)

variable (ε h δ v : ℝ) (N : ℕ) (hε : 0 < ε) (hδ : 0 < δ)

def action (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) : Hilbert →L[ℂ] Hilbert :=
  (N:ℂ)⁻¹ • ∑ j ∈ Finset.range N, shifted ε h (width δ j) v hε (width_pos δ hδ j) y hy

theorem action_apply (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (f : Hilbert) :
    action ε h δ v N hε hδ y hy f =
      mean N (fun j => shifted ε h (width δ j) v hε (width_pos δ hδ j) y hy f) := by
  exact operator_mean_apply N _ f

#print axioms action_apply

theorem action_coe (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (f : Hilbert) :
    coordinates ε hε (action ε h δ v N hε hδ y hy f) =ᵐ[volume]
      fun x => familyAverage ε h δ v N ((x 0:ℂ)+(y:ℂ)*Complex.I) (tail x)*coordinates ε hε f x := by
  have H := isometry_mean_representation (coordinates ε hε) N
    (fun j => shifted ε h (width δ j) v hε (width_pos δ hδ j) y hy f)
    (fun j x => symbol (family ε h (width δ j) v) y x*coordinates ε hε f x)
    (fun j => shifted_coe ε h (width δ j) v hε (width_pos δ hδ j) y hy f)
  have he := congrArg (fun g : Hilbert => ((coordinates ε hε g) : Space → ℂ))
    (action_apply ε h δ v N hε hδ y hy f)
  refine (Filter.EventuallyEq.of_eq he).trans ?_
  filter_upwards [H] with x hx
  rw [hx]
  simp only [familyAverage,symbol,Finset.sum_mul,mul_assoc]

#print axioms action_coe

theorem action_difference (hN : 0 < N) (hh : |h| ≤ 2*Real.pi*ε/3)
    (hm : |-h/2| ≤ Real.pi*ε/3) (hp : |h/2| ≤ Real.pi*ε/3) (f : Hilbert) :
    ‖action ε h δ v N hε hδ (-h/2) hm f-action ε h δ v N hε hδ (h/2) hp f‖ ≤
      (|h| *responseConstant ε δ v N)*‖f‖ := by
  apply KFCausalUnitaryMultiplierPairing.difference_bound (coordinates ε hε)
    (action ε h δ v N hε hδ (-h/2) hm) (action ε h δ v N hε hδ (h/2) hp)
    (fun x => familyAverage ε h δ v N ((x 0:ℂ)+(-h/2:ℝ)*Complex.I) (tail x))
    (fun x => familyAverage ε h δ v N ((x 0:ℂ)+(h/2:ℝ)*Complex.I) (tail x))
    (action_coe ε h δ v N hε hδ (-h/2) hm) (action_coe ε h δ v N hε hδ (h/2) hp)
  intro x
  exact (family_vertical_difference ε h δ v N hε hδ hN (x 0) h hh (tail x)).trans_eq (by ring)

#print axioms action_difference

end
end UnifiedTheory.Audit.KFCausalNeutralPositionDyadicShift
