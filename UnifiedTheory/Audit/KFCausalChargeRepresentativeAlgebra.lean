/- Finite charge-coordinate representative algebra and a four-rotation
criterion for the actual continuous zero-charge projection. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialKineticProfiles
import UnifiedTheory.Audit.KFCausalStandingChargeOperator
import UnifiedTheory.Audit.KFCausalClockFloorChargeClockHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalChargeRepresentativeAlgebra
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates action action_coordinates)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero flowEquiv flow_preserves_volume)
open KFCausalStandingChargeOperator (zeroProjection zeroSector zeroProjection_action zeroProjection_fixes)
open KFCausalIndependentRadialKineticProfiles (fourAverage)

theorem add_coe (f g : Hilbert) (F G : Joint 2 4 → ℂ)
    (hf : chargeCoordinates f =ᵐ[volume] F) (hg : chargeCoordinates g =ᵐ[volume] G) :
    chargeCoordinates (f+g) =ᵐ[volume] fun x => F x+G x := by
  rw [map_add]
  filter_upwards [Lp.coeFn_add (chargeCoordinates f) (chargeCoordinates g),hf,hg] with x ha hf hg
  simpa only [Pi.add_apply,hf,hg] using ha

theorem smul_coe (z : ℂ) (f : Hilbert) (F : Joint 2 4 → ℂ)
    (hf : chargeCoordinates f =ᵐ[volume] F) :
    chargeCoordinates (z • f) =ᵐ[volume] fun x => z*F x := by
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul z (chargeCoordinates f),hf] with x hs hf
  simpa only [Pi.smul_apply,smul_eq_mul,hf] using hs

theorem action_coe (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Hilbert) (F : Joint 2 4 → ℂ)
    (hf : chargeCoordinates f =ᵐ[volume] F) :
    chargeCoordinates (action h hh θ f) =ᵐ[volume] fun x =>
      F (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) θ x) := by
  rw [action_coordinates]
  filter_upwards [KFCausalMixedCircleAction.action_coe (momentumScale h) (momentumScale_ne_zero h hh) θ _,
    (flow_preserves_volume (momentumScale h) (momentumScale_ne_zero h hh) θ).quasiMeasurePreserving.ae hf]
    with x hx hy
  exact hx.trans hy

def four (h : ℝ) (hh : h ≠ 0) (f : Hilbert) : Hilbert :=
  (1/4:ℂ) • (f+action h hh (Real.pi/2) f+action h hh Real.pi f+action h hh (-Real.pi/2) f)

theorem four_coe (h : ℝ) (hh : h ≠ 0) (f : Hilbert) (F : Joint 2 4 → ℂ)
    (hf : chargeCoordinates f =ᵐ[volume] F) :
    chargeCoordinates (four h hh f) =ᵐ[volume]
      fourAverage (momentumScale h) (momentumScale_ne_zero h hh) F :=
  smul_coe _ _ _ (add_coe _ _ _ _ (add_coe _ _ _ _
    (add_coe _ _ _ _ hf (action_coe h hh (Real.pi/2) f F hf))
    (action_coe h hh Real.pi f F hf)) (action_coe h hh (-Real.pi/2) f F hf))

theorem projected_four (h : ℝ) (hh : h ≠ 0) (f : Hilbert) :
    zeroProjection h hh (four h hh f)=zeroProjection h hh f := by
  simp only [four,map_smul,map_add,zeroProjection_action]
  module

theorem projection_of_four (h : ℝ) (hh : h ≠ 0) (f z : Hilbert)
    (hf : four h hh f=z) (hz : z ∈ zeroSector h hh) : zeroProjection h hh f=z := by
  rw [← projected_four,hf,zeroProjection_fixes h hh z hz]

theorem fixed_of_rep (h : ℝ) (hh : h ≠ 0) (f : Hilbert) (F : Joint 2 4 → ℂ)
    (hf : chargeCoordinates f =ᵐ[volume] F)
    (hF : ∀ θ x, F (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) θ x)=F x) :
    f ∈ zeroSector h hh := by
  intro θ
  change action h hh θ f=f
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [action_coe h hh θ f F hf,hf] with x hx hy
  rw [hx,hF,hy]

open KFCausalClockFloorBoundedInverse (inverseL)

theorem four_inverse (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (f : Hilbert) :
    four h hh (inverseL ε hε f)=inverseL ε hε (four h hh f) := by
  simp only [four,map_smul,map_add,KFCausalClockFloorChargeClockHalf.inverseL_action]

theorem inverse_fixed (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (f : Hilbert)
    (hf : f ∈ zeroSector h hh) : inverseL ε hε f ∈ zeroSector h hh := by
  intro θ
  change action h hh θ (inverseL ε hε f)=inverseL ε hε f
  rw [← KFCausalClockFloorChargeClockHalf.inverseL_action]
  exact congrArg (inverseL ε hε) (hf θ)

#print axioms four_inverse
#print axioms inverse_fixed
#print axioms add_coe
#print axioms smul_coe
#print axioms action_coe
#print axioms four_coe
#print axioms projected_four
#print axioms projection_of_four
#print axioms fixed_of_rep
end
end UnifiedTheory.Audit.KFCausalChargeRepresentativeAlgebra
