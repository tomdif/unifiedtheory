/- The neutral Hermite multiplier used in the numerical trial family is
an actual admissible physical polynomial Gaussian, at every degree.
This treats the packet before charge projection. It does not identify
the projected response matrices or assert a uniform response bound. -/
import UnifiedTheory.Audit.KFCausalPolynomialGaussianDomain
import UnifiedTheory.Audit.KFCausalHermitePolynomials

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNeutralHermiteDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth clockFunction)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative (physicalProfile)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (commonEnergyDomain)
open UnifiedTheory.Audit.KFCausalPolynomialGaussianDomain


variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (B : ℝ) (n : ℕ)

def state : Hilbert :=
  input ε a h hε ha hh C p b 4 (multiplier (neutralWidth h) B n)

theorem state_coe :
    state ε a h hε ha hh C p b B n =ᵐ[volume] fun x : Configuration =>
      ((physicistsHermite n).eval
        ((Real.sqrt (2*neutralWidth h):ℂ)*((x.2 4:ℂ)-(B:ℂ)))/
          (Real.sqrt ((2:ℝ)^n*n.factorial):ℂ))*
      physicalProfile C p (groundWidth h) (neutralWidth h) b (clockFunction ε a) x := by
  filter_upwards [input_coe ε a h hε ha hh C p b 4 (multiplier (neutralWidth h) B n)] with x hx
  exact hx.trans (congrArg (fun z => z*
    physicalProfile C p (groundWidth h) (neutralWidth h) b (clockFunction ε a) x)
      (multiplier_eval (neutralWidth h) B n (x.2 4:ℂ)))

theorem state_commonEnergyDomain (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    state ε a h hε ha hh C p b B n ∈ commonEnergyDomain ε hε h v l :=
  input_commonEnergyDomain ε a h hε ha hh C p b 4 hb (multiplier (neutralWidth h) B n) v l

#print axioms physicistsHermite_zero
#print axioms physicistsHermite_one
#print axioms physicistsHermite_recurrence
#print axioms multiplier_eval
#print axioms state_coe
#print axioms state_commonEnergyDomain
end
end UnifiedTheory.Audit.KFCausalNeutralHermiteDomain
