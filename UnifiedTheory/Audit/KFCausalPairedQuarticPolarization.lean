/- Exact finite directional polarization of the corrected quartic.
It supplies source-integral operator witnesses without assuming
domain membership of a polynomial multiplier. -/
import UnifiedTheory.Audit.KFCausalQuarticChargeProfiles
import UnifiedTheory.Audit.KFCausalDirectionalGaussianDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace UnifiedTheory.Audit.KFCausalPairedQuarticPolarization
noncomputable section
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalDirectionalGaussianStates (linearForm)
open KFCausalQuarticChargeProfiles (quarticPolynomial chargedRadius)
open KFCausalChargedPairCoordinates (pairPolynomial)

def directions : Fin 21 → Transverse :=
  ![![1,1,0,0,0],![1,-1,0,0,0],![0,0,1,1,0],![0,0,1,-1,0],
    ![1,0,0,0,0],![0,1,0,0,0],![0,0,1,0,0],![0,0,0,1,0],
    ![1,1,1,1,0],![1,1,1,-1,0],![1,1,-1,1,0],![1,1,-1,-1,0],
    ![1,-1,1,1,0],![1,-1,1,-1,0],![1,-1,-1,1,0],![1,-1,-1,-1,0],
    ![1,0,0,0,0],![0,1,0,0,0],![0,0,1,0,0],![0,0,0,1,0],![0,0,0,0,0]]
def degrees : Fin 21 → ℕ := ![4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,2,2,2,2,0]
def coefficients (α : ℝ) : Fin 21 → ℂ :=
  ![1/12,1/12,1/12,1/12,-1/6,-1/6,-1/6,-1/6,
    -1/96,1/96,1/96,-1/96,1/96,-1/96,-1/96,1/96,
    -1/(4*α),-1/(4*α),-1/(4*α),-1/(4*α),1/(8*(α:ℂ)^2)]

theorem polarization (α : ℝ) (q : Transverse) :
    (∑ i, coefficients α i*(linearForm (directions i) q:ℂ)^(degrees i)) =
      (quarticPolynomial α q:ℂ) := by
  simp [coefficients,directions,degrees,linearForm,Fin.sum_univ_succ,
    quarticPolynomial,chargedRadius,pairPolynomial]
  ring

#print axioms polarization
end
end UnifiedTheory.Audit.KFCausalPairedQuarticPolarization
