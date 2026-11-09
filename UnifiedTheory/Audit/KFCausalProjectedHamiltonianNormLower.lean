/- Explicit nonnegative costs bound the full projected response below.
The costs are constructed transported initial norms and slope moments.
Their uniform comparison with Hamiltonian energy is not assumed. -/
import UnifiedTheory.Audit.KFCausalProjectedMatterNormSecant
import UnifiedTheory.Audit.KFCausalProjectedHamiltonianMatterLower

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedHamiltonianNormLower
noncomputable section
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState input)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroProjection)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian (meanInput factorRate projectedResponse)
open UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage (matterIndex)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight (moment moment_bounds)
open UnifiedTheory.Audit.KFCausalMatterScalarAbsorption (coefficient coefficient_nonneg)
open UnifiedTheory.Audit.KFCausalProjectedMatterCommutatorResponse
  (weightedExpectation slopeOutput absorbedLower absorbed_lower)
open UnifiedTheory.Audit.KFCausalProjectedMatterNormSecant (meanInitial projected_secant projected_norm_lower)
open UnifiedTheory.Audit.KFCausalClockSecantMultiplier (operator operator_norm_sq)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)
local notation "M" => operator ε h hε hb hh

def sharpLower (i : Fin 2) : ℝ :=
  (2/ε^2)*(‖M (meanInput ε h hε hh hb S (matterIndex i))‖^2-
    ‖M (meanInitial ε h hε hh hb S pointField i)‖^2)-
      coefficient ε h*moment ε hε (slopeOutput ε h hε hh hb S i)

def normCost (i : Fin 2) : ℝ :=
  (1/(2*ε))*‖meanInitial ε h hε hh hb S pointField i‖^2+
    coefficient ε h*moment ε hε (slopeOutput ε h hε hh hb S i)

theorem sharp_absorbed_lower (i : Fin 2) :
    sharpLower ε h hε hh hb S i ≤ absorbedLower ε h hε hh hb S i := by
  have he := mul_le_mul_of_nonneg_left (projected_secant ε h hε hh hb S i)
    (by positivity : (0:ℝ) ≤ 4/ε^2)
  unfold sharpLower absorbedLower
  convert sub_le_sub_right he (coefficient ε h*moment ε hε (slopeOutput ε h hε hh hb S i)) using 1
  ring

theorem norm_le_sharp (i : Fin 2) : -normCost ε h hε hh hb S i ≤ sharpLower ε h hε hh hb S i := by
  have hn := operator_norm_sq ε h hε hb hh (meanInitial ε h hε hh hb S pointField i)
  have he := mul_le_mul_of_nonneg_left hn (by positivity : (0:ℝ) ≤ 2/ε^2)
  have hs : (2/ε^2)*((ε/4)*‖meanInitial ε h hε hh hb S pointField i‖^2) =
      (1/(2*ε))*‖meanInitial ε h hε hh hb S pointField i‖^2 := by
    field_simp
    ring
  rw [hs] at he
  have hp := mul_nonneg (by positivity : (0:ℝ) ≤ 2/ε^2)
    (sq_nonneg ‖M (meanInput ε h hε hh hb S (matterIndex i))‖)
  unfold normCost sharpLower
  nlinarith only [he,hp]

theorem normCost_nonneg (i : Fin 2) : 0 ≤ normCost ε h hε hh hb S i := by
  have hc := coefficient_nonneg ε hε h
  have hm := (moment_bounds ε hε (slopeOutput ε h hε hh hb S i)).1
  unfold normCost
  positivity

theorem absorbed_norm_lower (i : Fin 2) :
    -normCost ε h hε hh hb S i ≤ absorbedLower ε h hε hh hb S i := by
  have he := mul_le_mul_of_nonneg_left (projected_norm_lower ε h hε hh hb S i)
    (by positivity : (0:ℝ) ≤ 4/ε^2)
  have hs : (4/ε^2)*(-(ε/8)*‖meanInitial ε h hε hh hb S pointField i‖^2) =
      -(1/(2*ε))*‖meanInitial ε h hε hh hb S pointField i‖^2 := by
    field_simp
    ring
  rw [hs] at he
  unfold normCost absorbedLower
  linarith only [he]

theorem matter_norm_lower (i : Fin 2) :
    -normCost ε h hε hh hb S i ≤ factorRate ε h hε hh hb S (matterIndex i) :=
  (absorbed_norm_lower ε h hε hh hb S i).trans (absorbed_lower ε h hε hh hb S i)

theorem full_sharp_lower (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    Real.exp (2*t)*(mass2/2*sharpLower ε h hε hh hb S 0+quartic/4*sharpLower ε h hε hh hb S 1)-
      ‖zeroProjection h hh (input ε h hε hh S)‖^2/2 ≤
      projectedResponse ε h hε hh hb S mass2 quartic vacuum t := by
  have he := mul_le_mul_of_nonneg_left
    (add_le_add
      (mul_le_mul_of_nonneg_left (sharp_absorbed_lower ε h hε hh hb S 0)
        (div_nonneg hm (by norm_num : (0:ℝ) ≤ 2)))
      (mul_le_mul_of_nonneg_left (sharp_absorbed_lower ε h hε hh hb S 1)
        (div_nonneg hq (by norm_num : (0:ℝ) ≤ 4)))) (Real.exp_pos (2*t)).le
  exact (sub_le_sub_right he _).trans
    (KFCausalProjectedHamiltonianMatterLower.full_absorbed_lower
      ε h hε hh hb S mass2 quartic vacuum t hm hq hv)

theorem full_norm_lower (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    -Real.exp (2*t)*(mass2/2*normCost ε h hε hh hb S 0+quartic/4*normCost ε h hε hh hb S 1)-
      ‖zeroProjection h hh (input ε h hε hh S)‖^2/2 ≤
      projectedResponse ε h hε hh hb S mass2 quartic vacuum t := by
  have he := mul_le_mul_of_nonneg_left
    (add_le_add
      (mul_le_mul_of_nonneg_left (absorbed_norm_lower ε h hε hh hb S 0)
        (div_nonneg hm (by norm_num : (0:ℝ) ≤ 2)))
      (mul_le_mul_of_nonneg_left (absorbed_norm_lower ε h hε hh hb S 1)
        (div_nonneg hq (by norm_num : (0:ℝ) ≤ 4)))) (Real.exp_pos (2*t)).le
  have hf := KFCausalProjectedHamiltonianMatterLower.full_absorbed_lower
    ε h hε hh hb S mass2 quartic vacuum t hm hq hv
  linarith only [he,hf]

#print axioms sharp_absorbed_lower
#print axioms norm_le_sharp
#print axioms normCost_nonneg
#print axioms absorbed_norm_lower
#print axioms matter_norm_lower
#print axioms full_sharp_lower
#print axioms full_norm_lower
end
end UnifiedTheory.Audit.KFCausalProjectedHamiltonianNormLower
