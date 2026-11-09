/- The full projected Hamiltonian response has an explicit lower bound
in the actual corrected shear expectations and slope moments. Their
uniform control by Hamiltonian energy remains a separate obligation. -/
import UnifiedTheory.Audit.KFCausalProjectedMatterCommutatorResponse
import UnifiedTheory.Audit.KFCausalProjectedMatterResponseReduction

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedHamiltonianMatterLower
noncomputable section
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState input)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroProjection)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian (factorRate projectedResponse reduced_rate_eq)
open UnifiedTheory.Audit.KFCausalProjectedMatterCommutatorResponse (absorbedLower absorbed_lower)
open UnifiedTheory.Audit.KFCausalProjectedMatterResponseReduction (matterResponse full_lower_by_matter)

theorem full_absorbed_lower (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
    (S : StructuredState) (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    Real.exp (2*t)*(mass2/2*absorbedLower ε h hε hh hb S 0+quartic/4*absorbedLower ε h hε hh hb S 1)-
      ‖zeroProjection h hh (input ε h hε hh S)‖^2/2 ≤
      projectedResponse ε h hε hh hb S mass2 quartic vacuum t := by
  have h0 := absorbed_lower ε h hε hh hb S 0
  have h1 := absorbed_lower ε h hε hh hb S 1
  change absorbedLower ε h hε hh hb S 0 ≤ factorRate ε h hε hh hb S 5 at h0
  change absorbedLower ε h hε hh hb S 1 ≤ factorRate ε h hε hh hb S 6 at h1
  have he := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left h0 (div_nonneg hm (by norm_num : (0:ℝ) ≤ 2)))
      (mul_le_mul_of_nonneg_left h1 (div_nonneg hq (by norm_num : (0:ℝ) ≤ 4)))) (Real.exp_pos (2*t)).le
  have hr := full_lower_by_matter ε h hε hh hb S mass2 quartic vacuum t hm hq hv
  unfold matterResponse at hr
  rw [reduced_rate_eq ε h hε hh hb S 1,reduced_rate_eq ε h hε hh hb S 2] at hr
  exact (sub_le_sub_right he _).trans hr

#print axioms full_absorbed_lower
end
end UnifiedTheory.Audit.KFCausalProjectedHamiltonianMatterLower
