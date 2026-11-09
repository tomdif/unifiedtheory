/- The only unresolved lower response terms are the two ordered matter
factors. Vacuum and kinetic terms are nonnegative; the clock term loses
at most half the projected input norm squared, uniformly in epsilon. -/
import UnifiedTheory.Audit.KFCausalProjectedStructuredVacuumSign
import UnifiedTheory.Audit.KFCausalProjectedClockResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalProjectedMatterResponseReduction
noncomputable section
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState input)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian
  (factorRate reducedRate projectedResponse full_reduced_response)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroProjection)
open UnifiedTheory.Audit.KFCausalProjectedClockResponse (orderedResponse clock_norm_bounds)
open UnifiedTheory.Audit.KFCausalProjectedKineticResponse (kinetic_bounds)
open UnifiedTheory.Audit.KFCausalProjectedStructuredVacuumSign (reduced_vacuum_nonnegative)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)
  (mass2 quartic vacuum t : ℝ)

def matterResponse : ℝ := Real.exp (2*t)*(mass2/2*reducedRate ε h hε hh S 1+
  quartic/4*reducedRate ε h hε hh S 2)

include hb in
theorem matter_le_ordered (hv : 0 ≤ vacuum) :
    matterResponse ε h hε hh S mass2 quartic t ≤ orderedResponse ε h hε hh S mass2 quartic vacuum t := by
  have hvac := mul_nonneg hv (reduced_vacuum_nonnegative ε h hε hh hb S)
  unfold matterResponse orderedResponse
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hvac) (Real.exp_pos _).le

theorem full_lower_by_matter (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    matterResponse ε h hε hh S mass2 quartic t-
      ‖zeroProjection h hh (input ε h hε hh S)‖^2/2 ≤
      projectedResponse ε h hε hh hb S mass2 quartic vacuum t := by
  have h0 := (clock_norm_bounds ε h hε hh hb S).1
  have h1 := (kinetic_bounds ε h hε hh hb S 0).1
  have h2 := (kinetic_bounds ε h hε hh hb S 1).1
  have h3 := (kinetic_bounds ε h hε hh hb S 2).1
  have h4 := (kinetic_bounds ε h hε hh hb S 3).1
  change 0 ≤ factorRate ε h hε hh hb S 1 at h1
  change 0 ≤ factorRate ε h hε hh hb S 2 at h2
  change 0 ≤ factorRate ε h hε hh hb S 3 at h3
  change 0 ≤ factorRate ε h hε hh hb S 4 at h4
  have hp : 0 ≤ Real.exp (2*t)*((factorRate ε h hε hh hb S 3+factorRate ε h hε hh hb S 4)/2+
      vacuum*reducedRate ε h hε hh S 0) :=
    mul_nonneg (Real.exp_pos _).le (add_nonneg (div_nonneg (add_nonneg h3 h4) (by norm_num))
      (mul_nonneg hv (reduced_vacuum_nonnegative ε h hε hh hb S)))
  rw [full_reduced_response ε h hε hh hb S mass2 quartic vacuum t hm hq hv]
  unfold matterResponse
  nlinarith

theorem matterless_lower (hv : 0 ≤ vacuum) :
    -‖zeroProjection h hh (input ε h hε hh S)‖^2/2 ≤
      projectedResponse ε h hε hh hb S 0 0 vacuum t := by
  have he := full_lower_by_matter ε h hε hh hb S 0 0 vacuum t (by norm_num) (by norm_num) hv
  simpa only [matterResponse,zero_div,zero_mul,add_zero,mul_zero,zero_sub,neg_div] using he

#print axioms matter_le_ordered
#print axioms full_lower_by_matter
#print axioms matterless_lower
end
end UnifiedTheory.Audit.KFCausalProjectedMatterResponseReduction
