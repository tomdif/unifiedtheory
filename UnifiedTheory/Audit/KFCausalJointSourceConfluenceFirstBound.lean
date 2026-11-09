/- The first genuine joint width/source jet inherits the state-independent
two-width response constant. No higher-order uniform bound is asserted. -/
import UnifiedTheory.Audit.KFCausalJointSourceConfluenceLimit
import UnifiedTheory.Audit.KFCausalTwoWidthIntegratedResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalJointSourceConfluenceFirstBound
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalJointSourceConfluenceProfiles (widths sources coefficients)
open KFCausalJointSourceConfluenceFactors (limitDensity limitResponse)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)

theorem actual_first_bound (α β w0 ε y s : ℝ) (b ℓ : ℂ) (P : Polynomial ℂ)
    (hw0 : 1 ≤ w0) (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    (∫ p, limitResponse 1 α β w0 (scale ε y s) (deriv (scale ε y) s) b ℓ P p ∂jointMeasure) ≤
      ((48+82944/α)*fraction ε s)*
        ∫ p, limitDensity 1 α β w0 (scale ε y s) b ℓ P p ∂jointMeasure := by
  apply le_of_tendsto_of_tendsto
    (KFCausalJointSourceConfluenceLimit.actual_response_tendsto
      1 α β w0 ε y s b ℓ P hw0 hα hβ hwidth hε hy)
    ((KFCausalJointSourceConfluenceLimit.actual_energy_tendsto
      1 α β w0 ε y s b ℓ P hw0 hα hβ hwidth hε hy).const_mul
        ((48+82944/α)*fraction ε s))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hb := KFCausalTwoWidthIntegratedResponse.actual_integral_bound 2 α β ε y s
    (widths 1 w0 δ) id (sources 1 δ b ℓ) (coefficients 1 w0 δ) (fun _ => P)
    hα hβ hwidth hε hy
    (KFCausalJointSourceConfluenceProfiles.widths_admissible 1 w0 δ hw0 hδ.le)
  simpa only [Function.comp_id] using hb

#print axioms actual_first_bound
end
end UnifiedTheory.Audit.KFCausalJointSourceConfluenceFirstBound
