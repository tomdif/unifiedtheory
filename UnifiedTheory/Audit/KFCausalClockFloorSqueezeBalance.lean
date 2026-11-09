/- Exact bounded-squeeze balance along the actual full physical quantum
propagator. The rate is expressed in all eight angle-dependent energy
outputs. No state generator moment or Hamiltonian domain is required. -/
import UnifiedTheory.Audit.KFCausalClockFloorSqueezeEhrenfest
import UnifiedTheory.Audit.KFCausalClockFloorSqueezePairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSqueezeBalance
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (FormSpace)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezePairing
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEhrenfest
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k

def outputRate (a s t : ℝ) (w : V) : ℂ :=
  coefficient h * inner ℂ (timeOutput ε hε h hne hh m g k t (F s t w))
    (differenceOutputLp a (timeOutput ε hε h hne hh m g k t (F s t w)))

theorem exactRate_output (a s t : ℝ) (w : V) :
    exactRate ε hε h hne hh m g k a s t w = outputRate ε hε h hne hh m g k a s t w := by
  unfold exactRate outputRate
  exact congrArg (fun z : ℂ => coefficient h*z)
    (reference_difference ε hε h hne hh m g k a t (F s t w))

theorem bounded_squeeze_derivative (a s t : ℝ) (w : V) :
    HasDerivAt (fun z => characteristic ε hε h hne hh m g k a s z w)
      (outputRate ε hε h hne hh m g k a s t w) t :=
  (expectation_derivative ε hε h hne hh m g k a s t w).congr_deriv
    (exactRate_output ε hε h hne hh m g k a s t w)

theorem outputRate_continuous (a s : ℝ) (w : V) :
    Continuous (fun t => outputRate ε hε h hne hh m g k a s t w) := by
  simpa only [exactRate_output] using exactRate_continuous ε hε h hne hh m g k a s w

theorem bounded_squeeze_integral (a s b c : ℝ) (w : V) :
    (∫ t in b..c, outputRate ε hε h hne hh m g k a s t w) =
      characteristic ε hε h hne hh m g k a s c w-
        characteristic ε hε h hne hh m g k a s b w := by
  simpa only [exactRate_output] using expectation_integral ε hε h hne hh m g k a s b c w

#print axioms exactRate_output
#print axioms bounded_squeeze_derivative
#print axioms outputRate_continuous
#print axioms bounded_squeeze_integral

end
end UnifiedTheory.Audit.KFCausalClockFloorSqueezeBalance
