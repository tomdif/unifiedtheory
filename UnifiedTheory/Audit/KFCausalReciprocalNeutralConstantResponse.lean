/- Clock and kinetic response bounds for actual finite reciprocal packets
with constant neutral polynomials and arbitrary complex sources. The clock
output's extra momentum domain is constructed, rather than hypothesized. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralConstantClockComposition
import UnifiedTheory.Audit.KFCausalReciprocalNeutralKineticResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralConstantResponse
noncomputable section
open KFCausalReciprocalNeutralSuperposition
open KFCausalReciprocalNeutralKineticResponse
open KFCausalReciprocalNeutralConstantClockComposition (finite_clock_graph)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "f" => state n ε h a w p C b (fun _ => 1) hε ha hh hw
local notation "Bf" => momentum n ε h a w p C b (fun _ => 1) hε ha hh hw
local notation "u" => output n ε h a w p C b (fun _ => 1) hε ha hh hw hb
local notation "v" => momentumOutput n ε h a w p C b (fun _ => 1) hε ha hh hw hb
local notation "E" => factorEnergy n ε h a w p C b (fun _ => 1) hε ha hh hw hb
local notation "R" => factorRate n ε h a w p C b (fun _ => 1) hε ha hh hw hb

theorem clock_response : R 0 = -KFCausalClockFloorPureClockKineticResponse.response ε hε (u 0) :=
  KFCausalClockFloorPureClockClockResponse.weak_response ε hε h hh f (u 0) Bf (v 0) _
    (output_graph n ε h a w p C b (fun _ => 1) hε ha hh hw hb 0)
    (momentum_graph n ε h a w p C b (fun _ => 1) hε ha hh hw)
    (momentumOutput_graph n ε h a w p C b (fun _ => 1) hε ha hh hw hb 0)
    (finite_clock_graph n ε h a w p C b hε ha hh hw hb)

theorem clock_energy_bounds : -(1/(4*ε))*E 0 ≤ R 0 ∧ R 0 ≤ 0 := by
  rw [clock_response]
  exact KFCausalClockFloorPureClockClockResponse.response_bounds ε hε f (u 0)

theorem clockKinetic_lower (t : ℝ) :
    -(1/(4*ε))*clockKineticEnergy n ε h a w p C b (fun _ => 1) hε ha hh hw hb t ≤
      clockKineticResponse n ε h a w p C b (fun _ => 1) hε ha hh hw hb t := by
  have h0 := (clock_energy_bounds n ε h a w p C b hε ha hh hw hb).1
  have h1 := (kinetic_bounds n ε h a w p C b (fun _ => 1) hε ha hh hw hb 0).1
  have h2 := (kinetic_bounds n ε h a w p C b (fun _ => 1) hε ha hh hw hb 1).1
  have h3 := (kinetic_bounds n ε h a w p C b (fun _ => 1) hε ha hh hw hb 2).1
  have h4 := (kinetic_bounds n ε h a w p C b (fun _ => 1) hε ha hh hw hb 3).1
  change 0 ≤ R 1 at h1
  change 0 ≤ R 2 at h2
  change 0 ≤ R 3 at h3
  change 0 ≤ R 4 at h4
  have hc : 0 ≤ 1/(4*ε) := by positivity
  have he : E 0/2 ≤ clockKineticEnergy n ε h a w p C b (fun _ => 1) hε ha hh hw hb t := by
    have hs : 0 ≤ (E 1+E 2)/2 := by unfold factorEnergy; positivity
    have hg : 0 ≤ Real.exp (2*t)*(E 3+E 4)/2 := by unfold factorEnergy; positivity
    unfold clockKineticEnergy
    linarith
  have hr : -(1/(4*ε))*(E 0/2) ≤ clockKineticResponse n ε h a w p C b (fun _ => 1) hε ha hh hw hb t := by
    have hg := mul_nonneg (Real.exp_pos (2*t)).le (add_nonneg h3 h4)
    unfold clockKineticResponse
    linarith
  exact (mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hc)).trans hr

#print axioms clock_response
#print axioms clock_energy_bounds
#print axioms clockKinetic_lower
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralConstantResponse
