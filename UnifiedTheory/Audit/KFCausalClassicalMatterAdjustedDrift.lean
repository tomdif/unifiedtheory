/- The uniform weighted-tilt estimate yields a monotone corrected
longitudinal quantity. The correction is a proof device, not a new field. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterTiltControl
import UnifiedTheory.Audit.KFCausalClassicalMatterDefect
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterAdjustedDrift
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum (kineticMean kineticMean_nonnegative)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect

theorem correctedRate_nonnegative (ε m g κ N t s p : ℝ) (hε : 0 < ε) (z : Phase)
    (hT : -N*weightedMean m g κ (clock ε s) z ≤
      weightedMean m g κ (clock ε s) z+weightedTilt m g κ (clock ε s) z) :
    0 ≤ longitudinalRate ε m g κ t z s p+
      N*(response ε s*clockRate ε m g κ t z s p)+1/2 := by
  have hc := clock_positive ε s hε.le
  have hr := response_bounds ε s hε
  have ha : 0 ≤ amplitude ε t s p := (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_left hT ha
  have hn : 0 ≤ kineticMean t z+amplitude ε t s p*
      (weightedMean m g κ (clock ε s) z+weightedTilt m g κ (clock ε s) z)+
        N*amplitude ε t s p*weightedMean m g κ (clock ε s) z := by
    nlinarith only [h,kineticMean_nonnegative t z]
  have hp := mul_nonneg (div_nonneg hr.1.le (sq_nonneg (clock ε s))) hn
  have he : longitudinalRate ε m g κ t z s p+
      N*(response ε s*clockRate ε m g κ t z s p)+1/2 =
      (response ε s/(clock ε s)^2)*
        (kineticMean t z+amplitude ε t s p*
          (weightedMean m g κ (clock ε s) z+weightedTilt m g κ (clock ε s) z)+
            N*amplitude ε t s p*weightedMean m g κ (clock ε s) z)+(1-response ε s)/2 := by
    unfold longitudinalRate clockRate
    ring
  rw [he]
  linarith only [hp,hr.2]

variable (ε m g κ τ : ℝ) (hε : 0 < ε) (z : ℝ → Phase) (s p : ℝ → ℝ)
  (hs : ∀ t, HasDerivAt s (clockRate ε m g κ (t+τ) (z t) (s t) (p t)) t)
  (hp : ∀ t, HasDerivAt p (momentumRate ε m g κ (t+τ) (z t) (s t) (p t)) t)

include hε hs hp in
theorem longitudinal_derivative (t : ℝ) :
    HasDerivAt (fun u => p u/clock ε (s u))
      (longitudinalRate ε m g κ (t+τ) (z t) (s t) (p t)) t := by
  have hc := (clock_positive ε (s t) hε.le).ne'
  have h := (hp t).div ((hs t).exp.add_const ε) hc
  convert h using 1
  rw [longitudinalRate_eq ε m g κ (t+τ) hε.le (z t) (s t) (p t)]
  change _ = (momentumRate ε m g κ (t+τ) (z t) (s t) (p t)*clock ε (s t)-
    p t*(Real.exp (s t)*clockRate ε m g κ (t+τ) (z t) (s t) (p t)))/(clock ε (s t))^2
  field_simp

include hε hs in
theorem logClock_derivative (t : ℝ) :
    HasDerivAt (fun u => Real.log (clock ε (s u)))
      (response ε (s t)*clockRate ε m g κ (t+τ) (z t) (s t) (p t)) t := by
  have h := ((hs t).exp.add_const ε).log (clock_positive ε (s t) hε.le).ne'
  convert h using 1
  unfold response clock
  ring

include hε hs hp in
theorem corrected_monotone (N : ℝ)
    (hT : ∀ (C : ℝ) (w : Phase), -N*weightedMean m g κ C w ≤
      weightedMean m g κ C w+weightedTilt m g κ C w) :
    Monotone (fun t => p t/clock ε (s t)+N*Real.log (clock ε (s t))+t/2) := by
  have hd (t : ℝ) := ((longitudinal_derivative ε m g κ τ hε z s p hs hp t).add
    ((logClock_derivative ε m g κ τ hε z s p hs t).const_mul N)).add
    ((hasDerivAt_id t).div_const 2)
  apply monotone_of_hasDerivAt_nonneg (fun t => hd t)
  intro t
  exact correctedRate_nonnegative ε m g κ N (t+τ) (s t) (p t) hε (z t) (hT _ _)

include hε hs hp in
theorem corrected_linear_lower (N : ℝ)
    (hT : ∀ (C : ℝ) (w : Phase), -N*weightedMean m g κ C w ≤
      weightedMean m g κ C w+weightedTilt m g κ C w) (t : ℝ) (ht : 0 ≤ t) :
    p 0/clock ε (s 0)+N*Real.log (clock ε (s 0))-t/2 ≤
      p t/clock ε (s t)+N*Real.log (clock ε (s t)) := by
  have h := corrected_monotone ε m g κ τ hε z s p hs hp N hT ht
  dsimp only at h
  linarith only [h]

#print axioms correctedRate_nonnegative
#print axioms longitudinal_derivative
#print axioms logClock_derivative
#print axioms corrected_monotone
#print axioms corrected_linear_lower

end
end UnifiedTheory.Audit.KFCausalClassicalMatterAdjustedDrift

