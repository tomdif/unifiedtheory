/- The exact regularized evolution identity approximates the increments of
any bounded physical observable, with an explicit form-energy error.
No limit of the instantaneous commutator is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorResolventEhrenfest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorResolventBalance
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorResolventTests
open UnifiedTheory.Audit.KFCausalClockFloorResolventEhrenfest

theorem difference_bound (X Y x y : ℂ) :
    ‖(X-Y)-(x-y)‖ ≤ ‖X-x‖+‖Y-y‖ := by
  calc
    _ = ‖(X-x)-(Y-y)‖ := congrArg norm (by ring)
    _ ≤ _ := norm_sub_le _ _

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "E" => timeEnergy ε hε h hne hh m g k

def expectation (D : Hilbert →L[ℂ] Hilbert) (s t : ℝ) (w : V₀) : ℂ :=
  inner ℂ (U s t (J w)) (D (U s t (J w)))

theorem expectation_error (a τ : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert)
    (s t : ℝ) (w : V₀) :
    ‖characteristic ε hε h hne hh m g k a τ D s t w-
      expectation ε hε h hne hh m g k D s t w‖ ≤
        2*‖D‖*‖J w‖*Real.sqrt (E τ (F s t w)/(4*a)) := by
  simpa only [characteristic,expectation,evolution_embedding,formFlow_physical_norm] using
    observable_expectation_error ε hε h hne hh m g k a τ ha D (F s t w)

theorem expectation_unit_error (a τ : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert)
    (hD : ‖D‖ ≤ 1) (s t : ℝ) (w : V₀) (hw : ‖J w‖ = 1)
    (B : ℝ) (hB : E τ (F s t w) ≤ B) :
    ‖characteristic ε hε h hne hh m g k a τ D s t w-
      expectation ε hε h hne hh m g k D s t w‖ ≤ 2*Real.sqrt (B/(4*a)) := by
  have hb := expectation_error ε hε h hne hh m g k a τ ha D s t w
  rw [hw,mul_one] at hb
  have hs := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hB (by positivity : 0 ≤ 4*a))
  exact hb.trans (mul_le_mul (by linarith : 2*‖D‖ ≤ 2) hs
    (Real.sqrt_nonneg _) (by norm_num))

theorem integral_balance_error (a τ : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert)
    (hD : ‖D‖ ≤ 1) (s b c : ℝ) (w : V₀) (hw : ‖J w‖ = 1)
    (B : ℝ) (hb : E τ (F s b w) ≤ B) (hc : E τ (F s c w) ≤ B) :
    ‖(∫ t in b..c, exactRate ε hε h hne hh m g k a τ D s t w)-
      (expectation ε hε h hne hh m g k D s c w-
        expectation ε hε h hne hh m g k D s b w)‖ ≤ 4*Real.sqrt (B/(4*a)) := by
  have hi := expectation_integral ε hε h hne hh m g k a τ D ha s b c w
  have hdiff := difference_bound
    (characteristic ε hε h hne hh m g k a τ D s c w)
    (characteristic ε hε h hne hh m g k a τ D s b w)
    (expectation ε hε h hne hh m g k D s c w)
    (expectation ε hε h hne hh m g k D s b w)
  have htotal := add_le_add
    (expectation_unit_error ε hε h hne hh m g k a τ ha D hD s c w hw B hc)
    (expectation_unit_error ε hε h hne hh m g k a τ ha D hD s b w hw B hb)
  exact (congrArg (fun z : ℂ => ‖z-(expectation ε hε h hne hh m g k D s c w-
    expectation ε hε h hne hh m g k D s b w)‖) hi).le.trans
      (hdiff.trans (htotal.trans_eq (by ring)))

theorem reference_energy_bound (s t : ℝ) (x : V₀) :
    E s x ≤ Real.exp (2*|t-s|)*E t x := by
  by_cases hst : s ≤ t
  · exact (timeEnergy_comparison ε hε h hne hh m g k s t hst x).1.trans
      (le_mul_of_one_le_left (timeEnergy_nonneg ε hε h hne hh m g k t x)
        (Real.one_le_exp (by positivity)))
  · have hts := (not_le.mp hst).le
    simpa only [abs_of_nonpos (sub_nonpos.mpr hts),neg_sub] using
      (timeEnergy_comparison ε hε h hne hh m g k t s hts x).2

#print axioms difference_bound
#print axioms expectation_error
#print axioms expectation_unit_error
#print axioms integral_balance_error
#print axioms reference_energy_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorResolventBalance
