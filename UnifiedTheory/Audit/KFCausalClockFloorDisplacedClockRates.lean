/- Clock-defect expectations of the actual evolved boosted states.
The comparison rate uses the classical coefficient on quantum energy
outputs; it is not yet a classical phase-space transport expectation. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds
import UnifiedTheory.Audit.KFCausalClockFloorStrictQuantumLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution evolution_norm)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState boostedState_norm)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy timeEnergy_actual)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator defectOperator_norm_le)
open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput (classicalOutputLp_pairing_bound)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration)
local notation "w" => referenceState ε a h hε ha hh hb m g κ s p
local notation "E" => timeEnergy ε hε h hh hb m g κ
local notation "U" => evolution ε hε h hh hb m g κ
local notation "f" => boostedState ε a h hε ha hh (positionFrequency (Prod.fst p) (Prod.snd p))

def clockExpectation (t : ℝ) : ℝ := (inner ℂ (U s t f) (defectOperator ε hε (U s t f))).re
def clockRate (t : ℝ) : ℝ := exactRate ε hε h hh hb m g κ s t w
def comparisonRate (t : ℝ) : ℝ := classicalRate ε hε h hh hb m g κ s t w

theorem clockExpectation_derivative (t : ℝ) :
    HasDerivAt (clockExpectation ε a h hε ha hh hb m g κ s p)
      (clockRate ε a h hε ha hh hb m g κ s p t) t := by
  simpa only [referenceState_embedding] using expectation_derivative ε hε h hh hb m g κ s t w

theorem clockExpectation_continuous : Continuous (clockExpectation ε a h hε ha hh hb m g κ s p) :=
  continuous_iff_continuousAt.mpr (fun t => (clockExpectation_derivative ε a h hε ha hh hb m g κ s p t).continuousAt)

theorem clockRate_continuous : Continuous (clockRate ε a h hε ha hh hb m g κ s p) :=
  exactRate_continuous ε hε h hh hb m g κ s w

theorem clockExpectation_integral (r t : ℝ) :
    (∫ u in r..t, clockRate ε a h hε ha hh hb m g κ s p u) =
      clockExpectation ε a h hε ha hh hb m g κ s p t-clockExpectation ε a h hε ha hh hb m g κ s p r := by
  simpa only [referenceState_embedding] using expectation_integral ε hε h hh hb m g κ s r t w

theorem clockExpectation_bounds (t : ℝ) :
    0 ≤ clockExpectation ε a h hε ha hh hb m g κ s p t ∧ clockExpectation ε a h hε ha hh hb m g κ s p t ≤ 1 := by
  have hn : ‖U s t f‖ = 1 := by rw [evolution_norm,boostedState_norm]
  refine ⟨KFCausalClockFloorStrictQuantumLimit.expectation_nonnegative ε hε _,?_⟩
  have he := (KFCausalClockFloorStrictQuantumLimit.expectation_bounds ε hε (U s t f)).2
  have hd := defectOperator_norm_le ε hε (U s t f)
  rw [hn,one_mul] at he
  exact he.trans (hd.trans_eq hn)

theorem comparisonRate_bound (t : ℝ) :
    |comparisonRate ε a h hε ha hh hb m g κ s p t| ≤
      (1/ε)*E t (trajectory ε a h hε ha hh hb m g κ s p t) := by
  have he := classicalOutputLp_pairing_bound ε hε (evolvingOutput ε hε h hh hb m g κ s t w)
  simpa only [evolvingOutput,timeEnergy_actual] using he

theorem rate_error_bound (t : ℝ) :
    |clockRate ε a h hε ha hh hb m g κ s p t-comparisonRate ε a h hε ha hh hb m g κ s p t| ≤
      (20*|h|/ε^2)*E t (trajectory ε a h hε ha hh hb m g κ s p t) :=
  rate_error ε hε h hh hb m g κ s t w

theorem clockRate_bound (t : ℝ) :
    |clockRate ε a h hε ha hh hb m g κ s p t| ≤
      (1/ε+20*|h|/ε^2)*E t (trajectory ε a h hε ha hh hb m g κ s p t) := by
  calc
    _ = |(clockRate ε a h hε ha hh hb m g κ s p t-comparisonRate ε a h hε ha hh hb m g κ s p t)+
        comparisonRate ε a h hε ha hh hb m g κ s p t| := by rw [sub_add_cancel]
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add (rate_error_bound ε a h hε ha hh hb m g κ s p t)
      (comparisonRate_bound ε a h hε ha hh hb m g κ s p t)
    _ = _ := by ring

#print axioms clockExpectation_derivative
#print axioms clockExpectation_continuous
#print axioms clockRate_continuous
#print axioms clockExpectation_integral
#print axioms clockExpectation_bounds
#print axioms comparisonRate_bound
#print axioms rate_error_bound
#print axioms clockRate_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates
