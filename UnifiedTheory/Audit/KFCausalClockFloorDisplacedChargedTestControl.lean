/- The charged Born tails give eventual uniform control of four actual
canonical test directions: symmetric positions and antisymmetric momenta.
The common radius works throughout every finite symmetric time window. -/
import UnifiedTheory.Audit.KFCausalChargedMomentumTests
import UnifiedTheory.Audit.KFCausalL2PhaseTailBound
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedChargedTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedChargedTestControl
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalComplementaryPhysicalMomenta (physicalDirection)
open UnifiedTheory.Audit.KFCausalComplementaryPositionTests (antiDirection)
open UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol (position momentum)
open UnifiedTheory.Audit.KFCausalClockFloorChargedTail (planeTail)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedChargedTail (evolved_plane_tail)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (Frequency characteristic operator)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation (modulation)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def frequency (u : ℝ) (k i : Fin 2) : Frequency (X := Configuration) :=
  if k = 0 then (u • positionFrequency 0 (physicalDirection i.castSucc),0)
  else (0,(0,u • antiDirection i))

def test (h u : ℝ) (k i : Fin 2) : Hilbert ≃ₗᵢ[ℂ] Hilbert := operator volume h (frequency u k i)

def symbol (h : ℝ) (k i : Fin 2) (x : Joint 2 4) : ℝ :=
  if k = 0 then position i x else momentum h i x

theorem symbol_measurable (h : ℝ) (k i : Fin 2) : Measurable (symbol h k i) := by
  unfold symbol
  split
  · unfold position
    fun_prop
  · unfold momentum
    fun_prop

def chargeTest (h u : ℝ) (k i : Fin 2) : JointHilbert 2 4 ≃ₗᵢ[ℂ] JointHilbert 2 4 :=
  modulation volume (fun x => u*symbol h k i x) (measurable_const.mul (symbol_measurable h k i))

theorem test_charge (h u : ℝ) (k i : Fin 2) (f : Hilbert) :
    chargeCoordinates (test h u k i f) = chargeTest h u k i (chargeCoordinates f) := by
  fin_cases k
  · exact KFCausalChargedPositionTests.positionTest_charge h u i f
  · exact KFCausalChargedMomentumTests.momentumTest_charge h u i f

theorem symbol_square_le (h : ℝ) (k i : Fin 2) (x : Joint 2 4) :
    symbol h k i x^2 ≤ momentum h i x^2+position i x^2 := by
  unfold symbol
  split <;> nlinarith [sq_nonneg (momentum h i x),sq_nonneg (position i x)]

theorem test_tail_bound (h u R : ℝ) (hR : 0 ≤ R) (k i : Fin 2) (f : Hilbert) :
    ‖test h u k i f-f‖^2 ≤ u^2*R^2*‖f‖^2+4*planeTail h R i f := by
  rw [← chargeCoordinates.norm_map (test h u k i f-f),map_sub,test_charge,← chargeCoordinates.norm_map f]
  exact KFCausalL2PhaseTailBound.phase_difference_square_tail (symbol h k i)
    (fun x => momentum h i x^2+position i x^2) (symbol_measurable h k i)
    (by unfold momentum position; fun_prop) (symbol_square_le h k i) u R hR (chargeCoordinates f)

theorem characteristic_difference (h u : ℝ) (k i : Fin 2) (f : Hilbert) (hf : ‖f‖ = 1) :
    ‖characteristic volume h f (frequency u k i)-1‖ ≤ ‖test h u k i f-f‖ := by
  have hi : inner ℂ f f = 1 := by rw [inner_self_eq_norm_sq_to_K,hf]; norm_num
  change ‖inner ℂ f (test h u k i f)-1‖ ≤ _
  rw [← hi,← inner_sub_right]
  simpa only [hf,one_mul] using norm_inner_le_norm (𝕜 := ℂ) f (test h u k i f-f)

theorem evolved_test_uniform (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T → ∀ k i : Fin 2,
      ∀ u : ℝ, |u| ≤ ρ →
      ‖test (h n) u k i (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t)-
        evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t‖ < δ := by
  obtain ⟨R,hR,N,hN⟩ := evolved_plane_tail ε a hε ha m g κ s p hm hg hκ
    h hh hb hz T (δ^2/16) (by positivity)
  refine ⟨δ/(2*R),by positivity,N,fun n hn t ht k i u hu => ?_⟩
  let f := evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t
  have hnorm : ‖f‖ = 1 := evolvedState_norm ε a (h n) hε ha (hh n) (hb n) m g κ s p t
  have htail : planeTail (h n) R i f < δ^2/16 := hN n hn t ht i
  have hp : |u| * R ≤ δ/2 := by
    have he := (le_div_iff₀ (by positivity : 0 < 2*R)).mp hu
    nlinarith
  have hs : u^2*R^2 ≤ δ^2/4 := by
    have he := pow_le_pow_left₀ (mul_nonneg (abs_nonneg u) hR.le) hp 2
    simpa only [mul_pow,sq_abs,div_pow,show (2:ℝ)^2 = 4 by norm_num] using he
  have he := test_tail_bound (h n) u R hR.le k i f
  rw [hnorm,one_pow,mul_one] at he
  change ‖test (h n) u k i f-f‖ < δ
  nlinarith [norm_nonneg (test (h n) u k i f-f)]

theorem evolved_characteristic_uniform (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T → ∀ k i : Fin 2,
      ∀ u : ℝ, |u| ≤ ρ →
      ‖characteristic volume (h n) (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t)
        (frequency u k i)-1‖ < δ := by
  obtain ⟨ρ,hρ,N,hN⟩ := evolved_test_uniform ε a hε ha m g κ s p hm hg hκ h hh hb hz T δ hδ
  refine ⟨ρ,hρ,N,fun n hn t ht k i u hu => ?_⟩
  exact (characteristic_difference (h n) u k i _
    (evolvedState_norm ε a (h n) hε ha (hh n) (hb n) m g κ s p t)).trans_lt (hN n hn t ht k i u hu)

#print axioms symbol_measurable
#print axioms test_charge
#print axioms symbol_square_le
#print axioms test_tail_bound
#print axioms characteristic_difference
#print axioms evolved_test_uniform
#print axioms evolved_characteristic_uniform

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedChargedTestControl
