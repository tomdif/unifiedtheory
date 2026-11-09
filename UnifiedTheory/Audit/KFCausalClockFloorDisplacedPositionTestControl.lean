/- Existing evolved complementary tails imply eventual uniform norm
continuity at zero of the actual canonical antisymmetric position tests
throughout finite time windows. No unweighted moment is assumed. -/
import UnifiedTheory.Audit.KFCausalComplementaryPositionTests
import UnifiedTheory.Audit.KFCausalL2PhaseTailBound
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedComplementaryTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedPositionTestControl
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit (dualPhysical)
open UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol
open UnifiedTheory.Audit.KFCausalComplementaryPositionTests
open UnifiedTheory.Audit.KFCausalClockFloorComplementaryTail
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedComplementaryTail
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (characteristic operator)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem positionTest_tail_bound (h u R : ℝ) (hR : 0 ≤ R) (i : Fin 2) (f : Hilbert) :
    ‖positionTest u i f-f‖^2 ≤ u^2*R^2*‖f‖^2+4*complementaryTail h R i f := by
  rw [← dualPhysical.norm_map (positionTest u i f-f),map_sub,positionTest_dual,
    ← dualPhysical.norm_map f]
  apply KFCausalL2PhaseTailBound.phase_difference_square_tail
    (complementaryPosition i) (complementarySquare h i) (by unfold complementaryPosition; fun_prop)
    (complementarySquare_continuous h i).measurable ?_ u R hR (dualPhysical f)
  intro x
  unfold complementarySquare
  nlinarith [sq_nonneg (complementaryMomentum h i x),sq_nonneg (neutralTerm h i x)]

theorem positionCharacteristic_difference (h u : ℝ) (i : Fin 2) (f : Hilbert) (hf : ‖f‖ = 1) :
    ‖characteristic volume h f (u • positionFrequency 0 (antiDirection i),0)-1‖ ≤
      ‖positionTest u i f-f‖ := by
  have hi : inner ℂ f f = 1 := by rw [inner_self_eq_norm_sq_to_K,hf]; norm_num
  unfold characteristic
  rw [← positionTest_canonical,← hi,← inner_sub_right]
  simpa only [hf,one_mul] using norm_inner_le_norm (𝕜 := ℂ) f (positionTest u i f-f)

theorem evolved_positionTest_uniform (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T → ∀ i : Fin 2,
      ∀ u : ℝ, |u| ≤ ρ →
      ‖positionTest u i (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t)-
        evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t‖ < δ := by
  obtain ⟨R,hR,N,hN⟩ := evolved_complementary_tail ε a hε ha m g κ s p hm hg hκ
    h hh hb hz T (δ^2/16) (by positivity)
  refine ⟨δ/(2*R),by positivity,N,fun n hn t ht i u hu => ?_⟩
  let f := evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t
  have hnorm : ‖f‖ = 1 := evolvedState_norm ε a (h n) hε ha (hh n) (hb n) m g κ s p t
  have htail : complementaryTail (h n) R i f < δ^2/16 := hN n hn t ht i
  have hp : |u| * R ≤ δ/2 := by
    have he := (le_div_iff₀ (by positivity : 0 < 2*R)).mp hu
    nlinarith
  have hs : u^2*R^2 ≤ δ^2/4 := by
    have he := pow_le_pow_left₀ (mul_nonneg (abs_nonneg u) hR.le) hp 2
    simpa only [mul_pow,sq_abs,div_pow,show (2:ℝ)^2 = 4 by norm_num] using he
  have he := positionTest_tail_bound (h n) u R hR.le i f
  rw [hnorm,one_pow,mul_one] at he
  change ‖positionTest u i f-f‖ < δ
  nlinarith [norm_nonneg (positionTest u i f-f)]

theorem evolved_positionCharacteristic_uniform (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T → ∀ i : Fin 2,
      ∀ u : ℝ, |u| ≤ ρ →
      ‖characteristic volume (h n) (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t)
        (u • positionFrequency 0 (antiDirection i),0)-1‖ < δ := by
  obtain ⟨ρ,hρ,N,hN⟩ := evolved_positionTest_uniform ε a hε ha m g κ s p hm hg hκ h hh hb hz T δ hδ
  refine ⟨ρ,hρ,N,fun n hn t ht i u hu => ?_⟩
  exact (positionCharacteristic_difference (h n) u i _
    (evolvedState_norm ε a (h n) hε ha (hh n) (hb n) m g κ s p t)).trans_lt (hN n hn t ht i u hu)

#print axioms positionTest_tail_bound
#print axioms positionCharacteristic_difference
#print axioms evolved_positionTest_uniform
#print axioms evolved_positionCharacteristic_uniform

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedPositionTestControl
