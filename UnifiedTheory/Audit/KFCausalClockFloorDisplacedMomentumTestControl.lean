/- The actual evolved states have eventual uniform continuity at zero
for canonical momentum tests in both symmetric directions and the neutral
direction. The result uses derived tails, not unweighted second moments. -/
import UnifiedTheory.Audit.KFCausalComplementaryMomentumTests
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedPositionTestControl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentumTestControl
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit (dualPhysical)
open UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol
open UnifiedTheory.Audit.KFCausalComplementaryPhysicalMomenta (physicalDirection momentumIndex)
open UnifiedTheory.Audit.KFCausalComplementaryMomentumTests
open UnifiedTheory.Audit.KFCausalClockFloorComplementaryTail
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedComplementaryTail
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (characteristic operator)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def momentumGroup (j : Fin 3) : Fin 2 := ![0,1,1] j

theorem momentumSquare_le (h : ℝ) (j : Fin 3) (x : KFCausalEuclideanProductCoordinates.Joint 5 1) :
    momentumSymbol h j x^2 ≤ complementarySquare h (momentumGroup j) x := by
  fin_cases j <;> simp only [momentumGroup,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · change complementaryMomentum h 0 x^2 ≤ complementaryMomentum h 0 x^2+complementaryPosition 0 x^2+0^2
    nlinarith [sq_nonneg (complementaryPosition 0 x)]
  · change complementaryMomentum h 1 x^2 ≤ complementaryMomentum h 1 x^2+complementaryPosition 1 x^2+neutralMomentum h x^2
    nlinarith [sq_nonneg (complementaryPosition 1 x),sq_nonneg (neutralMomentum h x)]
  · change neutralMomentum h x^2 ≤ complementaryMomentum h 1 x^2+complementaryPosition 1 x^2+neutralMomentum h x^2
    nlinarith [sq_nonneg (complementaryPosition 1 x),sq_nonneg (complementaryMomentum h 1 x)]

theorem momentumTest_tail_bound (h u R : ℝ) (hR : 0 ≤ R) (j : Fin 3) (f : Hilbert) :
    ‖momentumTest h u j f-f‖^2 ≤ u^2*R^2*‖f‖^2+4*complementaryTail h R (momentumGroup j) f := by
  rw [← dualPhysical.norm_map (momentumTest h u j f-f),map_sub,momentumTest_dual,
    ← dualPhysical.norm_map f]
  exact KFCausalL2PhaseTailBound.phase_difference_square_tail
    (momentumSymbol h j) (complementarySquare h (momentumGroup j)) (by unfold momentumSymbol; fun_prop)
    (complementarySquare_continuous h (momentumGroup j)).measurable
    (momentumSquare_le h j) u R hR (dualPhysical f)

theorem momentumCharacteristic_difference (h u : ℝ) (j : Fin 3) (f : Hilbert) (hf : ‖f‖ = 1) :
    ‖characteristic volume h f (0,(0,u • physicalDirection j))-1‖ ≤ ‖momentumTest h u j f-f‖ := by
  have hi : inner ℂ f f = 1 := by rw [inner_self_eq_norm_sq_to_K,hf]; norm_num
  change ‖inner ℂ f (momentumTest h u j f)-1‖ ≤ _
  rw [← hi,← inner_sub_right]
  simpa only [hf,one_mul] using norm_inner_le_norm (𝕜 := ℂ) f (momentumTest h u j f-f)

theorem evolved_momentumTest_uniform (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T → ∀ j : Fin 3,
      ∀ u : ℝ, |u| ≤ ρ →
      ‖momentumTest (h n) u j (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t)-
        evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t‖ < δ := by
  obtain ⟨R,hR,N,hN⟩ := evolved_complementary_tail ε a hε ha m g κ s p hm hg hκ
    h hh hb hz T (δ^2/16) (by positivity)
  refine ⟨δ/(2*R),by positivity,N,fun n hn t ht j u hu => ?_⟩
  let f := evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t
  have hnorm : ‖f‖ = 1 := evolvedState_norm ε a (h n) hε ha (hh n) (hb n) m g κ s p t
  have htail : complementaryTail (h n) R (momentumGroup j) f < δ^2/16 := hN n hn t ht (momentumGroup j)
  have hp : |u| * R ≤ δ/2 := by
    have he := (le_div_iff₀ (by positivity : 0 < 2*R)).mp hu
    nlinarith
  have hs : u^2*R^2 ≤ δ^2/4 := by
    have he := pow_le_pow_left₀ (mul_nonneg (abs_nonneg u) hR.le) hp 2
    simpa only [mul_pow,sq_abs,div_pow,show (2:ℝ)^2 = 4 by norm_num] using he
  have he := momentumTest_tail_bound (h n) u R hR.le j f
  rw [hnorm,one_pow,mul_one] at he
  change ‖momentumTest (h n) u j f-f‖ < δ
  nlinarith [norm_nonneg (momentumTest (h n) u j f-f)]

theorem evolved_momentumCharacteristic_uniform (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T → ∀ j : Fin 3,
      ∀ u : ℝ, |u| ≤ ρ →
      ‖characteristic volume (h n) (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t)
        (0,(0,u • physicalDirection j))-1‖ < δ := by
  obtain ⟨ρ,hρ,N,hN⟩ := evolved_momentumTest_uniform ε a hε ha m g κ s p hm hg hκ h hh hb hz T δ hδ
  refine ⟨ρ,hρ,N,fun n hn t ht j u hu => ?_⟩
  exact (momentumCharacteristic_difference (h n) u j _
    (evolvedState_norm ε a (h n) hε ha (hh n) (hb n) m g κ s p t)).trans_lt (hN n hn t ht j u hu)

#print axioms momentumSquare_le
#print axioms momentumTest_tail_bound
#print axioms momentumCharacteristic_difference
#print axioms evolved_momentumTest_uniform
#print axioms evolved_momentumCharacteristic_uniform

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentumTestControl
