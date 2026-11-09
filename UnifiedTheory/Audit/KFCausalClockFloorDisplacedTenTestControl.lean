/- Simultaneous small changes in ten canonical frequencies act uniformly
close to the identity on the actual evolved states, eventually in the
small-hbar family and uniformly over finite forward time windows. -/
import UnifiedTheory.Audit.KFCausalCanonicalTenDirections

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedTenTestControl
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCanonicalTenDirections
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (operator characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem evolved_axes_uniform (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc s (s+T),
      let f := evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t
      (∀ i : Fin 5, ∀ u : ℝ, |u| ≤ ρ → ‖positionAxis (h n) u i f-f‖ < δ) ∧
      (∀ j : Fin 5, ∀ u : ℝ, |u| ≤ ρ → ‖momentumAxis (h n) u j f-f‖ < δ) := by
  obtain ⟨rC,hrC,NC,hC⟩ := KFCausalClockFloorDisplacedClockTestControl.evolved_test_uniform
    ε a hε ha m g κ s p hm hg hκ h hh hb hz T δ hδ
  obtain ⟨rA,hrA,NA,hA⟩ := KFCausalClockFloorDisplacedPositionTestControl.evolved_positionTest_uniform
    ε a hε ha m g κ s p hm hg hκ h hh hb hz T δ hδ
  obtain ⟨rM,hrM,NM,hM⟩ := KFCausalClockFloorDisplacedMomentumTestControl.evolved_momentumTest_uniform
    ε a hε ha m g κ s p hm hg hκ h hh hb hz T δ hδ
  obtain ⟨rG,hrG,NG,hG⟩ := KFCausalClockFloorDisplacedChargedTestControl.evolved_test_uniform
    ε a hε ha m g κ s p hm hg hκ h hh hb hz T δ hδ
  let ρ := min rC (min rA (min rM rG))
  have hr : 0 < ρ := lt_min hrC (lt_min hrA (lt_min hrM hrG))
  have hc : ρ ≤ rC := min_le_left _ _
  have ha' : ρ ≤ rA := (min_le_right _ _).trans (min_le_left _ _)
  have hm' : ρ ≤ rM := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hg' : ρ ≤ rG := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ρ,hr,max NC (max NA (max NM NG)),fun n hn t ht => ?_⟩
  have hnC : NC ≤ n := (le_max_left _ _).trans hn
  have hnA : NA ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnM : NM ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnG : NG ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have htime : |t-s| ≤ T := by rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]; linarith [ht.2]
  exact axes_control (h n) ρ δ _
    (fun u hu => hC n hnC t ht u (hu.trans hc))
    (fun i u hu => hA n hnA t htime i u (hu.trans ha'))
    (fun j u hu => hM n hnM t htime j u (hu.trans hm'))
    (fun k i u hu => hG n hnG t htime k i u (hu.trans hg'))

theorem evolved_simultaneous_uniform (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc s (s+T),
      ∀ q v : Fin 5 → ℝ, (∀ i, |q i| ≤ ρ) → (∀ j, |v j| ≤ ρ) →
      let f := evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t
      ‖operator volume (h n) (frequency q v) f-f‖ < δ := by
  obtain ⟨ρ,hρ,N,hN⟩ := evolved_axes_uniform ε a hε ha m g κ s p hm hg hκ h hh hb hz T (δ/10) (by linarith)
  refine ⟨ρ,hρ,N,fun n hn t ht q v hq hv => ?_⟩
  exact simultaneous_small (h n) ρ δ q v _ hq hv (hN n hn t ht).1 (hN n hn t ht).2

theorem characteristic_difference (h : ℝ) (q v : Fin 5 → ℝ) (f : Hilbert) (hf : ‖f‖ = 1) :
    ‖characteristic volume h f (frequency q v)-1‖ ≤ ‖operator volume h (frequency q v) f-f‖ := by
  have hi : inner ℂ f f = 1 := by rw [inner_self_eq_norm_sq_to_K,hf]; norm_num
  unfold characteristic
  rw [← hi,← inner_sub_right]
  simpa only [hf,one_mul] using norm_inner_le_norm (𝕜 := ℂ) f (operator volume h (frequency q v) f-f)

theorem evolved_characteristic_uniform (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc s (s+T),
      ∀ q v : Fin 5 → ℝ, (∀ i, |q i| ≤ ρ) → (∀ j, |v j| ≤ ρ) →
      ‖characteristic volume (h n) (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t)
        (frequency q v)-1‖ < δ := by
  obtain ⟨ρ,hρ,N,hN⟩ := evolved_simultaneous_uniform ε a hε ha m g κ s p hm hg hκ h hh hb hz T δ hδ
  refine ⟨ρ,hρ,N,fun n hn t ht q v hq hv => ?_⟩
  exact (characteristic_difference (h n) q v _
    (evolvedState_norm ε a (h n) hε ha (hh n) (hb n) m g κ s p t)).trans_lt (hN n hn t ht q v hq hv)

#print axioms evolved_axes_uniform
#print axioms evolved_simultaneous_uniform
#print axioms characteristic_difference
#print axioms evolved_characteristic_uniform

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedTenTestControl
