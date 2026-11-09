/- Reachable-state freezing on selected arbitrarily late windows whose
length can exceed the square-root scale by any prescribed factor. -/
import UnifiedTheory.Audit.KFCausalClockFloorLossSensitiveFreeze
import UnifiedTheory.Audit.KFCausalVanishingLossWindows

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSelectedFreeze
noncomputable section
open Filter
open scoped Topology
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorLossSensitiveFreeze

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "e" => trace ε hε h hne hb m g k
local notation "q" => KFCausalClockFloorFrozenFastEvolution.energy ε hε h hne hb m g k
local notation "P" => KFCausalClockFloorMovingFreeze.actual ε hε h hne hb m g k
local notation "Q" => KFCausalClockFloorMovingFreeze.frozen ε hε h hne hb m g k

theorem selected_window (a R C beta : ℝ) (ha : 0 < a) (hC : 0 < C) (hb' : 0 < beta)
    (v : V) (M : ℕ) :
    ∃ U L : ℝ, 0 < U ∧ 0 < L ∧ R ≤ U ∧ a ≤ U ∧ C*U ≤ L^2 ∧
      L/U ≤ 1/((M:ℝ)+1) ∧
      ∀ t, 0 ≤ t → t ≤ L → ‖P a U t (J v)-Q a U t (J v)‖^2 ≤ beta := by
  apply KFCausalVanishingLossWindows.selected_window (fun u => e a u v)
    (fun U t => ‖P a U t (J v)-Q a U t (J v)‖^2) |h| a R C beta (q a v)
    (abs_pos.mpr hne) hC hb'
    (add_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) ha.le))
    (trace_limit ε hε h hne hb m g k a v) _ _ M
  · intro U haU
    exact (trace_antitone ε hε h hne hb m g k a v ha (ha.trans_le haU) haU).trans_eq
      (trace_initial ε hε h hne hb m g k a ha v)
  · intro U L eta t hU ht htL he
    exact moving_window_bound ε hε h hne hb m g k a U L eta t hU ht htL he v

theorem exists_windows (a : ℝ) (ha : 0 < a) (v : V) :
    ∃ U L : ℕ → ℝ, (∀ n, 0 < U n ∧ 0 < L n) ∧ Tendsto U atTop atTop ∧ Tendsto L atTop atTop ∧
      Tendsto (fun n => (L n)^2/U n) atTop atTop ∧
      Tendsto (fun n => L n/U n) atTop (𝓝 0) ∧
      TendstoUniformlyOn (fun n r => P a (U n) (r*L n) (J v)-Q a (U n) (r*L n) (J v))
        (fun _ => 0) atTop (Set.Icc 0 1) := by
  have hex (n : ℕ) := selected_window ε hε h hne hb m g k a ((n:ℝ)+a+1) ((n:ℝ)+1)
    ((1/((n:ℝ)+1))^2) ha (by positivity) (by positivity) v n
  choose U L hU hL hR haU hC hsmall herr using hex
  have hb' : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := hb'.const_div_atTop 1
  refine ⟨U,L,fun n => ⟨hU n,hL n⟩,?_,?_,?_,?_,?_⟩
  · apply tendsto_atTop_mono (fun n => ?_) hb'
    linarith only [hR n,ha]
  · apply tendsto_atTop_mono (fun n => ?_) hb'
    have hu : (n:ℝ)+1 ≤ U n := by linarith only [hR n,ha]
    have hm := mul_le_mul_of_nonneg_left hu (show 0 ≤ (n:ℝ)+1 by positivity)
    have hp := hL n
    nlinarith only [hm,hC n,hp]
  · apply tendsto_atTop_mono (fun n => ?_) hb'
    exact (le_div_iff₀ (hU n)).mpr (hC n)
  · exact squeeze_zero (fun n => div_nonneg (hL n).le (hU n).le) hsmall hi
  · apply KFCausalDenseUnitaryUniformComparison.uniform_zero_of_square_bound
      (fun n r => P a (U n) (r*L n) (J v)-Q a (U n) (r*L n) (J v))
      (fun n => (1/((n:ℝ)+1))^2) atTop (Set.Icc 0 1) _ (by simpa using hi.pow 2)
    exact Eventually.of_forall (fun n r hr => herr n (r*L n) (mul_nonneg hr.1 (hL n).le)
      (by nlinarith only [hr.2,hL n]))

#print axioms selected_window
#print axioms exists_windows
end
end UnifiedTheory.Audit.KFCausalClockFloorSelectedFreeze
